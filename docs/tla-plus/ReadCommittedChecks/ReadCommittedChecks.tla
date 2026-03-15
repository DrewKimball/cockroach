---------------------- MODULE ReadCommittedChecks ----------------------
EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS
  TXN1,           \* Transaction 1 identifier
  TXN2,           \* Transaction 2 identifier
  K1,             \* Key 1
  K2,             \* Key 2
  SSI,            \* Serializable isolation level
  RC,             \* Read-committed isolation level
  ZeroTimestamp,  \* Model value for uninitialized timestamp
  NoIntent        \* Model value for no intent

(************************************************************************)
(* This spec models CRDB enforcing a foreign key or unique constraint   *)
(* across two concurrent transactions. Each transaction performs a      *)
(* mutation (write) that must be validated by a check or cascade read   *)
(* on a related key -- for example, inserting a child row and checking  *)
(* that the parent exists, deleting a parent row and checking for       *)
(* dependent children, or inserting a unique key and checking for       *)
(* duplicates. The two transactions conflict:                           *)
(*   - TXN1 writes K1 and checks K2                                    *)
(*   - TXN2 writes K2 and checks K1                                    *)
(*                                                                      *)
(* Currently, read-committed (RC) transactions take replicated locks    *)
(* during check/cascade reads to prevent stale reads. This is           *)
(* expensive: replicated locks require a trip to the leaseholder and    *)
(* raft application and prevent 1PC. It has also led to correctness     *)
(* bugs due to predicate locking gaps.                                  *)
(*                                                                      *)
(* This spec validates a proposed alternative: three rules that allow   *)
(* non-locking RC check and cascade reads while maintaining             *)
(* correctness. The rules are:                                          *)
(* 1. All isolation levels block when a check/cascade read encounters   *)
(*    a weak-isolation intent or FOR UPDATE lock.                       *)
(* 2. All isolation levels retry when a check/cascade read encounters   *)
(*    a newer committed value (FailOnMoreRecent on the read itself).   *)
(* 3. Weak isolation levels perform check/cascade reads only after      *)
(*    successfully placing the intents for the triggering mutation.     *)
(*                                                                      *)
(* The spec also assumes existing system behavior: reads are refreshed  *)
(* and the read timestamp advanced when a write gets a WriteTooOld      *)
(* error. This is modeled by the RCRefresh step, which steps read_ts    *)
(* forward to write_ts and bumps the timestamp cache after the write.   *)
(*                                                                      *)
(* Both transaction types maintain read and write timestamps. Rules 1   *)
(* and 2 are enforced at check/cascade read time via FailOnMoreRecent.  *)
(* SSI relies on its standard commit-time refresh for the               *)
(* [read_ts, write_ts] window.                                          *)
(*                                                                      *)
(* TIMESTAMP MODEL:                                                     *)
(* We use a partial ordering model for timestamps instead of simple     *)
(* integers. Each timestamp is represented by a unique ID. When         *)
(* allocating a new timestamp, we non-deterministically choose where to *)
(* insert it into a global total ordering (subject to constraints).     *)
(* This allows us to model scenarios where transaction A allocates its  *)
(* timestamps, transaction B executes operations, and then transaction  *)
(* A executes - with A's timestamps being earlier than B's despite B    *)
(* executing first. This is critical for exploring timestamp cache      *)
(* interactions and refresh behavior.                                   *)
(*                                                                      *)
(* The spec verifies the key invariant: if a transaction commits, the   *)
(* values it read cannot have been stale (i.e., no value was written    *)
(* with a timestamp between the read timestamp and commit timestamp).   *)
(************************************************************************)

(*--algorithm readcommittedchecks
variables
  \* Timestamp counter for generating unique timestamp IDs.
  nextTS = 1;

  \* Total ordering of timestamps (sequence of timestamp IDs).
  \* When allocating a new timestamp, we non-deterministically choose where to
  \* insert it in this sequence (subject to partial order constraints).
  ordering = <<>>;

  \* Transaction state: [status, iso_level, read_ts, write_ts].
  \* status: "pending" | "committed" | "aborted".
  \* read_ts: timestamp ID for read timestamp. Both SSI and RC maintain this.
  \*          For SSI, this is the txn-level read timestamp which must be
  \*          refreshed (stepped forward to write_ts and checked for conflicts)
  \*          before commit.
  \*          For RC, this is allocated at the start of every statement and
  \*          stepped between statements (advanced without checking for
  \*          newer values). When a write gets a WriteTooOld error, the
  \*          read timestamp is refreshed to the new write timestamp.
  \* write_ts: timestamp ID for write timestamp, can advance during transaction.
  \*           When status is "committed", this is the commit timestamp.
  txns = [t \in {TXN1, TXN2} |-> [
    status    |-> "pending",
    iso_level |-> SSI,  \* will be set per-transaction
    read_ts   |-> ZeroTimestamp,    \* for SSI: txn-level; for RC: stmt-level
    write_ts  |-> ZeroTimestamp
  ]];

  \* Key state: [value, ts, intent_txn].
  \* intent_txn = NoIntent means no intent (committed value).
  \* intent_txn = TXN1 or TXN2 means there's an intent from that txn.
  \* ts is the timestamp ID of when the value was written.
  keys = [k \in {K1, K2} |-> [
    value      |-> 0,
    ts         |-> ZeroTimestamp,
    intent_txn |-> NoIntent
  ]];

  \* Timestamp cache per key (stores timestamp IDs).
  tscache = [k \in {K1, K2} |-> ZeroTimestamp];

  \* Track what values each transaction read: [key, value, ts].
  \* Used for validating no stale reads.
  reads = [t \in {TXN1, TXN2} |-> <<>>];

define
  TXNS == {TXN1, TXN2}
  KEYS == {K1, K2}

  \* Insert element at position pos in sequence seq.
  InsertAt(seq, elem, pos) ==
    SubSeq(seq, 1, pos-1) \o <<elem>> \o SubSeq(seq, pos, Len(seq))

  \* Compare two timestamps based on their position in the ordering.
  \* Returns TRUE if ts1 comes before ts2 in the total ordering.
  \* ZeroTimestamp orders before all other timestamps (represents "no timestamp yet").
  TimestampBefore(ts1, ts2) ==
    IF ts1 = ZeroTimestamp THEN
      ts2 /= ZeroTimestamp  \* ZeroTimestamp < any real timestamp, but not ZeroTimestamp < ZeroTimestamp
    ELSE IF ts2 = ZeroTimestamp THEN
      FALSE  \* any real timestamp is not < ZeroTimestamp
    ELSE
      LET pos1 == CHOOSE i \in 1..Len(ordering) : ordering[i] = ts1
          pos2 == CHOOSE i \in 1..Len(ordering) : ordering[i] = ts2
      IN pos1 < pos2

  \* TimestampBeforeOrEqual operator.
  TimestampBeforeOrEqual(ts1, ts2) ==
    ts1 = ts2 \/ TimestampBefore(ts1, ts2)

  \* Check if a key has an intent from a specific transaction.
  HasIntent(key, txn) ==
    keys[key].intent_txn = txn

  \* Check if a key has any intent.
  HasAnyIntent(key) ==
    keys[key].intent_txn /= NoIntent

  \* Check if an intent on a key requires blocking by a reader.
  \* Rule 1: weak-isolation intents always block check/cascade reads.
  \* SSI intents follow standard MVCC non-locking read behavior:
  \*   - Block if intent timestamp <= reader's read_ts
  \*   - Read through (ignore) if intent timestamp > reader's read_ts
  IntentBlocksReader(key, reader) ==
    /\ HasAnyIntent(key)
    /\ \/ txns[keys[key].intent_txn].iso_level /= SSI  \* rule 1: block on weak-iso intents
       \/ TimestampBeforeOrEqual(keys[key].ts, txns[reader].read_ts)  \* standard MVCC: block at/below read_ts

  \* Get the committed timestamp of a key (ZeroTimestamp if has intent).
  CommittedTimestamp(key) ==
    IF HasAnyIntent(key) THEN ZeroTimestamp ELSE keys[key].ts

  \* Check if transaction has committed.
  IsCommitted(txn) ==
    txns[txn].status = "committed"

  \* Check if transaction has aborted.
  IsAborted(txn) ==
    txns[txn].status = "aborted"

  \* Check if transaction is pending.
  IsPending(txn) ==
    txns[txn].status = "pending"

  \* The main safety invariant: if a transaction commits, all its reads
  \* must be non-stale. A read is stale if there exists a value written
  \* at a timestamp T such that:
  \*   read_ts < T <= commit_ts
  NoStaleReads ==
    \A txn \in TXNS:
      IsCommitted(txn) =>
        \A i \in DOMAIN reads[txn]:
          LET
            read_record == reads[txn][i]
            key == read_record[1]
            read_val == read_record[2]
            read_ts == read_record[3]
            commit_ts == txns[txn].write_ts
          IN
            \* If the current committed value is different from what we read,
            \* it must have been written either:
            \*   - at or before our read timestamp, OR
            \*   - after our commit timestamp
            (keys[key].value /= read_val) =>
              (TimestampBeforeOrEqual(CommittedTimestamp(key), read_ts) \/
               TimestampBefore(commit_ts, CommittedTimestamp(key)))

  \* Type invariant.
  TypeInvariant ==
    /\ nextTS \in Nat
    /\ Len(ordering) < nextTS  \* ordering contains timestamps < nextTS
    /\ \A i \in 1..Len(ordering) : ordering[i] /= ZeroTimestamp  \* ZeroTimestamp never in ordering
    /\ \A t \in TXNS:
      /\ txns[t].status \in {"pending", "committed", "aborted"}
      /\ txns[t].iso_level \in {SSI, RC}
      /\ txns[t].read_ts \in (1..(nextTS-1)) \cup {ZeroTimestamp}
      /\ txns[t].write_ts \in (1..(nextTS-1)) \cup {ZeroTimestamp}
    /\ \A k \in KEYS:
      /\ keys[k].value \in {0, 1}
      /\ keys[k].ts \in (1..(nextTS-1)) \cup {ZeroTimestamp}
      /\ keys[k].intent_txn \in {NoIntent, TXN1, TXN2}
      /\ tscache[k] \in (1..(nextTS-1)) \cup {ZeroTimestamp}

  \* Temporal properties.
  AllTransactionsFinalize ==
    <>[](\A t \in TXNS: txns[t].status \in {"committed", "aborted"})
  CommittedTransactionsStayCommitted ==
    \A t \in TXNS: [](IsCommitted(t) => []IsCommitted(t))
  AbortedTransactionsStayAborted ==
    \A t \in TXNS: [](IsAborted(t) => []IsAborted(t))

  \* Compute valid insertion positions for an event that must come after must_be_after.
  ValidPositions(must_be_after) ==
    {p \in 1..(Len(ordering)+1) :
      \A e \in must_be_after :
        e = ZeroTimestamp \/ \E i \in 1..(p-1) : ordering[i] = e}
end define;

\* Allocate a new timestamp and insert it into the ordering after must_be_after timestamps.
macro alloc_ts_after(ts_var, must_be_after) begin
  with pos \in ValidPositions(must_be_after) do
    ts_var := nextTS ||
    nextTS := nextTS + 1 ||
    ordering := InsertAt(ordering, nextTS, pos);
  end with;
end macro;

\* Non-deterministically advance write_ts or skip.
macro maybe_advance_write_ts() begin
  either
    alloc_ts_after(txns[self].write_ts, {txns[self].write_ts});
  or
    skip;
  end either;
end macro;

\* Each transaction process executes one statement consisting of a mutation
\* (write) and a check/cascade (read). Both SSI and RC transactions maintain
\* read_ts and write_ts. For RC, read_ts is stepped to write_ts when a
\* WriteTooOld bumps write_ts (existing behavior). For SSI, read_ts is
\* refreshed lazily at commit time.
fair process txn \in TXNS
variables
  \* Which key this txn reads and writes.
  read_key = IF self = TXN1 THEN K2 ELSE K1;
  write_key = IF self = TXN1 THEN K1 ELSE K2;

  \* Value read during statement.
  read_value = 0;

  \* Track which operations have completed.
  read_done = FALSE;
  write_done = FALSE;
begin
  \* Choose isolation level for this transaction.
  ChooseIsoLevel:
    either
      txns[self].iso_level := SSI;
    or
      txns[self].iso_level := RC;
    end either;

  \* Begin transaction/statement - allocate read and write timestamps.
  \* Both SSI and RC allocate read_ts. For RC, this will be stepped
  \* forward to write_ts if the write gets a WriteTooOld error.
  AssignReadTimestamp:
    alloc_ts_after(txns[self].read_ts, {});

  AssignWriteTimestamp:
    \* Allocate write timestamp equal to read_ts.
    txns[self].write_ts := txns[self].read_ts;

  \* Possibly induce skew between the read and write timestamps.
  MaybeAdvanceBeforeReadWrite:
    maybe_advance_write_ts();

  \* Branch based on isolation level.
  ExecuteStatement:
    if txns[self].iso_level = RC then
      goto RCWrite;
    else
      goto SSILoop;
    end if;

  \* ================================================================
  \* RC Path: write -> refresh -> read (rule 3)
  \* ================================================================

  \* Rule 3: RC must place intents before performing check/cascade reads.
  RCWrite:
    if TimestampBeforeOrEqual(txns[self].write_ts, tscache[write_key]) then
      alloc_ts_after(txns[self].write_ts, {tscache[write_key]});
    end if;
    \* Write intent at (possibly bumped) write_ts.
    keys[write_key] := [
      value      |-> 1,
      ts         |-> txns[self].write_ts,
      intent_txn |-> self
    ];

  \* Model the existing WriteTooOld refresh behavior: when the write bumps
  \* write_ts above read_ts, the refresher steps read_ts forward to
  \* write_ts. Since no check reads have occurred yet (rule 3), this
  \* refresh is trivially successful. We check for conflicts and bump
  \* the timestamp cache to prevent future conflicting writes.
  RCRefresh:
    \* Refresh checks (read_ts, write_ts] for conflicts, matching the real
    \* RefreshRequest semantics. Values above write_ts are ignored.
    if HasAnyIntent(read_key) then
      goto Abort;
    elsif TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) /\
          TimestampBeforeOrEqual(CommittedTimestamp(read_key), txns[self].write_ts) then
      goto Abort;
    else
      \* Refresh succeeded - step read_ts to write_ts and bump tscache.
      txns[self].read_ts := txns[self].write_ts;
      tscache[read_key] := txns[self].write_ts;
    end if;

  \* Check/cascade read with FailOnMoreRecent (rules 1, 2).
  \* Rule 1: block on weak-isolation intents at any timestamp.
  \* SSI intents follow standard MVCC: block at/below read_ts, read through above.
  RCRead:
    if IntentBlocksReader(read_key, self) then
      \* Detect deadlock: we've already written, so if the intent owner is
      \* pending and trying to read our write, we have a circular dependency.
      if txns[keys[read_key].intent_txn].status = "pending" /\
         HasAnyIntent(write_key) /\
         keys[write_key].intent_txn = self then
        goto Abort;
      end if;
      RCHandleIntent:
        if ~IntentBlocksReader(read_key, self) then
          skip;
        else
          either
            await ~IntentBlocksReader(read_key, self);
          or
            await txns[keys[read_key].intent_txn].status \in {"committed", "aborted"};
            if txns[keys[read_key].intent_txn].status = "committed" then
              keys[read_key] := [
                value      |-> 1,
                ts         |-> txns[keys[read_key].intent_txn].write_ts,
                intent_txn |-> NoIntent
              ];
            else
              keys[read_key] := [
                value      |-> 0,
                ts         |-> ZeroTimestamp,
                intent_txn |-> NoIntent
              ];
            end if;
          end either;
        end if;
    end if;
    RCPerformRead:
      \* FailOnMoreRecent: fail on blocking intents or newer committed values.
      \* Non-blocking intents (SSI intents above read_ts) are read through.
      if IntentBlocksReader(read_key, self) then
        goto Abort;
      end if;
      if TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
        \* There's a committed value newer than our read_ts.
        goto Abort;
      end if;
      \* Read succeeded. If there's a non-blocking SSI intent above our
      \* read_ts, we read through it to the underlying committed value.
      if HasAnyIntent(read_key) then
        \* Reading through an SSI intent above read_ts. In this model,
        \* each key has at most one writer, so the underlying value is 0.
        read_value := 0;
      else
        read_value := keys[read_key].value;
      end if;
    reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_ts>>);
    goto MaybeAdvanceBeforeCommit;

  \* ================================================================
  \* SSI Path: read/write in either order
  \* ================================================================

  SSILoop:
    while ~(read_done /\ write_done) do
      either
        \* Check/cascade read operation.
        \* Rule 1: block on weak-isolation intents at any timestamp.
        \* SSI intents follow standard MVCC: block at/below read_ts, read through above.
        when ~read_done;
        if IntentBlocksReader(read_key, self) then
          \* Detect deadlock.
          if write_done /\
             txns[keys[read_key].intent_txn].status = "pending" /\
             HasAnyIntent(write_key) /\
             keys[write_key].intent_txn = self then
            goto Abort;
          end if;
          SSIHandleIntent:
            if ~IntentBlocksReader(read_key, self) then
              skip;
            else
              either
                await ~IntentBlocksReader(read_key, self);
              or
                await txns[keys[read_key].intent_txn].status \in {"committed", "aborted"};
                if txns[keys[read_key].intent_txn].status = "committed" then
                  keys[read_key] := [
                    value      |-> 1,
                    ts         |-> txns[keys[read_key].intent_txn].write_ts,
                    intent_txn |-> NoIntent
                  ];
                else
                  keys[read_key] := [
                    value      |-> 0,
                    ts         |-> ZeroTimestamp,
                    intent_txn |-> NoIntent
                  ];
                end if;
              end either;
            end if;
        end if;
        SSIPerformRead:
          \* FailOnMoreRecent: fail on blocking intents or newer committed values.
          \* Non-blocking intents (SSI intents above read_ts) are read through.
          if IntentBlocksReader(read_key, self) then
            goto Abort;
          end if;
          if TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
            \* There's a committed value newer than our read_ts.
            goto Abort;
          end if;
          \* Read succeeded. If there's a non-blocking SSI intent above our
          \* read_ts, we read through it to the underlying committed value.
          if HasAnyIntent(read_key) then
            \* Reading through an SSI intent above read_ts. In this model,
            \* each key has at most one writer, so the underlying value is 0.
            read_value := 0;
          else
            read_value := keys[read_key].value;
          end if;
        reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_ts>>);
        read_done := TRUE;
      or
        \* Mutation write operation.
        when ~write_done;
        if TimestampBeforeOrEqual(txns[self].write_ts, tscache[write_key]) then
          alloc_ts_after(txns[self].write_ts, {tscache[write_key]});
        end if;
        keys[write_key] := [
          value      |-> 1,
          ts         |-> txns[self].write_ts,
          intent_txn |-> self
        ];
        write_done := TRUE;
      end either;
    end while;

  \* ================================================================
  \* Common: commit path
  \* ================================================================

  \* Possibly advance write_ts before commit.
  \* (models timestamp cache conflicts from other statements/transactions)
  MaybeAdvanceBeforeCommit:
    maybe_advance_write_ts();

  \* For SSI, must refresh all reads to write_ts before commit.
  CommitRefresh:
    if txns[self].iso_level = SSI then
      \* SSI refreshes from txn read_ts to current write_ts.
      if HasAnyIntent(read_key) then
        goto Abort;
      elsif TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) /\
            TimestampBeforeOrEqual(CommittedTimestamp(read_key), txns[self].write_ts) then
        goto Abort;
      else
        \* Refresh succeeded - bump timestamp cache.
        tscache[read_key] := txns[self].write_ts;
      end if;
    end if;

  \* Commit the transaction.
  Commit:
    \* Mark as committed (write_ts becomes the commit timestamp).
    txns[self].status := "committed";

    \* Resolve intent at commit timestamp.
    ResolveIntent:
      keys[write_key] := [
        value      |-> 1,
        ts         |-> txns[self].write_ts,
        intent_txn |-> NoIntent  \* intent resolved
      ];

    goto End;

  Abort:
    txns[self].status := "aborted";

    \* Clean up intent if we wrote one.
    if HasIntent(write_key, self) then
      \* Remove the intent by resetting to initial state.
      keys[write_key] := [
        value      |-> 0,
        ts         |-> ZeroTimestamp,
        intent_txn |-> NoIntent
      ];
    end if;

  End:
    skip;

end process;

end algorithm; *)
\* BEGIN TRANSLATION
\* Translation is stale - regenerate with: pcal.trans ReadCommittedChecks.tla
\* END TRANSLATION

====================================================================
