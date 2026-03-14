------------------ MODULE ReadCommittedChecksBaseline ------------------
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
(* This spec models the CURRENT system behavior for CRDB's foreign key *)
(* and unique constraint enforcement across two concurrent              *)
(* transactions. Each transaction performs a mutation (write) that must *)
(* be validated by a check or cascade read on a related key -- for     *)
(* example, inserting a child row and checking that the parent exists,  *)
(* deleting a parent row and checking for dependent children, or        *)
(* inserting a unique key and checking for duplicates. The two          *)
(* transactions conflict:                                               *)
(*   - TXN1 writes K1 and checks K2                                    *)
(*   - TXN2 writes K2 and checks K1                                    *)
(*                                                                      *)
(* This is the BASELINE spec, modeling how CRDB currently handles       *)
(* check/cascade reads:                                                 *)
(*   - RC transactions use locking reads with FailOnMoreRecent. The    *)
(*     locking read blocks on ALL intents, fails on committed values    *)
(*     above read_ts, and acquires a replicated lock that prevents      *)
(*     concurrent writes to the checked key.                            *)
(*   - SSI transactions use standard non-locking reads (no             *)
(*     FailOnMoreRecent) and rely on commit-time refresh for            *)
(*     correctness.                                                     *)
(*                                                                      *)
(* This baseline is the comparison point for the proposed V3 changes    *)
(* (see ReadCommittedChecks spec), which replace replicated locks with *)
(* four rules that allow non-locking RC check/cascade reads.            *)
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

(*--algorithm readcommittedchecksbaseline
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
  \*          newer values).
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

  \* Replicated lock state per key.
  \* NoIntent means no lock; TXN1/TXN2 means that transaction holds a
  \* replicated lock on this key. Only RC transactions acquire locks
  \* (during locking check/cascade reads). The lock prevents concurrent
  \* writes to the locked key while the lock holder is pending.
  locks = [k \in {K1, K2} |-> NoIntent];

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
      /\ locks[k] \in {NoIntent, TXN1, TXN2}

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
\* read_ts and write_ts. Both can perform the read and write in either order.
\* RC uses locking reads; SSI uses standard non-locking reads with commit-time
\* refresh.
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
  \* Both SSI and RC allocate read_ts.
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
      goto RCLoop;
    else
      goto SSILoop;
    end if;

  \* ================================================================
  \* RC Path: read/write in either order, locking reads
  \*
  \* RC uses locking reads for check/cascade operations. Locking reads
  \* inherently have FailOnMoreRecent semantics because setting
  \* KeyLockingStrength enables failOnMoreRecent in the MVCC scanner.
  \* This causes the read to block on ALL intents and fail on committed
  \* values above read_ts. The read also acquires a replicated lock
  \* that prevents concurrent writes to the checked key.
  \*
  \* The combination of FailOnMoreRecent + lock covers [read_ts, commit_ts]:
  \*   - FailOnMoreRecent catches values committed above read_ts before
  \*     the lock is acquired.
  \*   - The lock prevents new writes while the transaction is pending.
  \*   - On commit, the lock release bumps tscache to commit_ts.
  \* ================================================================

  RCLoop:
    while ~(read_done /\ write_done) do
      either
        \* Locking check/cascade read. Locking reads inherently have
        \* FailOnMoreRecent semantics (KeyLockingStrength sets
        \* failOnMoreRecent in the MVCC scanner), so they block on ALL
        \* intents regardless of the intent owner's isolation level, and
        \* fail on committed values above read_ts.
        \* After reading, acquires a replicated lock on the read key.
        when ~read_done;
        if HasAnyIntent(read_key) then
          \* Detect deadlock.
          if write_done /\
             txns[keys[read_key].intent_txn].status = "pending" /\
             HasAnyIntent(write_key) /\
             keys[write_key].intent_txn = self then
            goto Abort;
          end if;
          RCHandleIntent:
            if ~HasAnyIntent(read_key) then
              skip;
            else
              either
                await ~HasAnyIntent(read_key);
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
          \* FailOnMoreRecent: fail on any remaining intent.
          if HasAnyIntent(read_key) then
            goto Abort;
          end if;
          \* FailOnMoreRecent: fail on committed value above read_ts.
          if TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
            goto Abort;
          end if;
          \* Read succeeded. Acquire replicated lock and read value.
          locks[read_key] := self;
          read_value := keys[read_key].value;
        reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_ts>>);
        read_done := TRUE;
      or
        \* Mutation write operation.
        \* Wait for any replicated lock on write_key held by another txn.
        when ~write_done /\ locks[write_key] \in {NoIntent, self};
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
    goto MaybeAdvanceBeforeCommit;

  \* ================================================================
  \* SSI Path: read/write in either order, standard non-locking reads
  \*
  \* SSI uses standard non-locking reads without FailOnMoreRecent.
  \* Reads block on intents at or below read_ts and read through
  \* intents above read_ts. The commit-time refresh is the safety net
  \* that catches any values committed in [read_ts, write_ts].
  \* ================================================================

  SSILoop:
    while ~(read_done /\ write_done) do
      either
        \* Check/cascade read operation (standard non-locking read).
        \* Blocks on intents at or below read_ts only.
        \* Reads through intents above read_ts.
        when ~read_done;
        if HasAnyIntent(read_key) /\
           TimestampBeforeOrEqual(keys[read_key].ts, txns[self].read_ts) then
          \* Intent at or below read_ts - must block.
          \* Detect deadlock.
          if write_done /\
             txns[keys[read_key].intent_txn].status = "pending" /\
             HasAnyIntent(write_key) /\
             keys[write_key].intent_txn = self then
            goto Abort;
          end if;
          SSIHandleIntent:
            if ~HasAnyIntent(read_key) \/
               ~TimestampBeforeOrEqual(keys[read_key].ts, txns[self].read_ts) then
              \* Intent resolved or moved above read_ts - no longer blocking.
              skip;
            else
              either
                await ~HasAnyIntent(read_key) \/
                      ~TimestampBeforeOrEqual(keys[read_key].ts, txns[self].read_ts);
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
          \* Standard MVCC read at read_ts (no FailOnMoreRecent).
          \* Any intent at/below read_ts was handled above.
          if HasAnyIntent(read_key) then
            \* Intent above read_ts - read through to underlying value.
            \* In this model, each key has at most one writer, so the
            \* underlying value is 0 (the initial value).
            read_value := 0;
          elsif TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
            \* Committed value above read_ts - read previous value.
            read_value := 0;
          else
            \* Committed value at or below read_ts - read it.
            read_value := keys[read_key].value;
          end if;
        reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_ts>>);
        read_done := TRUE;
      or
        \* Mutation write operation.
        \* Wait for any replicated lock on write_key held by another txn.
        when ~write_done /\ locks[write_key] \in {NoIntent, self};
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

    \* Release replicated lock if held, bump tscache to commit timestamp.
    \* The tscache bump ensures future writes to this key are pushed
    \* above our commit timestamp, preserving the read's validity.
    if locks[read_key] = self then
      tscache[read_key] := txns[self].write_ts;
      locks[read_key] := NoIntent;
    end if;

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

    \* Release replicated lock if held (no tscache bump on abort).
    if locks[read_key] = self then
      locks[read_key] := NoIntent;
    end if;

  End:
    skip;

end process;

end algorithm; *)
\* BEGIN TRANSLATION
\* Translation is stale - regenerate with: pcal.trans ReadCommittedChecksBaseline.tla
\* END TRANSLATION

====================================================================
