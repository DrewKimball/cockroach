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
(* This spec models the non-blocking read mechanism for checks and      *)
(* cascades in read-committed isolation, as described in the README.    *)
(*                                                                      *)
(* We model two conflicting transactions with different isolation       *)
(* levels (SSI or RC). Each transaction performs a read and a write     *)
(* on different keys, creating read-write conflicts (no write-write     *)
(* conflicts in this model):                                            *)
(*   - TXN1 writes K1 and reads K2                                      *)
(*   - TXN2 reads K1 and writes K2                                      *)
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
(* For RC transactions, we model per-statement read refresh that:       *)
(*   - Refreshes from the statement's read timestamp to the txn's       *)
(*     write timestamp.                                                 *)
(*   - Blocks or pushes on encountering any intent.                     *)
(*   - Fails on encountering any committed value newer than the         *)
(*     statement's read timestamp.                                      *)
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
  \* read_ts: timestamp ID for read timestamp (SSI: txn-level; RC: stmt-level).
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
      /\ keys[k].value \in 0..10
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

\* Each transaction process executes one statement that does a read and a write.
\* Note: Since we model only one statement per transaction, we don't need a separate
\* stmt_read_ts variable. For RC transactions, txns[self].read_ts serves as the
\* statement-level read timestamp. For SSI, it's the transaction-level read timestamp.
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
  AssignReadTimestamp:
    \* For both SSI and RC, allocate read_ts (SSI: txn-level; RC: stmt-level).
    alloc_ts_after(txns[self].read_ts, {});

  AssignWriteTimestamp:
    \* Allocate write timestamp equal to read_ts.
    txns[self].write_ts := txns[self].read_ts;

  \* Possibly induce skew between the read and write timestamps.
  MaybeAdvanceBeforeReadWrite:
    maybe_advance_write_ts();

  \* Execute read and write operations in either order.
  ExecuteStatement:
    while ~(read_done /\ write_done) do
      either
        when ~read_done;
        \* Perform read with intent handling (blocking or pushing).
        if HasAnyIntent(read_key) then
          either
            \* Option 1: wait for intent to be resolved.
            await ~HasAnyIntent(read_key);
          or
            \* Option 2: try to push - succeeds if txn is finalized.
            await txns[keys[read_key].intent_txn].status \in {"committed", "aborted"};
            \* Successfully pushed - resolve the intent immediately.
            if txns[keys[read_key].intent_txn].status = "committed" then
              \* Resolve as committed value.
              keys[read_key] := [
                value      |-> keys[read_key].intent_txn,
                ts         |-> txns[keys[read_key].intent_txn].write_ts,
                intent_txn |-> NoIntent
              ];
            else
              \* Pushee aborted - remove intent (set to initial value).
              keys[read_key] := [
                value      |-> 0,
                ts         |-> ZeroTimestamp,
                intent_txn |-> NoIntent
              ];
            end if;
          end either;
        end if;
        \* Now read the (possibly just resolved) value.
        read_value := keys[read_key].value;
        \* Record read (SSI: txn read_ts; RC: stmt read_ts, both in txns[self].read_ts).
        reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_ts>>);
        read_done := TRUE;
      or
        when ~write_done;
        \* Perform write (checking timestamp cache).
        \* If timestamp cache conflict, bump write_ts.
        if TimestampBeforeOrEqual(txns[self].write_ts, tscache[write_key]) then
          alloc_ts_after(txns[self].write_ts, {tscache[write_key]});
        end if;
        \* Write intent at (possibly bumped) write_ts.
        keys[write_key] := [
          value      |-> self,
          ts         |-> txns[self].write_ts,
          intent_txn |-> self
        ];
        write_done := TRUE;
      end either;
    end while;

  \* Possibly advance the write timestamp again before refreshing.
  MaybeAdvanceBeforeRefresh:
    maybe_advance_write_ts();

  \* For RC, do per-statement refresh after statement completes.
  \* This is the NEW mechanism proposed for check/cascade reads.
  StatementRefresh:
    if txns[self].iso_level = RC then
      \* Refresh check/cascade reads from read_ts to current write_ts.
      \* Notably, we fail if any intent or committed value exists that is newer
      \* than the read_ts, even if it's newer than the current write_ts.
      \* The timestamp cache is still only bumped up to write_ts.
      if HasAnyIntent(read_key) then
        \* Fail on encountering intent.
        goto Abort;
      elsif TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
        \* Fail on encountering newer committed value. This includes values
        \* newer than the current write_ts.
        goto Abort;
      else
        \* Refresh succeeded - bump timestamp cache up to write_ts.
        tscache[read_key] := txns[self].write_ts;
      end if;
    end if;

  \* Possibly advance write_ts again before commit.
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
        value      |-> self,
        ts         |-> txns[self].write_ts,
        intent_txn |-> NoIntent  \* intent resolved
      ];

    goto End;

  Abort:
    txns[self].status := "aborted";

    \* Clean up intent if we wrote one.
    if HasIntent(write_key, self) then
      \* In reality, would clean up properly, but for model just mark aborted.
      \* Don't touch the key state for simplicity.
      skip;
    end if;

  End:
    skip;

end process;

end algorithm; *)
\* BEGIN TRANSLATION (this will be filled in by TLC when PlusCal is translated)
VARIABLES nextTS, ordering, txns, keys, tscache, reads, pc

(* define statement *)
TXNS == {TXN1, TXN2}
KEYS == {K1, K2}


InsertAt(seq, elem, pos) ==
  SubSeq(seq, 1, pos-1) \o <<elem>> \o SubSeq(seq, pos, Len(seq))




TimestampBefore(ts1, ts2) ==
  IF ts1 = ZeroTimestamp THEN
    ts2 /= ZeroTimestamp
  ELSE IF ts2 = ZeroTimestamp THEN
    FALSE
  ELSE
    LET pos1 == CHOOSE i \in 1..Len(ordering) : ordering[i] = ts1
        pos2 == CHOOSE i \in 1..Len(ordering) : ordering[i] = ts2
    IN pos1 < pos2


TimestampBeforeOrEqual(ts1, ts2) ==
  ts1 = ts2 \/ TimestampBefore(ts1, ts2)


HasIntent(key, txn) ==
  keys[key].intent_txn = txn


HasAnyIntent(key) ==
  keys[key].intent_txn /= NoIntent


CommittedTimestamp(key) ==
  IF HasAnyIntent(key) THEN ZeroTimestamp ELSE keys[key].ts


IsCommitted(txn) ==
  txns[txn].status = "committed"


IsAborted(txn) ==
  txns[txn].status = "aborted"


IsPending(txn) ==
  txns[txn].status = "pending"





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




          (keys[key].value /= read_val) =>
            (TimestampBeforeOrEqual(CommittedTimestamp(key), read_ts) \/
             TimestampBefore(commit_ts, CommittedTimestamp(key)))


TypeInvariant ==
  /\ nextTS \in Nat
  /\ Len(ordering) < nextTS
  /\ \A i \in 1..Len(ordering) : ordering[i] /= ZeroTimestamp
  /\ \A t \in TXNS:
    /\ txns[t].status \in {"pending", "committed", "aborted"}
    /\ txns[t].iso_level \in {SSI, RC}
    /\ txns[t].read_ts \in (1..(nextTS-1)) \cup {ZeroTimestamp}
    /\ txns[t].write_ts \in (1..(nextTS-1)) \cup {ZeroTimestamp}
  /\ \A k \in KEYS:
    /\ keys[k].value \in 0..10
    /\ keys[k].ts \in (1..(nextTS-1)) \cup {ZeroTimestamp}
    /\ keys[k].intent_txn \in {NoIntent, TXN1, TXN2}
    /\ tscache[k] \in (1..(nextTS-1)) \cup {ZeroTimestamp}


AllTransactionsFinalize ==
  <>[](\A t \in TXNS: txns[t].status \in {"committed", "aborted"})
CommittedTransactionsStayCommitted ==
  \A t \in TXNS: [](IsCommitted(t) => []IsCommitted(t))
AbortedTransactionsStayAborted ==
  \A t \in TXNS: [](IsAborted(t) => []IsAborted(t))


ValidPositions(must_be_after) ==
  {p \in 1..(Len(ordering)+1) :
    \A e \in must_be_after :
      e = ZeroTimestamp \/ \E i \in 1..(p-1) : ordering[i] = e}

VARIABLES read_key, write_key, read_value, read_done, write_done

vars == << nextTS, ordering, txns, keys, tscache, reads, pc, read_key, 
           write_key, read_value, read_done, write_done >>

ProcSet == (TXNS)

Init == (* Global variables *)
        /\ nextTS = 1
        /\ ordering = <<>>
        /\ txns =        [t \in {TXN1, TXN2} |-> [
                    status    |-> "pending",
                    iso_level |-> SSI,
                    read_ts   |-> ZeroTimestamp,
                    write_ts  |-> ZeroTimestamp
                  ]]
        /\ keys =        [k \in {K1, K2} |-> [
                    value      |-> 0,
                    ts         |-> ZeroTimestamp,
                    intent_txn |-> NoIntent
                  ]]
        /\ tscache = [k \in {K1, K2} |-> ZeroTimestamp]
        /\ reads = [t \in {TXN1, TXN2} |-> <<>>]
        (* Process txn *)
        /\ read_key = [self \in TXNS |-> IF self = TXN1 THEN K2 ELSE K1]
        /\ write_key = [self \in TXNS |-> IF self = TXN1 THEN K1 ELSE K2]
        /\ read_value = [self \in TXNS |-> 0]
        /\ read_done = [self \in TXNS |-> FALSE]
        /\ write_done = [self \in TXNS |-> FALSE]
        /\ pc = [self \in ProcSet |-> "ChooseIsoLevel"]

ChooseIsoLevel(self) == /\ pc[self] = "ChooseIsoLevel"
                        /\ \/ /\ txns' = [txns EXCEPT ![self].iso_level = SSI]
                           \/ /\ txns' = [txns EXCEPT ![self].iso_level = RC]
                        /\ pc' = [pc EXCEPT ![self] = "AssignReadTimestamp"]
                        /\ UNCHANGED << nextTS, ordering, keys, tscache, reads, 
                                        read_key, write_key, read_value, 
                                        read_done, write_done >>

AssignReadTimestamp(self) == /\ pc[self] = "AssignReadTimestamp"
                             /\ \E pos \in ValidPositions(({})):
                                  /\ nextTS' = nextTS + 1
                                  /\ ordering' = InsertAt(ordering, nextTS, pos)
                                  /\ txns' = [txns EXCEPT ![self].read_ts = nextTS]
                             /\ pc' = [pc EXCEPT ![self] = "AssignWriteTimestamp"]
                             /\ UNCHANGED << keys, tscache, reads, read_key, 
                                             write_key, read_value, read_done, 
                                             write_done >>

AssignWriteTimestamp(self) == /\ pc[self] = "AssignWriteTimestamp"
                              /\ txns' = [txns EXCEPT ![self].write_ts = txns[self].read_ts]
                              /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeReadWrite"]
                              /\ UNCHANGED << nextTS, ordering, keys, tscache, 
                                              reads, read_key, write_key, 
                                              read_value, read_done, 
                                              write_done >>

MaybeAdvanceBeforeReadWrite(self) == /\ pc[self] = "MaybeAdvanceBeforeReadWrite"
                                     /\ \/ /\ \E pos \in ValidPositions(({txns[self].write_ts})):
                                                /\ nextTS' = nextTS + 1
                                                /\ ordering' = InsertAt(ordering, nextTS, pos)
                                                /\ txns' = [txns EXCEPT ![self].write_ts = nextTS]
                                        \/ /\ TRUE
                                           /\ UNCHANGED <<nextTS, ordering, txns>>
                                     /\ pc' = [pc EXCEPT ![self] = "ExecuteStatement"]
                                     /\ UNCHANGED << keys, tscache, reads, 
                                                     read_key, write_key, 
                                                     read_value, read_done, 
                                                     write_done >>

ExecuteStatement(self) == /\ pc[self] = "ExecuteStatement"
                          /\ IF ~(read_done[self] /\ write_done[self])
                                THEN /\ \/ /\ ~read_done[self]
                                           /\ IF HasAnyIntent(read_key[self])
                                                 THEN /\ \/ /\ ~HasAnyIntent(read_key[self])
                                                            /\ keys' = keys
                                                         \/ /\ txns[keys[read_key[self]].intent_txn].status \in {"committed", "aborted"}
                                                            /\ IF txns[keys[read_key[self]].intent_txn].status = "committed"
                                                                  THEN /\ keys' = [keys EXCEPT ![read_key[self]] =                   [
                                                                                                                     value      |-> keys[read_key[self]].intent_txn,
                                                                                                                     ts         |-> txns[keys[read_key[self]].intent_txn].write_ts,
                                                                                                                     intent_txn |-> NoIntent
                                                                                                                   ]]
                                                                  ELSE /\ keys' = [keys EXCEPT ![read_key[self]] =                   [
                                                                                                                     value      |-> 0,
                                                                                                                     ts         |-> ZeroTimestamp,
                                                                                                                     intent_txn |-> NoIntent
                                                                                                                   ]]
                                                 ELSE /\ TRUE
                                                      /\ keys' = keys
                                           /\ read_value' = [read_value EXCEPT ![self] = keys'[read_key[self]].value]
                                           /\ reads' = [reads EXCEPT ![self] = Append(reads[self], <<read_key[self], read_value'[self], txns[self].read_ts>>)]
                                           /\ read_done' = [read_done EXCEPT ![self] = TRUE]
                                           /\ UNCHANGED <<nextTS, ordering, txns, write_done>>
                                        \/ /\ ~write_done[self]
                                           /\ IF TimestampBeforeOrEqual(txns[self].write_ts, tscache[write_key[self]])
                                                 THEN /\ \E pos \in ValidPositions(({tscache[write_key[self]]})):
                                                           /\ nextTS' = nextTS + 1
                                                           /\ ordering' = InsertAt(ordering, nextTS, pos)
                                                           /\ txns' = [txns EXCEPT ![self].write_ts = nextTS]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << nextTS, 
                                                                      ordering, 
                                                                      txns >>
                                           /\ keys' = [keys EXCEPT ![write_key[self]] =                    [
                                                                                          value      |-> self,
                                                                                          ts         |-> txns'[self].write_ts,
                                                                                          intent_txn |-> self
                                                                                        ]]
                                           /\ write_done' = [write_done EXCEPT ![self] = TRUE]
                                           /\ UNCHANGED <<reads, read_value, read_done>>
                                     /\ pc' = [pc EXCEPT ![self] = "ExecuteStatement"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeRefresh"]
                                     /\ UNCHANGED << nextTS, ordering, txns, 
                                                     keys, reads, read_value, 
                                                     read_done, write_done >>
                          /\ UNCHANGED << tscache, read_key, write_key >>

MaybeAdvanceBeforeRefresh(self) == /\ pc[self] = "MaybeAdvanceBeforeRefresh"
                                   /\ \/ /\ \E pos \in ValidPositions(({txns[self].write_ts})):
                                              /\ nextTS' = nextTS + 1
                                              /\ ordering' = InsertAt(ordering, nextTS, pos)
                                              /\ txns' = [txns EXCEPT ![self].write_ts = nextTS]
                                      \/ /\ TRUE
                                         /\ UNCHANGED <<nextTS, ordering, txns>>
                                   /\ pc' = [pc EXCEPT ![self] = "StatementRefresh"]
                                   /\ UNCHANGED << keys, tscache, reads, 
                                                   read_key, write_key, 
                                                   read_value, read_done, 
                                                   write_done >>

StatementRefresh(self) == /\ pc[self] = "StatementRefresh"
                          /\ IF txns[self].iso_level = RC
                                THEN /\ IF HasAnyIntent(read_key[self])
                                           THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                                /\ UNCHANGED tscache
                                           ELSE /\ IF TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key[self]))
                                                      THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                                           /\ UNCHANGED tscache
                                                      ELSE /\ tscache' = [tscache EXCEPT ![read_key[self]] = txns[self].write_ts]
                                                           /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeCommit"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeCommit"]
                                     /\ UNCHANGED tscache
                          /\ UNCHANGED << nextTS, ordering, txns, keys, reads, 
                                          read_key, write_key, read_value, 
                                          read_done, write_done >>

MaybeAdvanceBeforeCommit(self) == /\ pc[self] = "MaybeAdvanceBeforeCommit"
                                  /\ \/ /\ \E pos \in ValidPositions(({txns[self].write_ts})):
                                             /\ nextTS' = nextTS + 1
                                             /\ ordering' = InsertAt(ordering, nextTS, pos)
                                             /\ txns' = [txns EXCEPT ![self].write_ts = nextTS]
                                     \/ /\ TRUE
                                        /\ UNCHANGED <<nextTS, ordering, txns>>
                                  /\ pc' = [pc EXCEPT ![self] = "CommitRefresh"]
                                  /\ UNCHANGED << keys, tscache, reads, 
                                                  read_key, write_key, 
                                                  read_value, read_done, 
                                                  write_done >>

CommitRefresh(self) == /\ pc[self] = "CommitRefresh"
                       /\ IF txns[self].iso_level = SSI
                             THEN /\ IF HasAnyIntent(read_key[self])
                                        THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                             /\ UNCHANGED tscache
                                        ELSE /\ IF TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key[self])) /\
                                                   TimestampBeforeOrEqual(CommittedTimestamp(read_key[self]), txns[self].write_ts)
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                                        /\ UNCHANGED tscache
                                                   ELSE /\ tscache' = [tscache EXCEPT ![read_key[self]] = txns[self].write_ts]
                                                        /\ pc' = [pc EXCEPT ![self] = "Commit"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Commit"]
                                  /\ UNCHANGED tscache
                       /\ UNCHANGED << nextTS, ordering, txns, keys, reads, 
                                       read_key, write_key, read_value, 
                                       read_done, write_done >>

Commit(self) == /\ pc[self] = "Commit"
                /\ txns' = [txns EXCEPT ![self].status = "committed"]
                /\ pc' = [pc EXCEPT ![self] = "ResolveIntent"]
                /\ UNCHANGED << nextTS, ordering, keys, tscache, reads, 
                                read_key, write_key, read_value, read_done, 
                                write_done >>

ResolveIntent(self) == /\ pc[self] = "ResolveIntent"
                       /\ keys' = [keys EXCEPT ![write_key[self]] =                    [
                                                                      value      |-> self,
                                                                      ts         |-> txns[self].write_ts,
                                                                      intent_txn |-> NoIntent
                                                                    ]]
                       /\ pc' = [pc EXCEPT ![self] = "End"]
                       /\ UNCHANGED << nextTS, ordering, txns, tscache, reads, 
                                       read_key, write_key, read_value, 
                                       read_done, write_done >>

Abort(self) == /\ pc[self] = "Abort"
               /\ txns' = [txns EXCEPT ![self].status = "aborted"]
               /\ IF HasIntent(write_key[self], self)
                     THEN /\ TRUE
                     ELSE /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "End"]
               /\ UNCHANGED << nextTS, ordering, keys, tscache, reads, 
                               read_key, write_key, read_value, read_done, 
                               write_done >>

End(self) == /\ pc[self] = "End"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << nextTS, ordering, txns, keys, tscache, reads, 
                             read_key, write_key, read_value, read_done, 
                             write_done >>

txn(self) == ChooseIsoLevel(self) \/ AssignReadTimestamp(self)
                \/ AssignWriteTimestamp(self)
                \/ MaybeAdvanceBeforeReadWrite(self)
                \/ ExecuteStatement(self)
                \/ MaybeAdvanceBeforeRefresh(self)
                \/ StatementRefresh(self) \/ MaybeAdvanceBeforeCommit(self)
                \/ CommitRefresh(self) \/ Commit(self)
                \/ ResolveIntent(self) \/ Abort(self) \/ End(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in TXNS: txn(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in TXNS : WF_vars(txn(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====================================================================
