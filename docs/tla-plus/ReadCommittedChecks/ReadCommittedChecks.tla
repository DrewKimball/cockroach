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
(* The spec assumes existing system behavior: reads are refreshed and   *)
(* the read timestamp advanced when a write gets a WriteTooOld error    *)
(* (assumption 1). This is modeled inline in the write steps, which     *)
(* push write_ts above the tscache and step read_ts to write_ts.        *)
(*                                                                      *)
(* Both transaction types maintain read and write timestamps. Rules 1   *)
(* and 2 are enforced at check/cascade read time via FailOnMoreRecent.  *)
(* SSI uses a commit-time refresh with FailOnMoreRecent semantics to    *)
(* catch conflicts in the window between the read and commit. This is   *)
(* a change from the current system where the span refresher checks     *)
(* the bounded range (read_ts, write_ts]; it's needed to correctly      *)
(* handle the insert fast path where the check read precedes the write. *)
(*                                                                      *)
(* SIMPLIFICATION: All intents block all readers. In the real system,   *)
(* SSI readers can read through SSI intents above their read timestamp. *)
(* Blocking is strictly more conservative, so any invariant that holds  *)
(* here also holds in the real system.                                  *)
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

  \* Compute valid insertion positions for a timestamp that must come
  \* strictly after all timestamps in must_be_after.
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

  \* ================================================================
  \* Statement execution: write and check/cascade read.
  \* RC must write before reading (rule 3). SSI can do either order.
  \* ================================================================

  StatementLoop:
    while ~(read_done /\ write_done) do
      either
        \* Mutation write operation.
        \* If tscache >= write_ts, push write_ts above tscache (WriteTooOld).
        \* In the real system, the statement would also attempt to refresh
        \* its reads at this point, but we don't model that since the only
        \* reads in scope are for constraint validation.
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
      or
        \* Check/cascade read operation (rules 1, 2).
        when ~read_done;
        \* Rule 3: RC must place intents before performing check reads.
        when txns[self].iso_level = SSI \/ write_done;
        if HasAnyIntent(read_key) then
          \* Detect deadlock: if the intent owner is pending and we have
          \* an intent on their read key, we have a circular dependency.
          \*
          \* NOTE: this check is overeager when the intent owner has already
          \* completed its read (no actual circular wait). However, TLC
          \* explores all interleavings, so the non-aborting path where the
          \* intent owner finishes first is still fully explored.
          if txns[keys[read_key].intent_txn].status = "pending" /\
             HasIntent(write_key, self) then
            goto Abort;
          end if;
          \* Wait for the intent to be resolved by its owning transaction.
          HandleIntent:
            await ~HasAnyIntent(read_key);
        end if;
        PerformRead:
          \* Re-check for intents (one could have been placed after the
          \* HasAnyIntent check above, since they are separate labels).
          \* Also check for a committed value above read_ts (rule 2).
          if HasAnyIntent(read_key)
             \/ TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
            goto Abort;
          else
            read_value := keys[read_key].value;
            reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_ts>>);
            \* Bump tscache so concurrent writers get a WriteTooOld error.
            tscache[read_key] := txns[self].read_ts;
            read_done := TRUE;
          end if;
      end either;
    end while;

  \* ================================================================
  \* Common: commit path
  \* ================================================================

  \* Possibly advance write_ts before commit.
  \* (models timestamp cache conflicts from other statements/transactions)
  MaybeAdvanceBeforeCommit:
    maybe_advance_write_ts();

  \* SSI commit-time refresh of check/cascade read spans.
  \*
  \* In the current system, the span refresher checks committed values
  \* in the bounded range (read_ts, write_ts]. This is insufficient
  \* for check/cascade reads when the check is performed before the
  \* write (the "insert fast path"): a conflicting intent can resolve
  \* to a committed value above write_ts before the refresh runs,
  \* causing the bounded range check to miss it.
  \*
  \* The fix: use FailOnMoreRecent semantics when refreshing
  \* check/cascade read spans. This means blocking on intents and
  \* failing on any committed value above read_ts, with no upper bound.
  \* This requires tracking which refresh spans correspond to
  \* check/cascade reads in the span refresher, so FailOnMoreRecent
  \* can be applied selectively to those spans.
  CommitRefresh:
    if txns[self].iso_level = SSI then
      \* Fail if there's an intent or a committed value above read_ts.
      if HasAnyIntent(read_key)
         \/ TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
        goto Abort;
      else
        \* Refresh succeeded - bump tscache to write_ts (commit_ts).
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
    /\ keys[k].value \in {0, 1}
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
                                     /\ pc' = [pc EXCEPT ![self] = "StatementLoop"]
                                     /\ UNCHANGED << keys, tscache, reads, 
                                                     read_key, write_key, 
                                                     read_value, read_done, 
                                                     write_done >>

StatementLoop(self) == /\ pc[self] = "StatementLoop"
                       /\ IF ~(read_done[self] /\ write_done[self])
                             THEN /\ \/ /\ ~write_done[self]
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
                                                                                       value      |-> 1,
                                                                                       ts         |-> txns'[self].write_ts,
                                                                                       intent_txn |-> self
                                                                                     ]]
                                        /\ write_done' = [write_done EXCEPT ![self] = TRUE]
                                        /\ pc' = [pc EXCEPT ![self] = "StatementLoop"]
                                     \/ /\ ~read_done[self]
                                        /\ txns[self].iso_level = SSI \/ write_done[self]
                                        /\ IF HasAnyIntent(read_key[self])
                                              THEN /\ IF txns[keys[read_key[self]].intent_txn].status = "pending" /\
                                                         HasIntent(write_key[self], self)
                                                         THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "HandleIntent"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "PerformRead"]
                                        /\ UNCHANGED <<nextTS, ordering, txns, keys, write_done>>
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeCommit"]
                                  /\ UNCHANGED << nextTS, ordering, txns, keys, 
                                                  write_done >>
                       /\ UNCHANGED << tscache, reads, read_key, write_key, 
                                       read_value, read_done >>

HandleIntent(self) == /\ pc[self] = "HandleIntent"
                      /\ ~HasAnyIntent(read_key[self])
                      /\ pc' = [pc EXCEPT ![self] = "PerformRead"]
                      /\ UNCHANGED << nextTS, ordering, txns, keys, tscache, 
                                      reads, read_key, write_key, read_value, 
                                      read_done, write_done >>

PerformRead(self) == /\ pc[self] = "PerformRead"
                     /\ IF HasAnyIntent(read_key[self])
                           \/ TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key[self]))
                           THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                /\ UNCHANGED << tscache, reads, read_value, 
                                                read_done >>
                           ELSE /\ read_value' = [read_value EXCEPT ![self] = keys[read_key[self]].value]
                                /\ reads' = [reads EXCEPT ![self] = Append(reads[self], <<read_key[self], read_value'[self], txns[self].read_ts>>)]
                                /\ tscache' = [tscache EXCEPT ![read_key[self]] = txns[self].read_ts]
                                /\ read_done' = [read_done EXCEPT ![self] = TRUE]
                                /\ pc' = [pc EXCEPT ![self] = "StatementLoop"]
                     /\ UNCHANGED << nextTS, ordering, txns, keys, read_key, 
                                     write_key, write_done >>

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
                                        \/ TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key[self]))
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
                                                                      value      |-> 1,
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
                     THEN /\ keys' = [keys EXCEPT ![write_key[self]] =                    [
                                                                         value      |-> 0,
                                                                         ts         |-> ZeroTimestamp,
                                                                         intent_txn |-> NoIntent
                                                                       ]]
                     ELSE /\ TRUE
                          /\ keys' = keys
               /\ pc' = [pc EXCEPT ![self] = "End"]
               /\ UNCHANGED << nextTS, ordering, tscache, reads, read_key, 
                               write_key, read_value, read_done, write_done >>

End(self) == /\ pc[self] = "End"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << nextTS, ordering, txns, keys, tscache, reads, 
                             read_key, write_key, read_value, read_done, 
                             write_done >>

txn(self) == ChooseIsoLevel(self) \/ AssignReadTimestamp(self)
                \/ AssignWriteTimestamp(self)
                \/ MaybeAdvanceBeforeReadWrite(self) \/ StatementLoop(self)
                \/ HandleIntent(self) \/ PerformRead(self)
                \/ MaybeAdvanceBeforeCommit(self) \/ CommitRefresh(self)
                \/ Commit(self) \/ ResolveIntent(self) \/ Abort(self)
                \/ End(self)

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
