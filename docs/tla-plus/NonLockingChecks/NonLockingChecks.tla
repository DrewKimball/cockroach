---------------------- MODULE NonLockingChecks ----------------------
EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS
  TXN1,           \* Transaction 1 identifier
  TXN2,           \* Transaction 2 identifier
  K1,             \* Key 1
  K2,             \* Key 2
  ZeroTimestamp,  \* Model value for uninitialized timestamp
  NoIntent        \* Model value for no intent

(************************************************************************)
(* Models the target state where all isolation levels enforce           *)
(* write-before-read for check/cascade reads (rule 3 for all).          *)
(* With this constraint, SSI and RC behave identically for constraint   *)
(* checks, so isolation levels are not modeled. No commit-time refresh  *)
(* (or any refresh) is needed for correctness.                          *)
(*                                                                      *)
(* Three rules validated:                                               *)
(* 1. Block when a check read encounters an intent/lock.                *)
(* 2. Retry when a check read encounters a newer committed value.       *)
(* 3. Perform check reads only after placing the mutation's intents.    *)
(*                                                                      *)
(* TIMESTAMPS: Unique IDs inserted into a global total ordering.        *)
(* Non-deterministic insertion lets TLC explore cases where timestamps  *)
(* are allocated in one order but ordered differently (e.g., txn A      *)
(* allocates before txn B executes, but A's timestamps sort earlier).   *)
(*                                                                      *)
(* KEY INVARIANT: A committed txn's reads are non-stale -- no value     *)
(* was written between read_ts and commit_ts.                           *)
(************************************************************************)

(*--algorithm nonlockingchecks
variables
  \* Timestamp counter for generating unique timestamp IDs.
  nextTS = 1;

  \* Total ordering of timestamps (sequence of timestamp IDs).
  ordering = <<>>;

  \* Transaction state: [status, read_ts, write_ts].
  txns = [t \in {TXN1, TXN2} |-> [
    status   |-> "pending",
    read_ts  |-> ZeroTimestamp,
    write_ts |-> ZeroTimestamp
  ]];

  \* Key state: [value, ts, intent_txn].
  keys = [k \in {K1, K2} |-> [
    value      |-> 0,
    ts         |-> ZeroTimestamp,
    intent_txn |-> NoIntent
  ]];

  \* Timestamp cache per key.
  tscache = [k \in {K1, K2} |-> ZeroTimestamp];

  \* Track what values each transaction read: [key, value, ts].
  reads = [t \in {TXN1, TXN2} |-> <<>>];

define
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

\* Each transaction: write mutation, then check/cascade read (rule 3).
\* The real system eagerly refreshes reads on WriteTooOld; this is a no-op
\* here other reads are not modeled.
fair process txn \in TXNS
variables
  read_key = IF self = TXN1 THEN K2 ELSE K1;
  write_key = IF self = TXN1 THEN K1 ELSE K2;
  read_value = 0;
begin
  AssignReadTimestamp:
    alloc_ts_after(txns[self].read_ts, {});

  AssignWriteTimestamp:
    txns[self].write_ts := txns[self].read_ts;

  MaybeAdvanceBeforeReadWrite:
    maybe_advance_write_ts();

  \* Mutation write. WriteTooOld pushes write_ts above tscache. The real system
  \* eagerly refreshes reads on WriteTooOld; this is a no-op here since other
  \* reads are not modeled.
  Write:
    if TimestampBeforeOrEqual(txns[self].write_ts, tscache[write_key]) then
      alloc_ts_after(txns[self].write_ts, {tscache[write_key]});
    end if;
    keys[write_key] := [
      value      |-> 1,
      ts         |-> txns[self].write_ts,
      intent_txn |-> self
    ];

  \* Check/cascade read (rules 1, 2). Intent always placed above (rule 3).
  CheckRead:
    if HasAnyIntent(read_key) then
      \* Deadlock: both txns have intents and are waiting on each other.
      if txns[keys[read_key].intent_txn].status = "pending" /\
         HasIntent(write_key, self) then
        goto Abort;
      end if;
      \* Wait for the intent to be resolved by its owning transaction.
      HandleIntent:
        await ~HasAnyIntent(read_key);
    end if;
  PerformRead:
    \* Re-check for intents (one could have been placed after the check
    \* above, since they are separate labels). Also check for a committed
    \* value above read_ts (rule 2).
    if HasAnyIntent(read_key)
       \/ TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key)) then
      goto Abort;
    else
      read_value := keys[read_key].value;
      reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_ts>>);
      \* Bump tscache so concurrent writers get a WriteTooOld error.
      tscache[read_key] := txns[self].read_ts;
    end if;

  \* Possibly advance write_ts before commit.
  MaybeAdvanceBeforeCommit:
    maybe_advance_write_ts();

  \* Commit the transaction (write_ts becomes the commit timestamp).
  Commit:
    txns[self].status := "committed";

  \* Resolve intent at commit timestamp.
  ResolveIntent:
    keys[write_key] := [
      value      |-> 1,
      ts         |-> txns[self].write_ts,
      intent_txn |-> NoIntent
    ];
    goto End;

  Abort:
    txns[self].status := "aborted";
    \* Clean up intent if we wrote one.
    if HasIntent(write_key, self) then
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

VARIABLES read_key, write_key, read_value

vars == << nextTS, ordering, txns, keys, tscache, reads, pc, read_key, 
           write_key, read_value >>

ProcSet == (TXNS)

Init == (* Global variables *)
        /\ nextTS = 1
        /\ ordering = <<>>
        /\ txns =        [t \in {TXN1, TXN2} |-> [
                    status   |-> "pending",
                    read_ts  |-> ZeroTimestamp,
                    write_ts |-> ZeroTimestamp
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
        /\ pc = [self \in ProcSet |-> "AssignReadTimestamp"]

AssignReadTimestamp(self) == /\ pc[self] = "AssignReadTimestamp"
                             /\ \E pos \in ValidPositions(({})):
                                  /\ nextTS' = nextTS + 1
                                  /\ ordering' = InsertAt(ordering, nextTS, pos)
                                  /\ txns' = [txns EXCEPT ![self].read_ts = nextTS]
                             /\ pc' = [pc EXCEPT ![self] = "AssignWriteTimestamp"]
                             /\ UNCHANGED << keys, tscache, reads, read_key, 
                                             write_key, read_value >>

AssignWriteTimestamp(self) == /\ pc[self] = "AssignWriteTimestamp"
                              /\ txns' = [txns EXCEPT ![self].write_ts = txns[self].read_ts]
                              /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeReadWrite"]
                              /\ UNCHANGED << nextTS, ordering, keys, tscache, 
                                              reads, read_key, write_key, 
                                              read_value >>

MaybeAdvanceBeforeReadWrite(self) == /\ pc[self] = "MaybeAdvanceBeforeReadWrite"
                                     /\ \/ /\ \E pos \in ValidPositions(({txns[self].write_ts})):
                                                /\ nextTS' = nextTS + 1
                                                /\ ordering' = InsertAt(ordering, nextTS, pos)
                                                /\ txns' = [txns EXCEPT ![self].write_ts = nextTS]
                                        \/ /\ TRUE
                                           /\ UNCHANGED <<nextTS, ordering, txns>>
                                     /\ pc' = [pc EXCEPT ![self] = "Write"]
                                     /\ UNCHANGED << keys, tscache, reads, 
                                                     read_key, write_key, 
                                                     read_value >>

Write(self) == /\ pc[self] = "Write"
               /\ IF TimestampBeforeOrEqual(txns[self].write_ts, tscache[write_key[self]])
                     THEN /\ \E pos \in ValidPositions(({tscache[write_key[self]]})):
                               /\ nextTS' = nextTS + 1
                               /\ ordering' = InsertAt(ordering, nextTS, pos)
                               /\ txns' = [txns EXCEPT ![self].write_ts = nextTS]
                     ELSE /\ TRUE
                          /\ UNCHANGED << nextTS, ordering, txns >>
               /\ keys' = [keys EXCEPT ![write_key[self]] =                    [
                                                              value      |-> 1,
                                                              ts         |-> txns'[self].write_ts,
                                                              intent_txn |-> self
                                                            ]]
               /\ pc' = [pc EXCEPT ![self] = "CheckRead"]
               /\ UNCHANGED << tscache, reads, read_key, write_key, read_value >>

CheckRead(self) == /\ pc[self] = "CheckRead"
                   /\ IF HasAnyIntent(read_key[self])
                         THEN /\ IF txns[keys[read_key[self]].intent_txn].status = "pending" /\
                                    HasIntent(write_key[self], self)
                                    THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "HandleIntent"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "PerformRead"]
                   /\ UNCHANGED << nextTS, ordering, txns, keys, tscache, 
                                   reads, read_key, write_key, read_value >>

HandleIntent(self) == /\ pc[self] = "HandleIntent"
                      /\ ~HasAnyIntent(read_key[self])
                      /\ pc' = [pc EXCEPT ![self] = "PerformRead"]
                      /\ UNCHANGED << nextTS, ordering, txns, keys, tscache, 
                                      reads, read_key, write_key, read_value >>

PerformRead(self) == /\ pc[self] = "PerformRead"
                     /\ IF HasAnyIntent(read_key[self])
                           \/ TimestampBefore(txns[self].read_ts, CommittedTimestamp(read_key[self]))
                           THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                /\ UNCHANGED << tscache, reads, read_value >>
                           ELSE /\ read_value' = [read_value EXCEPT ![self] = keys[read_key[self]].value]
                                /\ reads' = [reads EXCEPT ![self] = Append(reads[self], <<read_key[self], read_value'[self], txns[self].read_ts>>)]
                                /\ tscache' = [tscache EXCEPT ![read_key[self]] = txns[self].read_ts]
                                /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeCommit"]
                     /\ UNCHANGED << nextTS, ordering, txns, keys, read_key, 
                                     write_key >>

MaybeAdvanceBeforeCommit(self) == /\ pc[self] = "MaybeAdvanceBeforeCommit"
                                  /\ \/ /\ \E pos \in ValidPositions(({txns[self].write_ts})):
                                             /\ nextTS' = nextTS + 1
                                             /\ ordering' = InsertAt(ordering, nextTS, pos)
                                             /\ txns' = [txns EXCEPT ![self].write_ts = nextTS]
                                     \/ /\ TRUE
                                        /\ UNCHANGED <<nextTS, ordering, txns>>
                                  /\ pc' = [pc EXCEPT ![self] = "Commit"]
                                  /\ UNCHANGED << keys, tscache, reads, 
                                                  read_key, write_key, 
                                                  read_value >>

Commit(self) == /\ pc[self] = "Commit"
                /\ txns' = [txns EXCEPT ![self].status = "committed"]
                /\ pc' = [pc EXCEPT ![self] = "ResolveIntent"]
                /\ UNCHANGED << nextTS, ordering, keys, tscache, reads, 
                                read_key, write_key, read_value >>

ResolveIntent(self) == /\ pc[self] = "ResolveIntent"
                       /\ keys' = [keys EXCEPT ![write_key[self]] =                    [
                                                                      value      |-> 1,
                                                                      ts         |-> txns[self].write_ts,
                                                                      intent_txn |-> NoIntent
                                                                    ]]
                       /\ pc' = [pc EXCEPT ![self] = "End"]
                       /\ UNCHANGED << nextTS, ordering, txns, tscache, reads, 
                                       read_key, write_key, read_value >>

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
                               write_key, read_value >>

End(self) == /\ pc[self] = "End"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << nextTS, ordering, txns, keys, tscache, reads, 
                             read_key, write_key, read_value >>

txn(self) == AssignReadTimestamp(self) \/ AssignWriteTimestamp(self)
                \/ MaybeAdvanceBeforeReadWrite(self) \/ Write(self)
                \/ CheckRead(self) \/ HandleIntent(self)
                \/ PerformRead(self) \/ MaybeAdvanceBeforeCommit(self)
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
