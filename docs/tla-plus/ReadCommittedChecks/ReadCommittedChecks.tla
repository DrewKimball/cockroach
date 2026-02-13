---------------------- MODULE ReadCommittedChecks ----------------------
EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS
  TXN1,           \* Transaction 1 identifier
  TXN2,           \* Transaction 2 identifier
  K1,             \* Key 1
  K2,             \* Key 2
  SSI,            \* Serializable isolation level
  RC,             \* Read-committed isolation level
  NoEvent,        \* Model value for uninitialized event
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
(* We use an event-based partial ordering model for timestamps instead  *)
(* of simple integers. Each timestamp is represented by a unique event  *)
(* ID. When allocating a new event, we non-deterministically choose     *)
(* where to insert it into a global total ordering (subject to          *)
(* constraints). This allows us to model scenarios where transaction A  *)
(* allocates its timestamps, transaction B executes operations, and     *)
(* then transaction A executes - with A's timestamps being earlier      *)
(* than B's despite B executing first. This is critical for exploring   *)
(* timestamp cache interactions and refresh behavior.                   *)
(*                                                                      *)
(* For RC transactions, we model per-statement read refresh that:       *)
(*   - Refreshes from the statement's read timestamp to the txn's       *)
(*     provisional commit timestamp.                                    *)
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
  \* Event ID counter for generating unique timestamp event IDs.
  eventID = 1;

  \* Total ordering of timestamp events (sequence of event IDs).
  \* When allocating a new event, we non-deterministically choose where to
  \* insert it in this sequence (subject to partial order constraints).
  ordering = <<>>;

  \* Transaction state: [status, iso_level, read_event, provisional_commit_event, final_commit_event].
  \* status: "pending" | "committed" | "aborted".
  \* read_event: event ID for read timestamp (SSI: txn-level; RC: stmt-level).
  \* provisional_commit_event: event ID for write timestamp, can advance during transaction.
  \* final_commit_event: event ID for final commit timestamp (only set when committed).
  txns = [t \in {TXN1, TXN2} |-> [
    status                |-> "pending",
    iso_level             |-> SSI,  \* will be set per-transaction
    read_event               |-> NoEvent,    \* for SSI: txn-level; for RC: stmt-level
    provisional_commit_event |-> NoEvent,    \* write timestamp event
    final_commit_event       |-> NoEvent
  ]];

  \* Key state: [value, event, intent_txn].
  \* intent_txn = NoIntent means no intent (committed value).
  \* intent_txn = TXN1 or TXN2 means there's an intent from that txn.
  \* event is the event ID of when the value was written.
  keys = [k \in {K1, K2} |-> [
    value      |-> 0,
    event      |-> NoEvent,
    intent_txn |-> NoIntent
  ]];

  \* Timestamp cache per key (stores event IDs).
  tscache = [k \in {K1, K2} |-> NoEvent];

  \* Track what values each transaction read: [key, value, event].
  \* Used for validating no stale reads.
  reads = [t \in {TXN1, TXN2} |-> <<>>];

define
  TXNS == {TXN1, TXN2}
  KEYS == {K1, K2}

  \* Insert element at position pos in sequence seq.
  InsertAt(seq, elem, pos) ==
    SubSeq(seq, 1, pos-1) \o <<elem>> \o SubSeq(seq, pos, Len(seq))

  \* Compare two event IDs based on their position in the ordering.
  \* Returns TRUE if e1 comes before e2 in the total ordering.
  \* NoEvent orders before all other events (represents "no timestamp yet").
  EventBefore(e1, e2) ==
    IF e1 = NoEvent THEN
      e2 /= NoEvent  \* NoEvent < any real event, but not NoEvent < NoEvent
    ELSE IF e2 = NoEvent THEN
      FALSE  \* any real event is not < NoEvent
    ELSE
      LET pos1 == CHOOSE i \in 1..Len(ordering) : ordering[i] = e1
          pos2 == CHOOSE i \in 1..Len(ordering) : ordering[i] = e2
      IN pos1 < pos2

  \* EventBeforeOrEqual operator.
  EventBeforeOrEqual(e1, e2) ==
    e1 = e2 \/ EventBefore(e1, e2)

  \* Check if a key has an intent from a specific transaction.
  HasIntent(key, txn) ==
    keys[key].intent_txn = txn

  \* Check if a key has any intent.
  HasAnyIntent(key) ==
    keys[key].intent_txn /= NoIntent

  \* Get the committed event of a key (NoEvent if has intent).
  CommittedEvent(key) ==
    IF HasAnyIntent(key) THEN NoEvent ELSE keys[key].event

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
  \* at a timestamp event T such that:
  \*   read_event < T <= final_commit_event
  NoStaleReads ==
    \A txn \in TXNS:
      IsCommitted(txn) =>
        \A i \in DOMAIN reads[txn]:
          LET
            read_record == reads[txn][i]
            key == read_record[1]
            read_val == read_record[2]
            read_event == read_record[3]
            final_commit_event == txns[txn].final_commit_event
          IN
            \* If the current committed value is different from what we read,
            \* it must have been written either:
            \*   - at or before our read timestamp event, OR
            \*   - after our commit timestamp event
            (keys[key].value /= read_val) =>
              (EventBeforeOrEqual(CommittedEvent(key), read_event) \/
               EventBefore(final_commit_event, CommittedEvent(key)))

  \* Type invariant.
  TypeInvariant ==
    /\ eventID \in Nat
    /\ Len(ordering) < eventID  \* ordering contains events < eventID
    /\ \A i \in 1..Len(ordering) : ordering[i] /= NoEvent  \* NoEvent never in ordering
    /\ \A t \in TXNS:
      /\ txns[t].status \in {"pending", "committed", "aborted"}
      /\ txns[t].iso_level \in {SSI, RC}
      /\ txns[t].read_event \in (1..(eventID-1)) \cup {NoEvent}
      /\ txns[t].provisional_commit_event \in (1..(eventID-1)) \cup {NoEvent}
      /\ txns[t].final_commit_event \in (1..(eventID-1)) \cup {NoEvent}
    /\ \A k \in KEYS:
      /\ keys[k].value \in 0..10
      /\ keys[k].event \in (1..(eventID-1)) \cup {NoEvent}
      /\ keys[k].intent_txn \in {NoIntent, TXN1, TXN2}
      /\ tscache[k] \in (1..(eventID-1)) \cup {NoEvent}

  \* Temporal properties.
  AllTransactionsFinalize ==
    <>[](\A t \in TXNS: txns[t].status \in {"committed", "aborted"})

  \* Compute valid insertion positions for an event that must come after must_be_after.
  ValidPositions(must_be_after) ==
    {p \in 1..(Len(ordering)+1) :
      \A e \in must_be_after :
        e = NoEvent \/ \E i \in 1..(p-1) : ordering[i] = e}
end define;

\* Allocate a new event and insert it into the ordering after must_be_after events.
macro alloc_event_after(ts_var, must_be_after) begin
  with pos \in ValidPositions(must_be_after) do
    ts_var := eventID ||
    eventID := eventID + 1 ||
    ordering := InsertAt(ordering, eventID, pos);
  end with;
end macro;

\* Non-deterministically advance provisional_commit_event or skip.
macro maybe_advance_commit_ts() begin
  either
    alloc_event_after(txns[self].provisional_commit_event, {txns[self].provisional_commit_event});
  or
    skip;
  end either;
end macro;

\* Each transaction process executes one statement that does a read and a write.
fair process txn \in TXNS
variables
  \* Which key this txn reads and writes.
  read_key = IF self = TXN1 THEN K2 ELSE K1;
  write_key = IF self = TXN1 THEN K1 ELSE K2;

  \* Statement-level read timestamp (for RC; for SSI this is txn-level).
  stmt_read_event = NoEvent;

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

  \* Begin transaction/statement - allocate read event.
  BeginTxnOrStmt:
    if txns[self].iso_level = SSI then
      \* SSI: allocate transaction-level read timestamp.
      alloc_event_after(txns[self].read_event, {});
    else
      \* RC: allocate statement-level read timestamp.
      alloc_event_after(stmt_read_event, {});
      txns[self].read_event := stmt_read_event;
    end if;

  \* Allocate provisional commit event.
  AllocWriteEvent:
    alloc_event_after(txns[self].provisional_commit_event, {txns[self].read_event});

  \* Execute read and write operations in either order.
  ExecuteStatement:
    while ~(read_done /\ write_done) do
      \* Before each operation, possibly advance provisional_commit_event.
      MaybeAdvanceTS:
        either
          alloc_event_after(txns[self].provisional_commit_event, {txns[self].provisional_commit_event});
        or
          skip;
        end either;
      ReadOrWrite:
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
                event      |-> txns[keys[read_key].intent_txn].final_commit_event,
                intent_txn |-> NoIntent
              ];
            else
              \* Pushee aborted - remove intent (set to initial value).
              keys[read_key] := [
                value      |-> 0,
                event      |-> NoEvent,
                intent_txn |-> NoIntent
              ];
            end if;
          end either;
        end if;
        \* Now read the (possibly just resolved) value.
        read_value := keys[read_key].value;
        if txns[self].iso_level = SSI then
          \* SSI reads at transaction read timestamp.
          reads[self] := Append(reads[self], <<read_key, read_value, txns[self].read_event>>);
        else
          \* RC reads at statement read timestamp.
          reads[self] := Append(reads[self], <<read_key, read_value, stmt_read_event>>);
        end if;
        read_done := TRUE;
      or
        when ~write_done;
        \* Perform write (checking timestamp cache).
        \* If timestamp cache conflict, bump provisional_commit_event.
        if EventBeforeOrEqual(txns[self].provisional_commit_event, tscache[write_key]) then
          alloc_event_after(txns[self].provisional_commit_event, {tscache[write_key]});
        end if;
        \* Write intent at (possibly bumped) provisional_commit_event.
        keys[write_key] := [
          value      |-> self,
          event      |-> txns[self].provisional_commit_event,
          intent_txn |-> self
        ];
        write_done := TRUE;
      end either;
    end while;

  \* Possibly advance the provisional commit timestamp again before refreshing.
  MaybeAdvanceBeforeRefresh:
    maybe_advance_commit_ts();

  \* For RC, do per-statement refresh after statement completes.
  \* This is the NEW mechanism proposed for check/cascade reads.
  StatementRefresh:
    if txns[self].iso_level = RC then
      \* Refresh check/cascade reads from stmt_read_event to current provisional_commit_event.
      \* Check if any value was written in (stmt_read_event, provisional_commit_event].
      if HasAnyIntent(read_key) then
        \* Fail on encountering intent.
        goto Abort;
      elsif EventBefore(stmt_read_event, CommittedEvent(read_key)) /\
            EventBeforeOrEqual(CommittedEvent(read_key), txns[self].provisional_commit_event) then
        \* Fail on encountering newer committed value.
        goto Abort;
      else
        \* Refresh succeeded - bump timestamp cache.
        tscache[read_key] := txns[self].provisional_commit_event;
      end if;
    end if;

  \* Possibly advance provisional_commit_event again before commit.
  \* (models timestamp cache conflicts from other statements/transactions)
  MaybeAdvanceBeforeCommit:
    maybe_advance_commit_ts();

  \* For SSI, must refresh all reads to provisional_commit_event before commit.
  CommitRefresh:
    if txns[self].iso_level = SSI then
      \* SSI refreshes from txn read_event to current provisional_commit_event.
      if HasAnyIntent(read_key) then
        goto Abort;
      elsif EventBefore(txns[self].read_event, CommittedEvent(read_key)) /\
            EventBeforeOrEqual(CommittedEvent(read_key), txns[self].provisional_commit_event) then
        goto Abort;
      else
        \* Refresh succeeded - bump timestamp cache.
        tscache[read_key] := txns[self].provisional_commit_event;
      end if;
    end if;

  \* Commit the transaction.
  Commit:
    \* Set final commit timestamp and mark as committed.
    txns[self].final_commit_event := txns[self].provisional_commit_event ||
    txns[self].status := "committed";

    \* Resolve intent at final commit timestamp.
    ResolveIntent:
      keys[write_key] := [
        value      |-> self,
        event      |-> txns[self].final_commit_event,
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
VARIABLES eventID, ordering, txns, keys, tscache, reads, pc

(* define statement *)
TXNS == {TXN1, TXN2}
KEYS == {K1, K2}


InsertAt(seq, elem, pos) ==
  SubSeq(seq, 1, pos-1) \o <<elem>> \o SubSeq(seq, pos, Len(seq))




EventBefore(e1, e2) ==
  IF e1 = NoEvent THEN
    e2 /= NoEvent
  ELSE IF e2 = NoEvent THEN
    FALSE
  ELSE
    LET pos1 == CHOOSE i \in 1..Len(ordering) : ordering[i] = e1
        pos2 == CHOOSE i \in 1..Len(ordering) : ordering[i] = e2
    IN pos1 < pos2


EventBeforeOrEqual(e1, e2) ==
  e1 = e2 \/ EventBefore(e1, e2)


HasIntent(key, txn) ==
  keys[key].intent_txn = txn


HasAnyIntent(key) ==
  keys[key].intent_txn /= NoIntent


CommittedEvent(key) ==
  IF HasAnyIntent(key) THEN NoEvent ELSE keys[key].event


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
          read_event == read_record[3]
          final_commit_event == txns[txn].final_commit_event
        IN




          (keys[key].value /= read_val) =>
            (EventBeforeOrEqual(CommittedEvent(key), read_event) \/
             EventBefore(final_commit_event, CommittedEvent(key)))


TypeInvariant ==
  /\ eventID \in Nat
  /\ Len(ordering) < eventID
  /\ \A i \in 1..Len(ordering) : ordering[i] /= NoEvent
  /\ \A t \in TXNS:
    /\ txns[t].status \in {"pending", "committed", "aborted"}
    /\ txns[t].iso_level \in {SSI, RC}
    /\ txns[t].read_event \in (1..(eventID-1)) \cup {NoEvent}
    /\ txns[t].provisional_commit_event \in (1..(eventID-1)) \cup {NoEvent}
    /\ txns[t].final_commit_event \in (1..(eventID-1)) \cup {NoEvent}
  /\ \A k \in KEYS:
    /\ keys[k].value \in 0..10
    /\ keys[k].event \in (1..(eventID-1)) \cup {NoEvent}
    /\ keys[k].intent_txn \in {NoIntent, TXN1, TXN2}
    /\ tscache[k] \in (1..(eventID-1)) \cup {NoEvent}


AllTransactionsFinalize ==
  <>[](\A t \in TXNS: txns[t].status \in {"committed", "aborted"})


ValidPositions(must_be_after) ==
  {p \in 1..(Len(ordering)+1) :
    \A e \in must_be_after :
      e = NoEvent \/ \E i \in 1..(p-1) : ordering[i] = e}

VARIABLES read_key, write_key, stmt_read_event, read_value, read_done, 
          write_done

vars == << eventID, ordering, txns, keys, tscache, reads, pc, read_key, 
           write_key, stmt_read_event, read_value, read_done, write_done >>

ProcSet == (TXNS)

Init == (* Global variables *)
        /\ eventID = 1
        /\ ordering = <<>>
        /\ txns =        [t \in {TXN1, TXN2} |-> [
                    status                |-> "pending",
                    iso_level             |-> SSI,
                    read_event               |-> NoEvent,
                    provisional_commit_event |-> NoEvent,
                    final_commit_event       |-> NoEvent
                  ]]
        /\ keys =        [k \in {K1, K2} |-> [
                    value      |-> 0,
                    event      |-> NoEvent,
                    intent_txn |-> NoIntent
                  ]]
        /\ tscache = [k \in {K1, K2} |-> NoEvent]
        /\ reads = [t \in {TXN1, TXN2} |-> <<>>]
        (* Process txn *)
        /\ read_key = [self \in TXNS |-> IF self = TXN1 THEN K2 ELSE K1]
        /\ write_key = [self \in TXNS |-> IF self = TXN1 THEN K1 ELSE K2]
        /\ stmt_read_event = [self \in TXNS |-> NoEvent]
        /\ read_value = [self \in TXNS |-> 0]
        /\ read_done = [self \in TXNS |-> FALSE]
        /\ write_done = [self \in TXNS |-> FALSE]
        /\ pc = [self \in ProcSet |-> "ChooseIsoLevel"]

ChooseIsoLevel(self) == /\ pc[self] = "ChooseIsoLevel"
                        /\ \/ /\ txns' = [txns EXCEPT ![self].iso_level = SSI]
                           \/ /\ txns' = [txns EXCEPT ![self].iso_level = RC]
                        /\ pc' = [pc EXCEPT ![self] = "BeginTxnOrStmt"]
                        /\ UNCHANGED << eventID, ordering, keys, tscache, 
                                        reads, read_key, write_key, 
                                        stmt_read_event, read_value, read_done, 
                                        write_done >>

BeginTxnOrStmt(self) == /\ pc[self] = "BeginTxnOrStmt"
                        /\ IF txns[self].iso_level = SSI
                              THEN /\ \E pos \in ValidPositions(({})):
                                        /\ eventID' = eventID + 1
                                        /\ ordering' = InsertAt(ordering, eventID, pos)
                                        /\ txns' = [txns EXCEPT ![self].read_event = eventID]
                                   /\ UNCHANGED stmt_read_event
                              ELSE /\ \E pos \in ValidPositions(({})):
                                        /\ eventID' = eventID + 1
                                        /\ ordering' = InsertAt(ordering, eventID, pos)
                                        /\ stmt_read_event' = [stmt_read_event EXCEPT ![self] = eventID]
                                   /\ txns' = [txns EXCEPT ![self].read_event = stmt_read_event'[self]]
                        /\ pc' = [pc EXCEPT ![self] = "AllocWriteEvent"]
                        /\ UNCHANGED << keys, tscache, reads, read_key, 
                                        write_key, read_value, read_done, 
                                        write_done >>

AllocWriteEvent(self) == /\ pc[self] = "AllocWriteEvent"
                         /\ \E pos \in ValidPositions(({txns[self].read_event})):
                              /\ eventID' = eventID + 1
                              /\ ordering' = InsertAt(ordering, eventID, pos)
                              /\ txns' = [txns EXCEPT ![self].provisional_commit_event = eventID]
                         /\ pc' = [pc EXCEPT ![self] = "ExecuteStatement"]
                         /\ UNCHANGED << keys, tscache, reads, read_key, 
                                         write_key, stmt_read_event, 
                                         read_value, read_done, write_done >>

ExecuteStatement(self) == /\ pc[self] = "ExecuteStatement"
                          /\ IF ~(read_done[self] /\ write_done[self])
                                THEN /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceTS"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeRefresh"]
                          /\ UNCHANGED << eventID, ordering, txns, keys, 
                                          tscache, reads, read_key, write_key, 
                                          stmt_read_event, read_value, 
                                          read_done, write_done >>

MaybeAdvanceTS(self) == /\ pc[self] = "MaybeAdvanceTS"
                        /\ \/ /\ \E pos \in ValidPositions(({txns[self].provisional_commit_event})):
                                   /\ eventID' = eventID + 1
                                   /\ ordering' = InsertAt(ordering, eventID, pos)
                                   /\ txns' = [txns EXCEPT ![self].provisional_commit_event = eventID]
                           \/ /\ TRUE
                              /\ UNCHANGED <<eventID, ordering, txns>>
                        /\ pc' = [pc EXCEPT ![self] = "ReadOrWrite"]
                        /\ UNCHANGED << keys, tscache, reads, read_key, 
                                        write_key, stmt_read_event, read_value, 
                                        read_done, write_done >>

ReadOrWrite(self) == /\ pc[self] = "ReadOrWrite"
                     /\ \/ /\ ~read_done[self]
                           /\ IF HasAnyIntent(read_key[self])
                                 THEN /\ \/ /\ ~HasAnyIntent(read_key[self])
                                            /\ keys' = keys
                                         \/ /\ txns[keys[read_key[self]].intent_txn].status \in {"committed", "aborted"}
                                            /\ IF txns[keys[read_key[self]].intent_txn].status = "committed"
                                                  THEN /\ keys' = [keys EXCEPT ![read_key[self]] =                   [
                                                                                                     value      |-> keys[read_key[self]].intent_txn,
                                                                                                     event      |-> txns[keys[read_key[self]].intent_txn].final_commit_event,
                                                                                                     intent_txn |-> NoIntent
                                                                                                   ]]
                                                  ELSE /\ keys' = [keys EXCEPT ![read_key[self]] =                   [
                                                                                                     value      |-> 0,
                                                                                                     event      |-> NoEvent,
                                                                                                     intent_txn |-> NoIntent
                                                                                                   ]]
                                 ELSE /\ TRUE
                                      /\ keys' = keys
                           /\ read_value' = [read_value EXCEPT ![self] = keys'[read_key[self]].value]
                           /\ IF txns[self].iso_level = SSI
                                 THEN /\ reads' = [reads EXCEPT ![self] = Append(reads[self], <<read_key[self], read_value'[self], txns[self].read_event>>)]
                                 ELSE /\ reads' = [reads EXCEPT ![self] = Append(reads[self], <<read_key[self], read_value'[self], stmt_read_event[self]>>)]
                           /\ read_done' = [read_done EXCEPT ![self] = TRUE]
                           /\ UNCHANGED <<eventID, ordering, txns, write_done>>
                        \/ /\ ~write_done[self]
                           /\ IF EventBeforeOrEqual(txns[self].provisional_commit_event, tscache[write_key[self]])
                                 THEN /\ \E pos \in ValidPositions(({tscache[write_key[self]]})):
                                           /\ eventID' = eventID + 1
                                           /\ ordering' = InsertAt(ordering, eventID, pos)
                                           /\ txns' = [txns EXCEPT ![self].provisional_commit_event = eventID]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << eventID, ordering, txns >>
                           /\ keys' = [keys EXCEPT ![write_key[self]] =                    [
                                                                          value      |-> self,
                                                                          event      |-> txns'[self].provisional_commit_event,
                                                                          intent_txn |-> self
                                                                        ]]
                           /\ write_done' = [write_done EXCEPT ![self] = TRUE]
                           /\ UNCHANGED <<reads, read_value, read_done>>
                     /\ pc' = [pc EXCEPT ![self] = "ExecuteStatement"]
                     /\ UNCHANGED << tscache, read_key, write_key, 
                                     stmt_read_event >>

MaybeAdvanceBeforeRefresh(self) == /\ pc[self] = "MaybeAdvanceBeforeRefresh"
                                   /\ \/ /\ \E pos \in ValidPositions(({txns[self].provisional_commit_event})):
                                              /\ eventID' = eventID + 1
                                              /\ ordering' = InsertAt(ordering, eventID, pos)
                                              /\ txns' = [txns EXCEPT ![self].provisional_commit_event = eventID]
                                      \/ /\ TRUE
                                         /\ UNCHANGED <<eventID, ordering, txns>>
                                   /\ pc' = [pc EXCEPT ![self] = "StatementRefresh"]
                                   /\ UNCHANGED << keys, tscache, reads, 
                                                   read_key, write_key, 
                                                   stmt_read_event, read_value, 
                                                   read_done, write_done >>

StatementRefresh(self) == /\ pc[self] = "StatementRefresh"
                          /\ IF txns[self].iso_level = RC
                                THEN /\ IF HasAnyIntent(read_key[self])
                                           THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                                /\ UNCHANGED tscache
                                           ELSE /\ IF EventBefore(stmt_read_event[self], CommittedEvent(read_key[self])) /\
                                                      EventBeforeOrEqual(CommittedEvent(read_key[self]), txns[self].provisional_commit_event)
                                                      THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                                           /\ UNCHANGED tscache
                                                      ELSE /\ tscache' = [tscache EXCEPT ![read_key[self]] = txns[self].provisional_commit_event]
                                                           /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeCommit"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "MaybeAdvanceBeforeCommit"]
                                     /\ UNCHANGED tscache
                          /\ UNCHANGED << eventID, ordering, txns, keys, reads, 
                                          read_key, write_key, stmt_read_event, 
                                          read_value, read_done, write_done >>

MaybeAdvanceBeforeCommit(self) == /\ pc[self] = "MaybeAdvanceBeforeCommit"
                                  /\ \/ /\ \E pos \in ValidPositions(({txns[self].provisional_commit_event})):
                                             /\ eventID' = eventID + 1
                                             /\ ordering' = InsertAt(ordering, eventID, pos)
                                             /\ txns' = [txns EXCEPT ![self].provisional_commit_event = eventID]
                                     \/ /\ TRUE
                                        /\ UNCHANGED <<eventID, ordering, txns>>
                                  /\ pc' = [pc EXCEPT ![self] = "CommitRefresh"]
                                  /\ UNCHANGED << keys, tscache, reads, 
                                                  read_key, write_key, 
                                                  stmt_read_event, read_value, 
                                                  read_done, write_done >>

CommitRefresh(self) == /\ pc[self] = "CommitRefresh"
                       /\ IF txns[self].iso_level = SSI
                             THEN /\ IF HasAnyIntent(read_key[self])
                                        THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                             /\ UNCHANGED tscache
                                        ELSE /\ IF EventBefore(txns[self].read_event, CommittedEvent(read_key[self])) /\
                                                   EventBeforeOrEqual(CommittedEvent(read_key[self]), txns[self].provisional_commit_event)
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "Abort"]
                                                        /\ UNCHANGED tscache
                                                   ELSE /\ tscache' = [tscache EXCEPT ![read_key[self]] = txns[self].provisional_commit_event]
                                                        /\ pc' = [pc EXCEPT ![self] = "Commit"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Commit"]
                                  /\ UNCHANGED tscache
                       /\ UNCHANGED << eventID, ordering, txns, keys, reads, 
                                       read_key, write_key, stmt_read_event, 
                                       read_value, read_done, write_done >>

Commit(self) == /\ pc[self] = "Commit"
                /\ txns' = [txns EXCEPT ![self].final_commit_event = txns[self].provisional_commit_event,
                                        ![self].status = "committed"]
                /\ pc' = [pc EXCEPT ![self] = "ResolveIntent"]
                /\ UNCHANGED << eventID, ordering, keys, tscache, reads, 
                                read_key, write_key, stmt_read_event, 
                                read_value, read_done, write_done >>

ResolveIntent(self) == /\ pc[self] = "ResolveIntent"
                       /\ keys' = [keys EXCEPT ![write_key[self]] =                    [
                                                                      value      |-> self,
                                                                      event      |-> txns[self].final_commit_event,
                                                                      intent_txn |-> NoIntent
                                                                    ]]
                       /\ pc' = [pc EXCEPT ![self] = "End"]
                       /\ UNCHANGED << eventID, ordering, txns, tscache, reads, 
                                       read_key, write_key, stmt_read_event, 
                                       read_value, read_done, write_done >>

Abort(self) == /\ pc[self] = "Abort"
               /\ txns' = [txns EXCEPT ![self].status = "aborted"]
               /\ IF HasIntent(write_key[self], self)
                     THEN /\ TRUE
                     ELSE /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "End"]
               /\ UNCHANGED << eventID, ordering, keys, tscache, reads, 
                               read_key, write_key, stmt_read_event, 
                               read_value, read_done, write_done >>

End(self) == /\ pc[self] = "End"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << eventID, ordering, txns, keys, tscache, reads, 
                             read_key, write_key, stmt_read_event, read_value, 
                             read_done, write_done >>

txn(self) == ChooseIsoLevel(self) \/ BeginTxnOrStmt(self)
                \/ AllocWriteEvent(self) \/ ExecuteStatement(self)
                \/ MaybeAdvanceTS(self) \/ ReadOrWrite(self)
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
