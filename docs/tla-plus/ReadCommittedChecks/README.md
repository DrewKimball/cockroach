# Read-Committed Non-Blocking Checks TLA+ Specification

This specification models the non-blocking read mechanism for foreign key checks and cascades in read-committed (RC) isolation.

## The Proposal

### Problem Statement

We have to prevent stale reads in checks and cascades. Serializable does this by ensuring all reads are refreshed by the time the transaction commits. Read-committed does this by taking locks. What if there was a way we could make RC transactions behave more like SSI transactions for checks and cascades?

We can't just refresh the reads for checks/cascades up to the transaction commit timestamp like a SSI transaction would. This could result in the RC transaction failing with a serializable retry error. That is a non-starter given that RC is meant to prevent the need for app-side retry loops. We need a way to guarantee progress, so that once a RC statement finishes successfully, it cannot cause the transaction to fail (though it may fail for other reasons later).

### Solution

We can guarantee both correctness and progress if we add a refresh step after each RC statement with the following properties:

- The refresh includes all reads performed for checks and cascades.
- The refresh happens after all other operations in the statement have completed successfully.
- It refreshes from the RC statement's read timestamp up to the surrounding transaction's write timestamp. The timestamp cache is bumped accordingly.
- It fails on encountering any intent. Possibly only after attempting a push?
- **FailOnMoreRecent**: It fails on encountering any committed value newer than the "refresh from" timestamp. Notably, this includes writes at a timestamp later than the transaction's write timestamp.

### Protecting [stmt_read_ts, stmt_write_ts]

It is clear that the read-refresh prevents stale reads from the RC statement's read timestamp up to its write timestamp. This is enforced by retrying the statement if any writes are discovered above the read timestamp and by bumping the timestamp cache up to the write timestamp to prevent future writes below the write timestamp.

### Protecting [stmt_write_ts, txn_commit_ts]

However, the write timestamp may change after the statement completes, for example, if a later writing statement in the same transaction is bumped by the timestamp cache. We already decided that we can't refresh the check/cascade reads up to the final commit timestamp, since this could cause the transaction to fail with a user-visible retry error. We need some other way to prevent another transaction from writing within this interval.

There is a property of these conflicting writes that we can rely on to simplify things: all writes that have a possibility of conflict check for conflicts. For a uniqueness constraint, we read all spans that could contain a duplicate key. For a FK parent key delete or update, we read the span containing all child rows. Similarly, for a FK child key insert, we read the parent row.

In fact, we don't need to protect the interval between a successful statement's write timestamp and the transaction's final commit timestamp. Potentially conflicting statements will do this instead! If a conflicting statement attempts to write in this [stmt_write_ts, txn_commit_ts] interval, the conflicting statement will refresh its own check before completing. There are two possibilities:

- Either the conflicting statement's refresh will encounter an intent and fail, or
- The intent has already been resolved, and the conflicting statement's refresh will observe the newer committed value, and fail.

This relies on the assumption that pushing an intent to a later timestamp or replacing it with a committed value happens atomically with removing the original intent. I believe this assumption holds true.

## Overview

The spec models two conflicting transactions with different isolation levels (Serializable or Read-Committed). Each transaction performs one statement that does both a read and a write:

- Transaction 1: writes K1, reads K2
- Transaction 2: reads K1, writes K2

This creates read-write conflicts where each transaction reads what the other writes. Note that there are no write-write conflicts in this model - each transaction writes to a different key.

## Key Mechanisms Modeled

### Timestamp Model

Each transaction has distinct timestamps:

**Read Timestamp:**
- **SSI**: Assigned once at transaction start, used for all reads in the transaction
- **RC**: Assigned per-statement, each statement reads at a new timestamp

**Write Timestamp:**
- Assigned at transaction/statement start
- Used for all writes (intents are written at this timestamp)
- Can advance during the transaction's lifetime (due to timestamp cache conflicts)
- When the transaction commits, this becomes the commit timestamp and all intents are resolved at this timestamp

### For SSI Transactions

SSI transactions:
1. Read at a fixed transaction-level read timestamp
2. Write at the write timestamp (which can advance)
3. Before commit, **must** refresh all reads from `read_ts` to `write_ts`
4. Commit at the final value of `write_ts`

### For RC Transactions (The Proposal)

RC transactions normally:
1. Read at a per-statement read timestamp
2. Write at the write timestamp
3. **Do NOT refresh reads** (unlike SSI)

**The proposal** adds a NEW per-statement refresh for check/cascade reads:

1. After the statement completes successfully
2. Refresh check/cascade reads from `stmt_read_ts` to current `write_ts`
3. Fails if it encounters any intent
4. Fails if it encounters any committed value written in `(stmt_read_ts, write_ts]`
5. On success, updates the timestamp cache to prevent future conflicting writes

### Timestamp Advancement

The spec models two scenarios where the write timestamp can advance:

1. **Intra-statement advancement** (`stmt_ts_skew`): The write timestamp advances between the read and write within a single statement (timestamp cache conflict)
2. **Pre-commit advancement** (`commit_ts_skew`): The write timestamp advances after the statement completes but before the transaction commits

## Safety Invariant

The primary invariant checked is **NoStaleReads**: If a transaction commits, the values it read must not be stale. Specifically, for each read performed at timestamp `read_ts`, no value should have been written with a timestamp `T` such that:

```
read_ts < T <= write_ts
```

Where:
- For SSI: `read_ts` is the transaction-level read timestamp
- For RC: `read_ts` is the per-statement read timestamp

This ensures that:
- For RC transactions: The per-statement refresh correctly prevents stale reads
- For SSI transactions: The traditional refresh mechanism works correctly

## Running the Spec

### Prerequisites

1. Install the TLA+ Toolbox from https://github.com/tlaplus/tlaplus/releases
2. Or install the TLA+ command-line tools

### Translate PlusCal to TLA+

Before running the model checker, you need to translate the PlusCal algorithm to TLA+:

```bash
# Using the TLA+ Toolbox
# File -> Open Module -> ReadCommittedChecks.tla
# File -> Translate PlusCal Algorithm (Ctrl+T or Cmd+T)

# Or using command line:
java -cp tla2tools.jar pcal.trans ReadCommittedChecks.tla
```

### Run the Model Checker

```bash
# Using TLA+ Toolbox
# TLC Model Checker -> New Model
# Run the model

# Or using command line:
java -cp tla2tools.jar tlc2.TLC -config ReadCommittedChecks.cfg ReadCommittedChecks.tla
```

## Configuration

The `ReadCommittedChecks.cfg` file configures:

- Transaction identifiers: `TXN1` and `TXN2`
- Key identifiers: `K1` and `K2`
- Isolation levels: `SSI` (Serializable) and `RC` (Read-Committed)
- **Constraint**: `clock <= 10` to bound state space (not a semantic constraint, just for model checking)

You can adjust the clock constraint for more thorough checking, but larger values will increase the state space and runtime.

## Expected Results

The model checker should verify that:

1. **TypeInvariant** holds: All variables stay within their expected types and ranges
2. **NoStaleReads** holds: No transaction commits with stale reads
3. **AllTransactionsFinalize** holds: All transactions eventually commit or abort

If the invariants hold, this validates that the per-statement refresh mechanism for RC transactions correctly prevents stale reads without requiring full transaction-level refreshes.

## Scenarios Covered

The spec explores all combinations of:

- Isolation levels: SSI × SSI, SSI × RC, RC × SSI, RC × RC
- Statement operation order: read-then-write vs write-then-read
- Statement timestamp skew: present or absent
- Commit timestamp skew: present or absent
- Transaction interleaving: various orderings of the two transactions' operations

This provides comprehensive coverage of the possible race conditions and timing scenarios.

## Key Test Cases

### Case 1: RC transaction succeeds with per-statement refresh

1. TXN2 (RC) begins statement
2. Allocates stmt_read_ts=1, reads K1 at ts=1, value=0
3. Allocates write_ts=1
4. write_ts advances to 2 (timestamp cache conflict)
5. Writes K2 at ts=2 with intent
6. Does NEW per-statement refresh on K1 from stmt_read_ts=1 to write_ts=2
7. No writes found in (1, 2], refresh succeeds, bumps tscache[K1]=2
8. Commits with write_ts=2

### Case 2: RC transaction aborts on conflicting write

1. TXN2 (RC) begins statement
2. Allocates stmt_read_ts=1, reads K1 at ts=1, value=0
3. (Meanwhile) TXN1 writes K1 at ts=2 with intent, commits, resolves intent at ts=2
4. TXN2 allocates write_ts=3
5. TXN2 writes K2 at ts=3 with intent
6. TXN2 does per-statement refresh on K1 from stmt_read_ts=1 to write_ts=3
7. Finds committed value at ts=2 in (1, 3], refresh FAILS
8. TXN2 aborts (avoiding stale read)

### Case 3: SSI transaction succeeds with commit-time refresh

1. TXN2 (SSI) begins transaction
2. Allocates txn read_ts=1, write_ts=1
3. Reads K1 at txn read_ts=1, value=0
4. Writes K2 at write_ts=1 with intent
5. write_ts advances to 2 before commit
6. Does commit-time refresh on K1 from txn read_ts=1 to write_ts=2
7. No writes found in (1, 2], refresh succeeds
8. Commits with write_ts=2

### Case 4: SSI transaction aborts when read timestamp cannot be refreshed

1. TXN2 (SSI) begins with txn read_ts=1, write_ts=1
2. Reads K1 at txn read_ts=1, value=0
3. (Meanwhile) TXN1 writes K1 at ts=2, commits
4. TXN2 writes K2 at write_ts=1 with intent
5. TXN2's write_ts advances to 3
6. TXN2 does commit-time refresh from txn read_ts=1 to write_ts=3
7. Finds committed value at ts=2 in (1, 3], refresh FAILS
8. TXN2 aborts

### Case 5: RC timestamp cache protection validates the proposal

1. TXN1 (RC) allocates stmt_read_ts=1, reads K2 at ts=1, value=0
2. TXN1 allocates write_ts=1, writes K1 at ts=1 with intent
3. TXN1 refreshes K2 from stmt_read_ts=1 to write_ts=1
4. No conflicts, bumps tscache[K2]=1
5. TXN1 commits with write_ts=1, resolves K1 intent at ts=1
6. TXN2 (RC) allocates stmt_read_ts=2, reads K1 at ts=2
7. Sees TXN1's committed value at ts=1 (OK, ts=1 ≤ stmt_read_ts=2)
8. TXN2 allocates write_ts=2, tries to write K2 at ts=2
9. tscache[K2]=1, so write succeeds (ts=2 > tscache=1)
10. TXN2 refreshes K1 from stmt_read_ts=2 to write_ts=2
11. Finds value at ts=1, but ts=1 ≤ stmt_read_ts=2, so NOT in (2, 2], refresh succeeds
12. This validates: "conflicting statements will refresh their own checks"

### Case 6: TXN2 blocks on TXN1's pending intent

1. TXN1 (RC) allocates stmt_read_ts=1, write_ts=2
2. TXN1 reads K2 at ts=1, writes K1 at ts=2 with intent
3. TXN1 refreshes K2 from ts=1 to ts=2, succeeds
4. *[TXN2 interleaves before TXN1 commits]*
5. TXN2 (RC) allocates stmt_read_ts=3, tries to read K1 at ts=3
6. TXN2 encounters TXN1's intent (intent_txn=TXN1, intent at ts=2)
7. TXN2 tries to push but TXN1.status = "pending", so TXN2 **blocks**
8. *[Back to TXN1]*
9. TXN1 commits with write_ts=2
10. TXN1 resolves intent (intent_txn → 0, committed value at ts=2)
11. *[Back to TXN2, now unblocked]*
12. TXN2 reads K1, sees committed value at ts=2
13. TXN2 continues execution

**Result**: TXN2 blocks on TXN1's pending intent and proceeds after resolution.

### Case 7: TXN2 successfully pushes committed intent

1. TXN1 (RC) allocates stmt_read_ts=1, write_ts=2
2. TXN1 reads K2 at ts=1, writes K1 at ts=2 with intent
3. TXN1 refreshes K2, succeeds
4. TXN1 commits (status → "committed", write_ts=2)
5. *[TXN2 interleaves before ResolveIntent]*
6. TXN2 (RC) allocates stmt_read_ts=3, tries to read K1 at ts=3
7. TXN2 encounters intent, tries to push
8. Push succeeds (TXN1.status = "committed"), TXN2 resolves intent immediately
9. TXN2 resolves K1 intent: sets ts=2, value=TXN1, intent_txn=0
10. TXN2 reads K1, sees committed value at ts=2
11. TXN2 continues without blocking

**Result**: Non-deterministic pushing allows TXN2 to successfully push a committed transaction's intent and immediately resolve it, avoiding the wait. This models the real push mechanism.

### Case 7b: TXN2 waits despite committed intent (alternate path)

Same setup as Case 7, but:
7. TXN2 non-deterministically chooses to **wait** instead of push
8. TXN2 blocks on intent
9. *[Back to TXN1]*
10. TXN1 resolves intent
11. *[Back to TXN2, now unblocked]*
12. TXN2 reads K1, sees committed value

**Result**: Even with non-deterministic pushing, TXN2 might choose to wait, modeling both execution paths.

### Case 8: TXN2 operates between TXN1's write timestamp and commit timestamp

With `commit_ts_skew=true`, write_ts can advance after the statement:

1. TXN1 (RC) allocates stmt_read_ts=1, write_ts=2
2. TXN1 reads K2 at ts=1, writes K1 at ts=2 with intent
3. TXN1 does StatementRefresh on K2 from ts=1 to ts=2, succeeds, bumps tscache[K2]=2
4. *[TXN2 interleaves]*
5. TXN2 (RC) allocates stmt_read_ts=3, write_ts=4
6. TXN2 tries to read K1, encounters TXN1's intent at ts=2
7. TXN2 tries to push but TXN1.status = "pending", so blocks
8. *[Back to TXN1]*
9. TXN1 MaybeAdvanceBeforeCommit → write_ts advances to 5
10. TXN1 commits with write_ts=5
11. TXN1 resolves intent at ts=5 (atomically updates timestamp)
12. *[Back to TXN2, now unblocked]*
13. TXN2 reads K1, sees committed value at ts=5

**Key insight**: TXN1 wrote the intent at ts=2 but commits at ts=5. The intent timestamp is updated atomically with resolution (as stated in The Proposal section above: "pushing an intent to a later timestamp or replacing it with a committed value happens atomically with removing the original intent"). TXN2 operating at ts=3-4 falls between these, and non-deterministic pushing models the race between blocking and successfully pushing.

### Case 9: RC refresh catches write in the interval after write_ts advances

1. TXN1 (RC) allocates stmt_read_ts=1, write_ts=2
2. TXN1 reads K2 at ts=1
3. *[TXN2 interleaves]*
4. TXN2 (RC) allocates stmt_read_ts=3, write_ts=4
5. TXN2 reads K1 at ts=3, writes K2 at ts=4 with intent
6. TXN2 refreshes K1, commits, resolves K2 intent at ts=4
7. *[Back to TXN1]*
8. TXN1 writes K1 at ts=2 (or later if write_ts advanced)
9. TXN1's write_ts advances to ts=5 (commit_ts_skew=true)
10. TXN1 does StatementRefresh on K2 from stmt_read_ts=1 to write_ts=5
11. Finds committed value at ts=4 in interval (1, 5]
12. TXN1 refresh FAILS, aborts

**Result**: The per-statement refresh correctly detects that K2 was written at ts=4, which is between TXN1's read (ts=1) and its current write_ts (ts=5), preventing a stale read.

### Case 10: SSI refresh catches write when write_ts advances late

1. TXN1 (SSI) allocates txn read_ts=1, write_ts=2
2. TXN1 reads K2 at txn read_ts=1
3. TXN1 writes K1 at write_ts=2 with intent
4. *[TXN2 interleaves]*
5. TXN2 writes K2 at ts=3, commits, resolves intent at ts=3
6. *[Back to TXN1]*
7. TXN1's write_ts advances to ts=4 before commit
8. TXN1 does CommitRefresh from txn read_ts=1 to write_ts=4
9. Finds committed value at ts=3 in interval (1, 4]
10. TXN1 refresh FAILS, aborts

**Result**: SSI's commit-time refresh correctly detects the conflicting write, even though it happened after the statement completed.

### Case 11: TXN1 allocates early timestamps but executes late (timestamp advancement and refresh failure)

This case demonstrates the critical distinction between timestamp allocation ordering and execution ordering:

1. TXN1 (RC) allocates stmt_read_ts=1, write_ts=2
2. *[TXN2 interleaves before TXN1 does any operations]*
3. TXN2 (RC) allocates stmt_read_ts=3, write_ts=4
4. TXN2 reads K1 at ts=3, value=0
5. TXN2 writes K2 at ts=4 with intent
6. TXN2 does StatementRefresh on K1 from ts=3 to ts=4, succeeds
7. TXN2 bumps tscache[K1]=4
8. TXN2 commits, resolves K2 intent at ts=4
9. *[Back to TXN1, now executing with its early timestamps]*
10. TXN1 reads K2 at ts=1, sees value=0 (doesn't see TXN2's write at ts=4 - correct snapshot behavior)
11. TXN1 tries to write K1 at write_ts=2
12. Timestamp cache check: tscache[K1]=4 >= write_ts=2
13. TXN1's write_ts is bumped to ts=5 (allocate new timestamp above tscache)
14. TXN1 writes K1 at ts=5 with intent (write SUCCEEDS)
15. TXN1 does StatementRefresh on K2 from stmt_read_ts=1 to write_ts=5
16. Finds committed value at ts=4 in interval (1, 5]
17. TXN1 refresh FAILS, TXN1 ABORTS

**Result**: The timestamp cache doesn't cause immediate abort - it causes timestamp advancement. TXN1's write succeeds at the bumped timestamp (ts=5), but then the per-statement refresh fails because TXN1 read K2 at ts=1 but is now committing at ts=5, and there's a write at ts=4 in that interval. The timestamp cache bump *indirectly* causes the abort by widening the refresh interval to include the conflicting write.

**Key insight**: This validates the proposal's core mechanism. The timestamp cache bump from TXN2's refresh forces TXN1 to a higher commit timestamp. This expanded interval (1, 5] instead of (1, 2]) then causes TXN1's refresh to detect the stale read and abort. The protection works even when transactions allocate timestamps in a different order than they execute operations.

### Case 12: Early allocation with SSI shows same timestamp advancement pattern

1. TXN1 (SSI) allocates txn read_ts=1, write_ts=2
2. *[TXN2 interleaves before TXN1 does any operations]*
3. TXN2 (RC) allocates stmt_read_ts=3, write_ts=4
4. TXN2 reads K1 at ts=3, writes K2 at ts=4
5. TXN2 does StatementRefresh on K1, bumps tscache[K1]=4
6. TXN2 commits at ts=4
7. *[Back to TXN1 with early timestamps]*
8. TXN1 reads K2 at txn read_ts=1 (sees initial value, TXN2's write is at ts=4)
9. TXN1 tries to write K1 at write_ts=2
10. Timestamp cache check: tscache[K1]=4 >= write_ts=2
11. TXN1's write_ts is bumped to ts=5
12. TXN1 writes K1 at ts=5 with intent (write SUCCEEDS)
13. TXN1 does CommitRefresh on K2 from txn read_ts=1 to write_ts=5
14. Finds committed value at ts=4 in interval (1, 5]
15. TXN1 refresh FAILS, TXN1 ABORTS

**Result**: The same pattern applies to SSI transactions. The timestamp cache causes timestamp advancement (not immediate abort), and then the commit-time refresh fails due to the stale read in the expanded interval.

**Key insight**: The timestamp cache mechanism works the same regardless of isolation level. Both RC (per-statement refresh) and SSI (commit-time refresh) abort when their refresh detects a stale read in the interval between read timestamp and (bumped) write timestamp.
