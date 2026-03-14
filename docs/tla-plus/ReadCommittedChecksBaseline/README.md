# Read-Committed Checks Baseline TLA+ Specification

This specification models the **current system behavior** for foreign key and unique constraint enforcement across isolation levels. It serves as the baseline comparison for the proposed V3 non-locking checks (see `ReadCommittedChecks` spec).

## Current System Behavior

### RC: Locking Reads with FailOnMoreRecent

RC transactions currently use **replicated locking reads** for check/cascade operations. The read and write can happen in either order within the statement:

- **Locking read** the check/cascade key:
  - Block on ALL intents (FailOnMoreRecent intent behavior — no isolation-level distinction)
  - Fail on committed values above read_ts (FailOnMoreRecent value behavior)
  - Acquire a replicated lock on the key
  - Read the committed value
- **Write** the mutation (place intent, may bump write_ts due to timestamp cache; waits for locks held by other transactions)
- **Commit** (resolve intent, release lock, bump tscache to commit_ts)

The lock prevents concurrent writes to the checked key while the transaction is pending. Combined with FailOnMoreRecent (which catches already-committed values above read_ts), this covers the full range `[read_ts, commit_ts]`:
- `[read_ts, lock_acquire_time]`: protected by FailOnMoreRecent (fails on committed values above read_ts)
- `[lock_acquire_time, commit_ts]`: protected by the lock (blocks concurrent writes)

### SSI: Standard Non-Locking Reads + Commit Refresh

SSI transactions use **standard non-locking reads** (no FailOnMoreRecent). The read and write can happen in either order:

- **Read**: block on intents at or below read_ts, read through intents above read_ts, read committed values at or below read_ts
- **Write**: place intent, bump write_ts if needed due to timestamp cache or locks
- **Commit-time refresh** from read_ts to write_ts (fails on any committed value or intent in the window)
- **Commit**

The commit-time refresh is the safety net that catches any values committed in `[read_ts, write_ts]`.

### Replicated Locks

Locks are modeled explicitly:
- Only RC transactions acquire locks (during locking reads)
- All write operations (both RC and SSI) check for locks before proceeding — a write to a locked key waits for the lock holder to finish
- Locks are released on commit (with tscache bump to commit_ts) or abort

## Differences from the V3 Proposal

| Aspect | Baseline (Current) | V3 Proposal |
|--------|-------------------|-------------|
| RC check reads | Locking + FailOnMoreRecent | Non-locking + FailOnMoreRecent |
| RC intent blocking | ALL intents | Weak-iso intents only (rule 1) |
| RC read/write order | Either order (lock provides correctness) | Write before read required (rule 3) |
| RC refresh step | None needed (lock provides protection) | Refresh read_ts to write_ts (rule 4) |
| SSI check reads | Standard non-locking (no FailOnMoreRecent) | FailOnMoreRecent (rule 2) |
| SSI intent blocking | Standard MVCC (at/below read_ts only) | Weak-iso: all timestamps; SSI: standard MVCC |
| Replicated locks | Required for RC | Not required |

## Running the Spec

### Translate PlusCal to TLA+

```bash
java -cp tla2tools.jar pcal.trans ReadCommittedChecksBaseline.tla
```

### Run the Model Checker

```bash
java -cp tla2tools.jar tlc2.TLC -config ReadCommittedChecksBaseline.cfg ReadCommittedChecksBaseline.tla
```

## Expected Results

The model checker should verify that:

1. **TypeInvariant** holds
2. **NoStaleReads** holds — replicated locks + FailOnMoreRecent (for RC) and commit-time refresh (for SSI) correctly prevent stale reads
3. **AllTransactionsFinalize** holds — deadlock detection ensures progress

## Scenarios Covered

The spec explores all combinations of:

- Isolation levels: SSI x SSI, SSI x RC, RC x SSI, RC x RC
- Statement operation order: read-then-write vs write-then-read (both isolation levels explore both orders)
- Timestamp skew: write_ts advancement before statement and before commit
- Lock contention: writes blocked by RC replicated locks
- Transaction interleaving: various orderings of the two transactions' operations
