# Read-Committed Non-Blocking Checks TLA+ Specification

## The Proposal (V3)

Three rules allow non-locking check/cascade reads while maintaining correctness:

1. **Block** when a check read encounters a weak-isolation intent or lock.
2. **Retry** when a check read encounters a newer committed value (FailOnMoreRecent).
3. **Write before read**: perform check reads only after placing the mutation's intents.

Rules 1 and 2 are enforced at read time. Rule 3 is already satisfied in the normal execution path (mutations flush before postquery checks). The exception is the insert fast path, which reads before writing; enforcing rule 3 there requires buffered writes to mature (see the proposal doc).

**Assumptions**: (1) WriteTooOld errors refresh the read timestamp. (2) Intent resolution is atomic — readers never see an intermediate state.

## What the Spec Models

Two conflicting transactions, each performing a mutation and a check read on the other's key (TXN1: writes K1, checks K2; TXN2: writes K2, checks K1). Each transaction is independently assigned SSI or RC isolation. The spec explores all interleavings across:

- Isolation level combinations (SSI×SSI, SSI×RC, RC×SSI, RC×RC)
- Operation order (SSI: either order; RC: write-first per rule 3)
- Timestamp skew (write_ts advancement before statement and before commit)

### RC Flow

1. Write mutation (WriteTooOld pushes write_ts above tscache)
2. Read check with FailOnMoreRecent (blocks on intents, fails on newer committed values)
3. Commit (no refresh needed)

### SSI Flow

The spec models SSI in its current state where the insert fast path can read before writing:

1. Read and write in either order (FailOnMoreRecent on check reads)
2. Commit-time refresh with FailOnMoreRecent (unbounded — needed because the standard bounded refresh `(read_ts, write_ts]` misses conflicting intents that resolve above write_ts)
3. Commit

Once rule 3 is enforced for SSI, its check reads become equivalent to RC — write-before-read with FailOnMoreRecent, no commit-time refresh. See `../NonLockingChecks/` for a simplified spec that models this target state.

### Simplifications

- **All intents block all readers.** The real system lets SSI read through SSI intents above read_ts. Blocking is strictly more conservative.
- **WriteTooOld refresh is not modeled.** The spec skips the eager read refresh on WriteTooOld, making it more permissive. This shows that write-before-read + FailOnMoreRecent alone provides correctness for check reads.
- **Timestamps use non-deterministic ordering.** Unique IDs inserted into a global total order, allowing TLC to explore cases where allocation order differs from logical order.

## Safety Invariant

**NoStaleReads**: if a transaction commits, no value was written between its read_ts and commit_ts for any key it read.

## Running

```bash
# Translate PlusCal, then run TLC:
java -cp tla2tools.jar pcal.trans ReadCommittedChecks.tla
java -cp tla2tools.jar tlc2.TLC -config ReadCommittedChecks.cfg ReadCommittedChecks.tla
```

All invariants (`TypeInvariant`, `NoStaleReads`) and temporal properties (`AllTransactionsFinalize`, `CommittedTransactionsStayCommitted`, `AbortedTransactionsStayAborted`) should pass.
