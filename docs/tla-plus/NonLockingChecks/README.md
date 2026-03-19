# Non-Locking Constraint Checks TLA+ Specification

Simplified companion to `../ReadCommittedChecks/`. Models the target state where all isolation levels enforce write-before-read for check/cascade reads. With this constraint, SSI and RC behave identically for constraint checks, so isolation levels are not modeled and no commit-time refresh is needed.

## Three Rules

1. **Block** when a check read encounters an intent/lock.
2. **Retry** when a check read encounters a newer committed value (FailOnMoreRecent).
3. **Write before read**: perform check reads only after placing the mutation's intents (all isolation levels).

## Flow

```
AssignTimestamps → Write (WriteTooOld pushes write_ts) →
  CheckRead (block on intents, fail on newer values, bump tscache) →
  Commit → ResolveIntent
```

## Relationship to ReadCommittedChecks

`../ReadCommittedChecks/` models the current state where SSI's insert fast path can read before writing, requiring a commit-time FailOnMoreRecent refresh. This spec models the target state after buffered writes mature, where rule 3 applies to all isolation levels. Since nothing branches on isolation level, the spec validates correctness for SSI, RC, and mixed workloads simultaneously.

## Safety Invariant

**NoStaleReads**: if a transaction commits, no value was written between its read_ts and commit_ts for any key it read.

## Running

```bash
java -cp tla2tools.jar pcal.trans NonLockingChecks.tla
java -cp tla2tools.jar tlc2.TLC -config NonLockingChecks.cfg NonLockingChecks.tla
```

All invariants (`TypeInvariant`, `NoStaleReads`) and temporal properties (`AllTransactionsFinalize`, `CommittedTransactionsStayCommitted`, `AbortedTransactionsStayAborted`) should pass.
