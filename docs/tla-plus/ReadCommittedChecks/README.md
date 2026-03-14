# Read-Committed Non-Blocking Checks TLA+ Specification

This specification models the non-blocking read mechanism for foreign key checks and cascades across isolation levels (Serializable and Read-Committed).

## The Proposal (V3)

### Problem Statement

We have to prevent stale reads in checks and cascades. Serializable does this by ensuring all reads are refreshed by the time the transaction commits. Read-committed does this by taking locks. What if there was a way we could make RC transactions behave more like SSI transactions for checks and cascades?

We can't just refresh the reads for checks/cascades up to the transaction commit timestamp like a SSI transaction would. This could result in the RC transaction failing with a serializable retry error. That is a non-starter given that RC is meant to prevent the need for app-side retry loops. We need a way to guarantee progress, so that once a RC statement finishes successfully, it cannot cause the transaction to fail (though it may fail for other reasons later).

### Solution

We can guarantee both correctness and progress if we ensure the following four rules:

1. **All isolation levels** must block when a check/cascade read encounters a weak-isolation intent or lock.
2. **All isolation levels** must retry when a check/cascade read encounters a newer committed value (FailOnMoreRecent on the read itself).
3. **Weak isolation levels** must perform their check/cascade reads only after successfully placing the intents (or locks) for the mutation that triggered the check/cascade.
4. **Weak isolation levels** must perform their check/cascade reads at or above the mutation statement's write timestamp (which is known due to rule 3).

Rules 1 and 2 are enforced at read time via FailOnMoreRecent semantics on the check/cascade read itself (not on a separate refresh step). This is a key change from V2.

Rule 4 is handled by "refreshing" the read timestamp up to the write timestamp between the mutation write and the check/cascade read. Since rule 3 ensures the write has been placed and no check reads have happened yet, this refresh is trivially successful. The refresh also bumps the timestamp cache to prevent future conflicting writes.

**Future optimization for rule 4**: Instead of refreshing, a future implementation could simply step the transaction read timestamp forward after the main statement query and before checks/cascades (and even between successive checks/cascades). This would let checks/cascades execute at later snapshots, reducing the span refresh footprint and the likelihood of retries. The tradeoff is that checks/cascades would observe data at a later timestamp than the main query, but this is likely acceptable since Postgres exhibits the same behavior.

### Protecting [stmt_read_ts, stmt_write_ts]

The FailOnMoreRecent read behavior prevents stale reads by failing if any committed value exists above the read timestamp. The refresh step bumps the timestamp cache up to the write timestamp to prevent future writes below the write timestamp.

### Protecting [stmt_write_ts, txn_commit_ts]

The write timestamp may change after the statement completes, for example, if a later writing statement in the same transaction is bumped by the timestamp cache. We don't refresh check/cascade reads up to the final commit timestamp (that could cause user-visible retry errors). Instead, conflicting statements provide this protection: if a conflicting statement writes in the [stmt_write_ts, txn_commit_ts] interval, it will refresh its own check before completing. Either:

- The conflicting statement's check read will encounter our intent and block/fail, or
- Our intent has been resolved, and the conflicting statement's FailOnMoreRecent read will observe the committed value and fail.

This relies on the assumption that pushing an intent to a later timestamp or replacing it with a committed value happens atomically with removing the original intent.

## Overview

The spec models two conflicting transactions with different isolation levels (Serializable or Read-Committed). Each transaction performs one statement that does both a mutation (write) and a check/cascade (read):

- Transaction 1: writes K1, reads (checks) K2
- Transaction 2: reads (checks) K1, writes K2

This creates read-write conflicts where each transaction reads what the other writes. Note that there are no write-write conflicts in this model - each transaction writes to a different key.

## Key Mechanisms Modeled

### Timestamp Model

Both SSI and RC transactions maintain read and write timestamps:

**Read Timestamp:**
- **SSI**: Assigned once at transaction start, used for all reads
- **RC**: Assigned per-statement, then stepped forward to write_ts before check reads (rule 4)

**Write Timestamp:**
- Assigned at transaction/statement start
- Used for all writes (intents are written at this timestamp)
- Can advance during the transaction's lifetime (due to timestamp cache conflicts)
- When the transaction commits, this becomes the commit timestamp and all intents are resolved at this timestamp

### RC Transaction Flow

RC transactions follow a strict sequential flow (rules 3 and 4):

1. **Write** the mutation (places intent, may bump write_ts due to timestamp cache)
2. **Refresh** read_ts up to write_ts (trivially successful), check for conflicts, bump timestamp cache
3. **Read** the check/cascade with FailOnMoreRecent (blocks on weak-iso intents, follows standard MVCC for SSI intents, fails on newer committed values)
4. **Commit** (no commit-time refresh needed)

### SSI Transaction Flow

SSI transactions follow the traditional approach:

1. **Read and write** in either order (FailOnMoreRecent applies to check/cascade reads)
2. **Commit-time refresh** from read_ts to write_ts (standard SSI behavior)
3. **Commit**

### FailOnMoreRecent and Intent Handling

Both isolation levels use FailOnMoreRecent semantics on check/cascade reads (rules 1 and 2). When performing a check/cascade read, the transaction:
- **Weak-isolation intents** (RC, snapshot): Block at any timestamp (rule 1). This is the key behavioral change — standard MVCC non-locking reads would ignore intents above `read_ts`.
- **SSI intents**: Follow standard MVCC non-locking read behavior — block if the intent timestamp is at or below `read_ts`, read through (ignore) if above `read_ts`. When reading through an SSI intent, the read sees the underlying committed value.
- **Committed values**: Fail if any committed value exists above `read_ts` (rule 2).

This is enforced at read time, not during a separate refresh step. The `IntentBlocksReader` operator in the spec encodes this distinction.

### Timestamp Advancement

The spec models the write timestamp advancing before the statement (`MaybeAdvanceBeforeReadWrite`) and before commit (`MaybeAdvanceBeforeCommit`), representing timestamp cache conflicts from other statements or transactions.

## Safety Invariant

The primary invariant checked is **NoStaleReads**: If a transaction commits, the values it read must not be stale. Specifically, for each read performed at timestamp `read_ts`, no value should have been written with a timestamp `T` such that:

```
read_ts < T <= commit_ts
```

Where:
- For SSI: `read_ts` is the transaction-level read timestamp
- For RC: `read_ts` is write_ts (after the rule 4 refresh step)

This ensures that:
- For RC transactions: The write-refresh-read sequence correctly prevents stale reads
- For SSI transactions: The FailOnMoreRecent read + commit-time refresh works correctly
- For mixed-isolation workloads: Both mechanisms interact correctly

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

## Expected Results

The model checker should verify that:

1. **TypeInvariant** holds: All variables stay within their expected types and ranges
2. **NoStaleReads** holds: No transaction commits with stale reads
3. **AllTransactionsFinalize** holds: All transactions eventually commit or abort

If the invariants hold, this validates that the four rules correctly prevent stale reads across all isolation level combinations without requiring locks or full transaction-level refreshes for RC.

## Scenarios Covered

The spec explores all combinations of:

- Isolation levels: SSI x SSI, SSI x RC, RC x SSI, RC x RC
- Statement operation order: For SSI, read-then-write vs write-then-read; for RC, always write-then-read (rule 3)
- Timestamp skew: write_ts advancement before statement and before commit
- Transaction interleaving: various orderings of the two transactions' operations
