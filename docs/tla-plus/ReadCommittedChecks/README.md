# Read-Committed Non-Blocking Checks TLA+ Specification

This specification models the non-blocking read mechanism for foreign key checks and cascades across isolation levels (Serializable and Read-Committed).

## The Proposal (V3)

### Problem Statement

We have to prevent stale reads in checks and cascades. Serializable does this by ensuring all reads are refreshed by the time the transaction commits. Read-committed does this by taking locks. What if there was a way we could make RC transactions behave more like SSI transactions for checks and cascades?

We can't just refresh the reads for checks/cascades up to the transaction commit timestamp like a SSI transaction would. This could result in the RC transaction failing with a serializable retry error. That is a non-starter given that RC is meant to prevent the need for app-side retry loops. We need a way to guarantee progress, so that once a RC statement finishes successfully, it cannot cause the transaction to fail (though it may fail for other reasons later).

### Solution

Both correctness and progress are guaranteed if we ensure the following three rules:

1. **All isolation levels** must block when a check/cascade read encounters a weak-isolation intent or FOR UPDATE lock.
2. **All isolation levels** must retry when a check/cascade read encounters a newer committed value (FailOnMoreRecent on the read itself).
3. **Weak isolation levels** must perform their check/cascade reads only after successfully placing the intents (or locks) for the mutation that triggered the check/cascade.

Rules 1 and 2 are enforced at read time via FailOnMoreRecent semantics on the check/cascade read itself (not on a separate refresh step).

### Assumptions

The proposal assumes the following existing system behavior:

1. **WriteTooOld refresh**: Reads are refreshed and the read timestamp advanced when a write gets a WriteTooOld error. This prevents unnecessary statement-level retries and ensures the read timestamp stays close to the write timestamp.
2. **Atomic intent resolution**: Pushing an intent to a higher timestamp or replacing it with a committed value happens atomically with removing the original intent. Readers (including followers) do not observe an intermediate state.

### Correctness

**SSI**: Correctness is guaranteed as before, since SSI transactions refresh reads up to their commit timestamp, preventing stale reads.

**RC**: Rules 1 and 2 force conflicting transactions to block and retry once the RC transaction has placed its intents (or locks). This prevents conflicting transactions from invalidating an RC transaction's check/cascade reads even if the RC transaction's write timestamp is pushed arbitrarily far forward. Rule 3 ensures the RC transaction observes any conflicting transaction that has already placed its intents.

**Mixed**: Rules 1 and 2 ensure that transactions of all isolation levels do not violate constraints when conflicting with a weak-isolation statement that has already completed. Rule 3 ensures that weak-isolation statements check for (and retry on discovering) conflicting writes up to that point.

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
- **RC**: Assigned per-statement, stepped forward to write_ts when a WriteTooOld bumps write_ts (assumption 1)

**Write Timestamp:**
- Assigned at transaction/statement start
- Used for all writes (intents are written at this timestamp)
- Can advance during the transaction's lifetime (due to timestamp cache conflicts)
- When the transaction commits, this becomes the commit timestamp and all intents are resolved at this timestamp

### RC Transaction Flow

RC transactions follow a strict sequential flow (rule 3):

1. **Write** the mutation (places intent, may bump write_ts due to timestamp cache; if bumped, the existing WriteTooOld refresh steps read_ts to write_ts)
2. **Read** the check/cascade with FailOnMoreRecent (blocks on weak-iso intents, follows standard MVCC for SSI intents, fails on newer committed values)
3. **Commit** (no commit-time refresh needed)

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
- For RC: `read_ts` is stepped to write_ts by the WriteTooOld refresh (assumption 1)

This ensures that:
- For RC transactions: The write-then-read sequence with FailOnMoreRecent correctly prevents stale reads
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

If the invariants hold, this validates that the three rules correctly prevent stale reads across all isolation level combinations without requiring locks or full transaction-level refreshes for RC.

## Scenarios Covered

The spec explores all combinations of:

- Isolation levels: SSI x SSI, SSI x RC, RC x SSI, RC x RC
- Statement operation order: For SSI, read-then-write vs write-then-read; for RC, always write-then-read (rule 3)
- Timestamp skew: write_ts advancement before statement and before commit
- Transaction interleaving: various orderings of the two transactions' operations
