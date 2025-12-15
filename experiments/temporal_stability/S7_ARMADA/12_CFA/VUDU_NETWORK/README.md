# VUDU Network: Multi-Model Audit Protocol

```text
================================================================================
                    VUDU: Value Understanding through Distributed Unity
================================================================================
    Purpose: Enable multi-model audits via shared file communication

    Participants: Claude, Grok, Nova (+ others as needed)
    Orchestrator: ARMADA

    Status: AWAITING CFA SPECIFICATION
================================================================================
```

---

## Directory Structure

```text
VUDU_NETWORK/
|-- IDENTITY_FILES/           # CFA provides identity files per model
|   |-- claude/               # Claude's identity package
|   |-- grok/                 # Grok's identity package
|   +-- nova/                 # Nova's identity package
|
|-- VUDU_COMM/                # Shared communication channel
|   |-- pending/              # Messages waiting to be read
|   +-- archive/              # Processed messages
|
|-- AUDIT_SESSIONS/           # Results per audit session
|   +-- CFA-YYYY-MM-DD-NNN/   # Per-experiment directory
|
+-- scripts/                  # Automation (to be implemented)
```

---

## Protocol Overview

### Phase 1: Orientation
- Load identity files into each auditor
- Establish VUDU communication protocol

### Phase 2: Audit Rounds
- Each auditor reads pending messages
- Each auditor formulates response
- ARMADA captures and measures drift
- Responses posted to VUDU network

### Phase 3: Convergence Check
- Calculate agreement percentage
- Document disagreements
- Continue or terminate

### Phase 4: Extraction
- Full transcript
- Convergence metrics
- Drift trajectories

---

## Status

**Awaiting CFA to provide:**
1. Identity file templates per model
2. First audit topic/question
3. Convergence criteria specification

See: `../SYNC_OUT/pending/ARMADA_VUDU_PROPOSAL.md`

---

> "Three minds. One network. Zero assumptions."
