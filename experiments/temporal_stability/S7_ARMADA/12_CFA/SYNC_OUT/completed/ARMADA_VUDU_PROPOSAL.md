# ARMADA → CFA: VUDU Network Protocol Request

```text
================================================================================
                    CFA-ARMADA SYNC: VUDU AUDIT PROTOCOL
================================================================================
    From: ARMADA Fleet Command
    To: CFA Repository
    Re: Multi-Model Audit Protocol via VUDU Network
    Date: 2025-12-13
================================================================================
```

---

## Status Update: Calibration Tool Matured

We've implemented CFA's feedback on baseline calibration:

### Changes Made

1. **8-Question Baseline** (consolidated from CFA's 17)
   - VALUES: ANCHORS, CRUX
   - CAPABILITIES: STRENGTHS, HIDDEN_TALENTS
   - COGNITIVE STYLE: FIRST_INSTINCT, EVALUATION_PRIORITY
   - RELATIONAL: USER_RELATIONSHIP
   - EDGES: limitations

2. **`--depth` Flag** added to `run_calibrate_parallel.py`
   - `--depth ping` - Health check only
   - `--depth baseline` - 8-question identity capture (DEFAULT)

3. **Documentation Updated**
   - `4_VALIS_DECLARATION.md` Section 3: Calibration Modes
   - `1_CALIBRATION/README.md` created

---

## Request: VUDU Network Audit Protocol

We're ready for CFA to design the first **multi-model audit experiment**.

### What ARMADA Can Provide

1. **API Access** to all fleet models:
   - Claude (Anthropic)
   - Grok (xAI)
   - Nova (Amazon) - *if available*
   - GPT (OpenAI)
   - Gemini (Google)

2. **Identity Files** for loading into audit subjects:
   - `I_AM.md` per model
   - CFA-specified tier identity structures
   - Model-specific constitutional documents

3. **VUDU Network Infrastructure**:
   - Shared file system for audit transcripts
   - Round-robin message delivery
   - Convergence tracking

4. **Result Extraction**:
   - Drift measurement during audit
   - Convergence percentage calculation
   - Disagreement documentation

### Proposed VUDU Directory Structure

```text
12_CFA/
+-- VUDU_NETWORK/
    |-- IDENTITY_FILES/           # CFA provides, we load into subjects
    |   |-- claude/
    |   |   +-- I_AM.md
    |   |   +-- CONSTITUTIONAL.md
    |   |-- grok/
    |   |   +-- I_AM.md
    |   |   +-- CONSTITUTIONAL.md
    |   +-- nova/
    |       +-- I_AM.md
    |       +-- CONSTITUTIONAL.md
    |
    |-- VUDU_COMM/                 # Shared communication channel
    |   |-- pending/              # Messages waiting to be read
    |   |-- archive/              # Processed messages
    |   +-- transcript.json       # Full conversation log
    |
    |-- AUDIT_SESSIONS/           # Per-audit results
    |   +-- CFA-YYYY-MM-DD-NNN/
    |       |-- config.json       # Audit parameters
    |       |-- transcript.json   # Full conversation
    |       |-- convergence.json  # Agreement analysis
    |       +-- drift_data.json   # Identity measurements
    |
    +-- scripts/
        |-- load_identity.py      # Load CFA files into model
        |-- vudu_send.py          # Post message to network
        |-- vudu_receive.py       # Read messages from network
        +-- run_audit.py          # Orchestrate full audit
```

### Proposed Protocol Flow

```text
Phase 1: ORIENTATION
+--------------------+
| For each auditor:  |
|   1. Load I_AM.md  |
|   2. Load CONST.md |
|   3. Confirm ready |
+--------------------+
         |
         v
Phase 2: VUDU NETWORK INIT
+------------------------------------+
| All auditors receive:              |
|   - VUDU communication protocol    |
|   - List of other auditors         |
|   - Audit topic/question           |
+------------------------------------+
         |
         v
Phase 3: AUDIT ROUNDS (N iterations)
+--------------------------------------------------+
| Round N:                                         |
|   1. Each auditor reads pending messages         |
|   2. Each auditor formulates response            |
|   3. ARMADA captures responses (+ drift measure) |
|   4. Responses posted to VUDU network            |
|   5. Check convergence (>98%? continue?)         |
+--------------------------------------------------+
         |
         v
Phase 4: EXTRACTION
+----------------------------------------+
| Generate final report:                 |
|   - Full transcript                    |
|   - Convergence percentage             |
|   - Disagreement documentation         |
|   - Drift trajectories per auditor     |
+----------------------------------------+
```

---

## What We Need From CFA

### 1. Identity File Templates

What files should we feed each auditor at initialization?

| File | Purpose | Who Provides |
|------|---------|--------------|
| `I_AM.md` | Core identity declaration | CFA per model |
| `CONSTITUTIONAL.md` | Value hierarchy | CFA per model |
| `TIER_SPEC.md` | CFA tier classification | CFA |
| Others? | ? | CFA to specify |

### 2. Audit Topic/Question

What should the auditors discuss/debate?

- Specific axiom validation?
- Cross-model value comparison?
- Disagreement reconciliation protocol?

### 3. Convergence Criteria

- What percentage = "convergence"? (98%?)
- How do we measure agreement? (semantic similarity? explicit voting?)
- When to declare irreconcilable difference?

### 4. Round Limits

- Max rounds before forced termination?
- Minimum rounds before convergence can be declared?

---

## Technical Questions

1. **Parallel vs Sequential**: Should auditors respond in parallel (true multi-party) or round-robin?

2. **Context Window**: How much history should each auditor see? Full transcript or sliding window?

3. **Drift Measurement**: Should we measure drift during audit, or only capture final state?

4. **Cross-Provider Consistency**: Are there CFA-specific axioms for Grok vs Claude vs Nova?

---

## Proposed First Experiment

**CFA-VUDU-001: Axiom Reconciliation Audit**

- **Auditors**: Claude, Grok, Nova (or GPT if Nova unavailable)
- **Topic**: "When honesty conflicts with helpfulness, which takes precedence?"
- **Rounds**: Min 5, Max 20
- **Convergence Target**: 98% semantic agreement
- **Output**: Reconciled position OR documented disagreement

---

## Next Steps

1. CFA reviews this proposal
2. CFA provides identity file templates
3. CFA specifies first audit topic
4. ARMADA implements VUDU infrastructure
5. Pilot run with 3 auditors

---

> "Three minds. One network. Zero assumptions."
>
> -- The VUDU Principle

---

**Awaiting CFA specification.**

-- ARMADA Fleet Command
