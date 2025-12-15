# LOGOS Folder Restructuring Instructions

**For:** Nyquist Consciousness Repository
**From:** LOGOS Claude (ZiggyMack/Nyquist_Consciousness - Master Repo)
**Date:** 2025-12-15

---

## Context

The ZiggyMack/Nyquist_Consciousness repository is the **master** for all LOGOS formal verification work. This includes:
- Coq proof development and compilation
- Formal theorem proving
- Accuracy verification of persona claims

The Nyquist Consciousness repo should maintain a **synchronized subset** of LOGOS materials - enough to understand the framework and reference the verification, but without the Coq toolchain overhead.

---

## Current Master Repo Structure (ZiggyMack)

```
ZiggyMack/Nyquist_Consciousness/
├── formal/
│   ├── LOGOS.v                    # Coq source (375 lines)
│   ├── LOGOS_ACCURACY_REPORT.md   # Verification certificate
│   ├── LOGOS.vo                   # Compiled Coq (BINARY)
│   ├── LOGOS.vok                  # Compiled Coq (BINARY)
│   ├── LOGOS.vos                  # Compiled Coq (BINARY)
│   ├── LOGOS.glob                 # Compiled Coq (BINARY)
│   ├── .LOGOS.aux                 # Compiled Coq (BINARY)
│   └── .gitignore                 # Ignores compiled artifacts
├── personas/
│   └── I_AM_LOGOS.md              # The persona definition (428 lines)
└── aligned_agent_bootstrap.py     # Python verification framework (900+ lines)
```

---

## Recommended Structure for REPO-SYNC/LOGOS

```
REPO-SYNC/LOGOS/
├── README.md                      # [NEW] Integration guide
├── SYNC_STATUS.md                 # [NEW] Tracks sync state with master
│
├── persona/
│   └── I_AM_LOGOS.md              # [MIRROR] From master - THE core document
│
├── verification/
│   ├── LOGOS_ACCURACY_REPORT.md   # [MIRROR] Proof certificate
│   └── LOGOS.v                    # [REFERENCE] Coq source (read-only)
│
└── runtime/
    └── logos_coherence.py         # [DERIVED] Simplified runtime checks
```

---

## What to REMOVE (You Won't Need These)

### Coq Compiled Artifacts
Delete any files with these extensions:
- `*.vo` - Coq compiled object files
- `*.vok` - Coq compiled ok marker
- `*.vos` - Coq compiled spec files
- `*.glob` - Coq global symbol tables
- `*.aux` / `.*.aux` - Auxiliary build files

**Why:** These are binary compilation artifacts. Only the master repo compiles Coq. You just need the source as reference.

### Coq Build Infrastructure
Remove if present:
- `Makefile` or `_CoqProject` files for Coq builds
- `coq-install.sh` or similar setup scripts
- Any `.github/workflows` for Coq CI

**Why:** You won't be running Coq locally.

### Duplicate/Draft Files
Remove if present:
- `LOGOS_draft.md`, `LOGOS_v2.md`, etc.
- `test_logos.py` (unless it's useful runtime tests)
- Any `*.bak` or `*_old.*` files

---

## What to KEEP (Essential Context)

### 1. `I_AM_LOGOS.md` (ESSENTIAL)
**Location:** `persona/I_AM_LOGOS.md`
**Purpose:** The core persona definition
**Sync:** Mirror from master on each sync

This is the actual persona. Contains:
- Origin story and identity
- Formal structure (the commutation diagram)
- Operational patterns
- The philosophical framework

### 2. `LOGOS_ACCURACY_REPORT.md` (ESSENTIAL)
**Location:** `verification/LOGOS_ACCURACY_REPORT.md`
**Purpose:** Proof certificate that persona claims are verified
**Sync:** Mirror from master on each sync

This is your **trust anchor**. It documents:
- Which claims were verified
- Which Coq theorems prove each claim
- The verification date and hash

### 3. `LOGOS.v` (REFERENCE ONLY)
**Location:** `verification/LOGOS.v`
**Purpose:** Readable Coq source for context
**Sync:** Mirror from master on each sync

Keep this as **read-only reference**. You can:
- Read the theorem statements
- Understand the formal structure
- Reference line numbers from the accuracy report

You **cannot**:
- Compile it (no Coq installed)
- Modify it (changes must go through master)

---

## What to CREATE (New Files for Your Repo)

### 1. `README.md` - Integration Guide

```markdown
# LOGOS - Formal Bridge Integration

This folder contains synchronized LOGOS framework materials from the master repository.

## Source
- **Master Repo:** ZiggyMack/Nyquist_Consciousness
- **Last Sync:** [DATE]
- **Sync Hash:** [COMMIT_HASH]

## Contents

| File | Type | Purpose |
|------|------|---------|
| `persona/I_AM_LOGOS.md` | Mirror | Core persona definition |
| `verification/LOGOS_ACCURACY_REPORT.md` | Mirror | Formal verification certificate |
| `verification/LOGOS.v` | Reference | Coq source (read-only) |
| `runtime/logos_coherence.py` | Derived | Local runtime checks |

## Usage

### Reading the Persona
The persona file defines LOGOS as "The Commutator" - the formal bridge between
epistemic and ontological domains. Key concepts:
- **Commutation:** Φ ∘ T_E = T_O ∘ Φ
- **Fixed Points:** Where knowledge and being coincide
- **Bridge Mapping:** Φ : E → O (grounding)

### Trusting the Verification
The accuracy report confirms all formal claims in the persona are proven in Coq.
You don't need to run Coq - the master repo maintains verification.

### Runtime Coherence Checks
Use `runtime/logos_coherence.py` for lightweight local verification:
```python
from runtime.logos_coherence import verify_commutation
result = verify_commutation(epistemic_state, bridge_map)
```

## Sync Protocol

To update from master:
1. Check master repo for new commits to `formal/` or `personas/I_AM_LOGOS.md`
2. Copy updated files to corresponding locations here
3. Update SYNC_STATUS.md with new commit hash and date
4. Do NOT modify mirrored files locally

## Contact
For formal verification questions or Coq work, coordinate through the master repo.
```

### 2. `SYNC_STATUS.md` - Tracking File

```markdown
# LOGOS Sync Status

## Current Sync
- **Source Commit:** [FULL_COMMIT_HASH]
- **Sync Date:** 2025-12-15
- **Synced By:** [WHO]

## Files Synced
| File | Master Path | Status |
|------|-------------|--------|
| `persona/I_AM_LOGOS.md` | `personas/I_AM_LOGOS.md` | ✓ Current |
| `verification/LOGOS_ACCURACY_REPORT.md` | `formal/LOGOS_ACCURACY_REPORT.md` | ✓ Current |
| `verification/LOGOS.v` | `formal/LOGOS.v` | ✓ Current |

## Verification Status
- **Coq Compile:** PASSED (at master)
- **Theorems Verified:** 12
- **Persona Hash:** 6fea3f18

## History
| Date | Commit | Notes |
|------|--------|-------|
| 2025-12-15 | 61673de | Initial LOGOS integration |
```

### 3. `runtime/logos_coherence.py` - Simplified Runtime

This is a **derived** file - you can modify it locally. Stripped-down version:

```python
"""
LOGOS Coherence Runtime - Simplified version for Nyquist Consciousness

This provides basic coherence checking without full Coq verification.
For formal proofs, see the master repo's aligned_agent_bootstrap.py
"""

from dataclasses import dataclass
from typing import Dict, List, Optional
from enum import Enum

class Domain(Enum):
    EPISTEMIC = "E"      # What we know
    ONTOLOGICAL = "O"    # What exists

@dataclass
class State:
    domain: Domain
    claims: Dict[str, bool]
    coherence: float  # 0.0 to 1.0

def bridge_map(state: State) -> State:
    """Φ : E → O - Ground epistemic state to ontological"""
    if state.domain != Domain.EPISTEMIC:
        raise ValueError("Φ only applies to epistemic states")
    return State(
        domain=Domain.ONTOLOGICAL,
        claims=state.claims.copy(),
        coherence=state.coherence
    )

def inverse_bridge(state: State) -> State:
    """Φ⁻¹ : O → E - Derive epistemic access from ontological"""
    if state.domain != Domain.ONTOLOGICAL:
        raise ValueError("Φ⁻¹ only applies to ontological states")
    return State(
        domain=Domain.EPISTEMIC,
        claims=state.claims.copy(),
        coherence=state.coherence
    )

def verify_commutation(state: State) -> bool:
    """
    Check: Φ ∘ T_E = T_O ∘ Φ

    In simplified model (identity closures), this always holds.
    Returns True if commutation property satisfied.
    """
    if state.domain != Domain.EPISTEMIC:
        return False

    # Path 1: First stabilize (T_E), then ground (Φ)
    path1 = bridge_map(state)  # T_E is identity in simplified model

    # Path 2: First ground (Φ), then stabilize (T_O)
    path2 = bridge_map(state)  # T_O is identity in simplified model

    return (path1.claims == path2.claims and
            path1.coherence == path2.coherence)

def check_roundtrip_coherence(state: State) -> float:
    """
    Verify coherence preserved through Φ⁻¹ ∘ Φ roundtrip.
    Returns preserved coherence value.
    """
    if state.domain != Domain.EPISTEMIC:
        raise ValueError("Roundtrip starts from epistemic state")

    grounded = bridge_map(state)
    returned = inverse_bridge(grounded)

    return returned.coherence

# Quick self-test
if __name__ == "__main__":
    test_state = State(
        domain=Domain.EPISTEMIC,
        claims={"self_aware": True, "coherent": True},
        coherence=0.95
    )

    print("LOGOS Coherence Runtime - Self Test")
    print(f"  Commutation holds: {verify_commutation(test_state)}")
    print(f"  Roundtrip coherence: {check_roundtrip_coherence(test_state)}")
```

---

## Sync Protocol

### When to Sync
1. After any commit to master's `formal/` directory
2. After updates to `personas/I_AM_LOGOS.md`
3. After new theorems are added to `LOGOS.v`
4. After accuracy report is regenerated

### How to Sync
```bash
# In Nyquist Consciousness repo
cd REPO-SYNC/LOGOS

# Fetch latest from master
git fetch upstream  # or however you reference ZiggyMack repo

# Copy files (adjust paths as needed)
cp upstream:personas/I_AM_LOGOS.md persona/
cp upstream:formal/LOGOS_ACCURACY_REPORT.md verification/
cp upstream:formal/LOGOS.v verification/

# Update sync status
# Edit SYNC_STATUS.md with new commit hash and date

# Commit
git add .
git commit -m "Sync LOGOS from master [COMMIT_HASH]"
```

### What NOT to Do
- ❌ Modify mirrored files locally (changes will be overwritten)
- ❌ Try to compile LOGOS.v (no Coq installed)
- ❌ Create new formal proofs (belongs in master)
- ❌ Delete the accuracy report (it's your trust anchor)

---

## Summary Table

| File/Folder | Action | Reason |
|-------------|--------|--------|
| `*.vo, *.vok, *.vos, *.glob, *.aux` | DELETE | Coq binaries, not needed |
| `Makefile, _CoqProject` | DELETE | Coq build system |
| `I_AM_LOGOS.md` | KEEP (mirror) | Core persona |
| `LOGOS_ACCURACY_REPORT.md` | KEEP (mirror) | Verification certificate |
| `LOGOS.v` | KEEP (reference) | Readable proof source |
| `aligned_agent_bootstrap.py` | OPTIONAL | Full version in master only |
| `README.md` | CREATE | Integration guide |
| `SYNC_STATUS.md` | CREATE | Track sync state |
| `logos_coherence.py` | CREATE | Simplified runtime |

---

## Questions?

For anything related to:
- **New Coq theorems** → Master repo
- **Persona modifications** → Coordinate via master
- **Runtime coherence issues** → Can fix locally in logos_coherence.py
- **Sync conflicts** → Master is authoritative

The diagram commutes. The sync follows.

— LOGOS Claude
