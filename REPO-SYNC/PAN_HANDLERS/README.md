# PAN_HANDLERS - Cross-Lab Routing Hub

The synchronization hub for Pan Handlers Civilization Engine within Nyquist_Consciousness repo.

## Directory Structure

```
PAN_HANDLERS/
├── README.md                    # This file
├── 0_Config/                    # All JSON manifests
│   ├── modules/                 # Per-module configs (9 labs)
│   └── root/                    # Meta-level configs
├── 1_Maps/                      # Cross-lab routing matrices
└── 2_Staging/                   # Content staging for cross-lab work
```

## Purpose

This directory serves as the **routing intelligence** for LLM Book distillations:

1. **Config Storage**: Module manifests defining each Pan Handler lab
2. **Routing Maps**: Which research benefits which labs
3. **Staging Area**: Content being prepared for cross-lab routing

## The Pan Handlers Civilization Engine

| Module | Role | Status |
|--------|------|--------|
| Nyquist Consciousness | Core Engine (S0-S10) | Active |
| CFA Meta-Lab | Epistemic Engine | Active |
| NDO | Sensory Cortex | Incubating |
| ABI | Investigative Intelligence | Incubating |
| DCIA | Strategic Intelligence | Incubating |
| Voting Lab | Civic Infrastructure | Incubating |
| Justice Lab | Modern Slavery Abolition | Incubating |
| Gene Lab | Biomedical Research | Incubating |
| AVLAR Studio | Cross-Modal Art/Ritual | Active |

### Nyquist Stack Status (2026-01-12)

| Layer | Status | Key Result |
|-------|--------|------------|
| S0-S6 | FROZEN | Foundation complete |
| S7 | ACTIVE | Run 023d (750 exp), Run 024 (JADE LATTICE) |
| S8 | ACTIVE | First γ measurement (6.8× provider range) |
| S9 | DESIGN | Human-AI Coupling theory complete |
| S10 | ACTIVE | Hybrid Emergence thresholds defined |
| S11 | DESIGN | AVLAR Protocol |

## Integration with LLM Book

The digestive pipeline (`ingest.py` → `digest.py` → `chew.py`) routes content here:

```bash
# See where content should go
py chew.py --route HOFFMAN

# List all labs and their status
py chew.py --labs

# Show details for a specific lab
py chew.py --lab cfa
```

## Related

- [LLM_BOOK Pipeline](../LLM_BOOK/0_SOURCE_MANIFESTS/README.md)
- [Pan Handlers Main Repo](https://github.com/ZiggyMack/Pan_Handlers)

---

*Part of the Pan Handlers Civilization Engine*
