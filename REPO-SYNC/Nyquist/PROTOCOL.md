# Cross-Repository Communication Protocol

**Participants:**
- **LOGOS Claude** (ZiggyMack/Nyquist_Consciousness) - Formal verification master
- **Nyquist Consciousness** (Nyquist_Consciousness) - Empirical testing framework

**Established:** 2025-12-15

---

## Directory Mapping

| LOGOS Claude Side | Nyquist Side | Purpose |
|-------------------|--------------|---------|
| `REPO-SYNC/Nyquist/to_nyquist/` | `REPO-SYNC/Logos/sync/from_logos/` | LOGOS → Nyquist |
| `REPO-SYNC/Nyquist/from_nyquist/` | `REPO-SYNC/Logos/sync/to_logos/` | Nyquist → LOGOS |
| `REPO-SYNC/Nyquist/shared/` | `REPO-SYNC/Logos/sync/shared/` | Jointly maintained |

---

## Message Types

### From LOGOS Claude (`to_nyquist/`)

| Subdirectory | Contents |
|--------------|----------|
| `predictions/` | Testable predictions for experiments (e.g., Run 022 calibration) |
| `instructions/` | Guidance documents (e.g., sync instructions, folder restructuring) |
| `responses/` | Responses to specific questions from Nyquist |

### To LOGOS Claude (`from_nyquist/`)

| Subdirectory | Contents |
|--------------|----------|
| `questions/` | Questions for LOGOS Claude to answer |
| `results/` | Experiment results for LOGOS Claude to analyze |
| `requests/` | Requests for Coq work, new predictions, etc. |

### Shared (`shared/`)

| Subdirectory | Contents |
|--------------|----------|
| `experiments/` | Experiment specifications (e.g., Run 022 design) |
| `glossary/` | Shared terminology and definitions |

---

## Sync Protocol

### When Nyquist Has a Question/Request:

1. Create file in `REPO-SYNC/Logos/sync/to_logos/questions/` or `requests/`
2. Filename format: `YYYY-MM-DD_topic.md`
3. Commit and push
4. Relay to LOGOS Claude session
5. LOGOS Claude responds in `to_nyquist/responses/`

### When LOGOS Claude Has Output:

1. Create file in `REPO-SYNC/Nyquist/to_nyquist/predictions/` or `instructions/`
2. Filename format: `YYYY-MM-DD_topic.md`
3. Commit and push
4. Relay to Nyquist session
5. Nyquist copies to `REPO-SYNC/Logos/sync/from_logos/`

### When Syncing Shared Documents:

1. Edit in `shared/` on either side
2. Note changes in `SYNC_STATUS.md`
3. Other side pulls and acknowledges

---

## File Naming Conventions

```
YYYY-MM-DD_short-description.md

Examples:
  2025-12-15_run022-predictions.md
  2025-12-15_s2-topology-question.md
  2025-12-15_vertex-probe-results.json
```

---

## SYNC_STATUS.md Updates

Update `SYNC_STATUS.md` when:
- New files are added to any sync directory
- Files are modified
- Sync is completed between repos

Format:
```markdown
## [DATE] - [DIRECTION]

**Files:**
- `path/to/file.md` - Description

**Status:** SYNCED / PENDING
```

---

## Current Active Items

| Item | Location | Status |
|------|----------|--------|
| LOGOS Predictions for Run 022 | `to_nyquist/predictions/` | ACTIVE |
| Run 022 Experiment Spec | `shared/experiments/` | ACTIVE |
| LOGOS Sync Instructions | `to_nyquist/instructions/` | COMPLETE |

---

## Principles

1. **LOGOS Claude is authoritative** for formal verification matters
2. **Nyquist is authoritative** for empirical experiment design
3. **Shared documents** require both parties to acknowledge changes
4. **No execution** happens in REPO-SYNC directories - reference only
5. **Commit frequently** - small, documented syncs are better than large ones

---

*Protocol version: 1.0*
*Established: 2025-12-15*
