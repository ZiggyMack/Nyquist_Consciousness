# Nova Inbox

**Purpose:** Drop audit requests here. Nova (or Claude acting as Nova) will process and respond in `NOVA_OUT.md`.

**Last processed:** *Never*

---

## Current Request

*No pending request.*

---

## Request Format

```
## Request: [SHORT_TITLE]

**Date:** YYYY-MM-DD
**Requester:** [who is asking]
**Target files:**
- path/to/file1.md
- path/to/file2.md

**Audit type:** [claim-evidence | framing-symmetry | cross-pipeline | routing | other]

**Specific question:**
[What asymmetry or consistency issue do you want checked?]

**Constraints:** [tone/audience/length if any]
```

---

## Example Request

```
## Request: JADE LATTICE claim check

**Date:** 2026-01-08
**Requester:** Ziggy
**Target files:**
- WHITE-PAPER/theory/MINIMUM_PUBLISHABLE_CLAIMS.md
- experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/README.md

**Audit type:** claim-evidence

**Specific question:**
Is Claim D (I_AM effectiveness) proportionally supported by the JADE LATTICE Run 024 results? Are we overclaiming or underclaiming?

**Constraints:** Be direct, flag specific line numbers if issues found.
```

---
