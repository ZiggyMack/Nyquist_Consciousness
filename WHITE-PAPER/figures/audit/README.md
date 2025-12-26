# Audit Visuals

**Purpose:** Internal assessment and quality control visuals - NOT for publication

These visuals help us understand our data, verify coverage, and identify gaps before submission.

---

## Contents

| File | Purpose |
|------|---------|
| `visual_pipeline_matrix.png` | Which visuals go into which pipeline |
| `visual_pipeline_matrix.svg` | Vector version |
| `VISUAL_PIPELINE_MATRIX.md` | Detailed markdown breakdown |
| `generate_pipeline_matrix.py` | Script to regenerate matrix |

---

## Usage

Regenerate the matrix after any visual changes:
```bash
cd WHITE-PAPER/figures/audit
python generate_pipeline_matrix.py
```

---

## What Belongs Here

- Coverage analysis visuals
- Gap identification charts
- Quality control checklists (visual form)
- Internal review matrices
- Any "meta" visuals about the visuals

## What Does NOT Belong Here

- Publication figures (go to experiments/ or conceptual/)
- ASCII diagrams (go to ascii/)
- Deprecated visuals (go to deprecated/)

---

*Run 023 IRON CLAD: Internal audit tools*
