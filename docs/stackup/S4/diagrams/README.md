<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
impacts:
  - ../README.md
keywords:
  - consciousness
  - documentation
-->
# S4 Diagrams — High-Resolution Exports

This directory contains high-resolution diagram source files for the S4 mathematical framework.

## Diagram Files

### 1. Compression Pipeline
**File:** `compression_pipeline.mmd`
**Used in:** [S4_CORE_AXIOMS.md](../S4_CORE_AXIOMS.md)
**Purpose:** Visual flow from original persona (P) → compression (C) → Tier-3 seed (T) → reconstruction (R) → reconstructed persona (P')

### 2. Domain Invariance Lattice
**File:** `domain_lattice.mmd`
**Used in:** [S4_CORE_AXIOMS.md](../S4_CORE_AXIOMS.md)
**Purpose:** Hierarchical structure showing TECH > ANAL > SELF ≈ PHIL > NARR

### 3. Drift Geometry
**File:** `drift_geometry.mmd`
**Used in:** [S4_COMPRESSION_FORMALISM.md](../S4_COMPRESSION_FORMALISM.md)
**Purpose:** 2D plot showing drift space with domain positioning and boundaries

### 4. Persona Variance Geometry
**File:** `persona_variance.mmd`
**Used in:** [S4_CROSS_PERSONA_THEOREMS.md](../S4_CROSS_PERSONA_THEOREMS.md)
**Purpose:** Distribution plot showing all PFI scores clustering around 0.88 with σ² = 0.000869

### 5. S4 Gate Decision Logic
**File:** `s4_gate_logic.mmd`
**Used in:** [S4_CROSS_PERSONA_THEOREMS.md](../S4_CROSS_PERSONA_THEOREMS.md)
**Purpose:** Flowchart showing three-condition gate leading to S4 formalization approval

## Format

All diagrams are provided in **Mermaid.js** format (`.mmd` files), which can be:

1. **Rendered directly** in GitHub, VS Code, and many markdown viewers
2. **Exported to PNG/SVG/PDF** using:
   - [Mermaid Live Editor](https://mermaid.live)
   - [Mermaid CLI](https://github.com/mermaid-js/mermaid-cli)
   - VS Code Mermaid extensions
3. **Embedded in presentations** (PowerPoint, Keynote, Google Slides)
4. **Included in LaTeX documents** via mermaid packages

## Rendering Instructions

### Online (Mermaid Live Editor)
1. Visit https://mermaid.live
2. Copy/paste contents of any `.mmd` file
3. Export as PNG (high-res), SVG (vector), or PDF

### Command Line (mermaid-cli)
```bash
# Install mermaid-cli
npm install -g @mermaid-js/mermaid-cli

# Export to PNG (high-res)
mmdc -i compression_pipeline.mmd -o compression_pipeline.png -w 2048 -H 1536

# Export to SVG (vector, scalable)
mmdc -i compression_pipeline.mmd -o compression_pipeline.svg

# Export to PDF
mmdc -i compression_pipeline.mmd -o compression_pipeline.pdf
```

### VS Code
1. Install "Markdown Preview Mermaid Support" extension
2. Open any `.mmd` file
3. Right-click in preview → Export diagram

## Publication Quality Settings

For **conference papers/presentations**, export at:
- **PNG:** 2048×1536px minimum (300 DPI)
- **SVG:** Vector format (infinite scaling)
- **PDF:** Vector format preferred

For **slides**, export at:
- **PNG:** 1920×1080px (Full HD)
- **SVG:** Recommended for crisp rendering at any size

## Color Scheme

Diagrams use a consistent color palette:
- **Blue** (#0288d1, #1565c0, #bbdefb): Input/neutral states
- **Yellow** (#f57f17, #fff9c4): Compression/transformation
- **Green** (#388e3c, #c8e6c9): Output/success states
- **Red** (#c62828, #ffcdd2): Warnings/thresholds
- **Purple** (#6a1b9a, #f3e5f5): Ideal/theoretical states

## Integration

These diagrams are referenced inline in the S4 framework documents using ASCII versions for universal compatibility. For formal presentations and publications, use the high-resolution exports from these source files.

---

**Version:** 1.0
**Date:** 2025-11-23
**Maintainer:** Repo Claude + Architect Nova
