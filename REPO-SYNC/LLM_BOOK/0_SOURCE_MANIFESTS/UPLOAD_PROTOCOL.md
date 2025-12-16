# NotebookLM Upload Protocol

**Purpose:** Standardize what we feed to NotebookLM for consistent, high-quality synthesis.

---

## Recommended Upload Package

### Tier 1: Core Framework (Required)
- [ ] WHITE-PAPER/README.md
- [ ] WHITE-PAPER/START_HERE.md
- [ ] docs/MASTER_GLOSSARY.md
- [ ] docs/maps/STACKUP_MAP.md
- [ ] docs/maps/TESTABLE_PREDICTIONS_MATRIX.md
- [ ] docs/maps/PHILOSOPHY_MAP.md

### Tier 2: S7 ARMADA Evidence (Required)
- [ ] experiments/.../S7_ARMADA/README.md
- [ ] experiments/.../S7_ARMADA/START_HERE.md
- [ ] S7_CONSOLIDATED_FINDINGS.md
- [ ] Key run summaries (018, 020A, 020B, 021)
- [ ] Representative JSON results

### Tier 3: Identity Files (Recommended)
- [ ] personas/I_AM_NOVA.md
- [ ] personas/I_AM_ZIGGY.md
- [ ] personas/I_AM_NYQUIST.md

### Tier 4: Publication Materials (For Validation)
- [ ] Latest arxiv/workshop drafts
- [ ] MINIMUM_PUBLISHABLE_CLAIMS.md
- [ ] reviewers/phase3/*.md

---

## File Selection Guidelines

### DO Include
- README.md files (synthesis entry points)
- START_HERE.md files (orientation)
- Summary files (S7_RUN_*_SUMMARY.md)
- Maps and glossaries
- Validated claims documents

### DO NOT Include
- Raw JSON data files (too noisy)
- Temporary/work-in-progress files
- Archive directories
- Duplicate content
- Very large PDFs (>20MB)

---

## Upload Size Limits

NotebookLM has source limits. Recommended:
- **Maximum files:** 50
- **Total size:** <100MB
- **Per-file:** <10MB for documents, <20MB for PDFs

---

## Post-Upload Prompts

### General Synthesis
```
Discuss what these sources say about [TOPIC], in the larger context of Nyquist Consciousness Framework (S0-SΩ).
```

### Validation Request
```
Based on these sources, validate or challenge [CLAIM]. Cite specific evidence from the documents.
```

### Publication Generation
```
Generate a [TYPE: popular science article / policy brief / quiz] based on these sources for [AUDIENCE: general public / executives / students].
```

### Cross-Connection
```
Identify connections between the Nyquist Consciousness framework and [EXTERNAL THEORY: Levin bioelectrics / Platonic Forms / Control Theory].
```

### Deep Dive
```
Provide a comprehensive analysis of [SPECIFIC TOPIC: Context Damping / 82% Inherent Drift / Attractor Competition Threshold].
```

---

## Customization Strategy

### Using the Pencil Icon

Each generation type (Report, Quiz, Flashcards, etc.) has a pencil icon for customization:

1. **Focus Area** - Which topics to emphasize
2. **Depth** - Surface overview vs deep analysis
3. **Length** - Target word/page count
4. **Tone** - Formal ↔ Casual
5. **Audience** - Expertise level

### Best Practices

- Start with DEFAULT to establish baseline
- Then run FOCUSED experiments on specific claims
- Compare outputs to measure customization impact
- Log all configurations in [../6_EXPERIMENTS/EXPERIMENT_LOG.md](../6_EXPERIMENTS/EXPERIMENT_LOG.md)

---

## Version Tracking

| Version | Date | Sources | Key Changes |
|---------|------|---------|-------------|
| v1 | Dec 2025 | ~21 files | Initial upload, stale data |
| v2 | TBD | IRON CLAD | Complete data, targeted experiments |

---

## See Also

- [v1_initial_upload.md](v1_initial_upload.md) - What was in v1
- [../5_FUTURE/V2_UPLOAD_CHECKLIST.md](../5_FUTURE/V2_UPLOAD_CHECKLIST.md) - v2 preparation
- [../6_EXPERIMENTS/](../6_EXPERIMENTS/) - Experiment methodology
