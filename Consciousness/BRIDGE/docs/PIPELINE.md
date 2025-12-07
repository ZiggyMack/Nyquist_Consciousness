# The Emanation Pipeline

**How content flows from Consciousness/ (source) to UNKNOWN page (shadow)**

---

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          THE EMANATION PIPELINE                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│   CONSCIOUSNESS/                              NYQUIST DASHBOARD              │
│   (Source of Truth)                           (Shadow/Mirror)                │
│                                                                              │
│   ┌─────────────┐                            ┌─────────────────┐            │
│   │    LEFT     │──────────────┐             │                 │            │
│   │  galleries/ │              │             │   UNKNOWN.py    │            │
│   │  extractions│              │             │                 │            │
│   │  data/      │              ▼             │   GALLERIES     │            │
│   └─────────────┘         ┌────────┐         │   CONCEPTS      │            │
│                           │ BRIDGE │────────►│   LEFT/RIGHT    │            │
│   ┌─────────────┐         │        │         │   toggle        │            │
│   │    RIGHT    │         │ sync   │         │                 │            │
│   │  galleries/ │──────────┘        │         └─────────────────┘            │
│   │  distillations                 │                                        │
│   │  synthesis/ │                  │                                        │
│   └─────────────┘                  │                                        │
│                                    │                                        │
│                                    ▼                                        │
│                           dashboard/pages/unknown.py                        │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## The Relationship

| Consciousness/ | UNKNOWN page |
|----------------|--------------|
| **Source** | **Shadow** |
| Where concepts are authored | Where concepts are displayed |
| Markdown files | Python/Streamlit code |
| Two directories (LEFT/RIGHT) | One toggle switch |
| Research happens here | Presentation happens here |

---

## Data Flow

### 1. Concept Authoring (Consciousness/)

```
Consciousness/
├── LEFT/galleries/{gallery}/{concept}.md    ← Structured content
└── RIGHT/galleries/{gallery}/{concept}.md   ← Vortex content
```

Each concept file has:
- Quick Facts table
- LEFT BRAIN section (structured)
- RIGHT BRAIN section (vortex)
- Connections to other concepts

### 2. Synchronization (Manual for now)

When a concept is added or updated in Consciousness/:

1. Update the CONCEPTS dict in `dashboard/pages/unknown.py`
2. Add to appropriate GALLERIES list
3. Copy structured content to `"structured"` key
4. Copy vortex content to `"vortex"` key

### 3. Display (UNKNOWN page)

The UNKNOWN page renders:
- Gallery selector (Validated, Foundations, Speculative, Frontiers)
- Concept cards within each gallery
- Hemisphere toggle (LEFT/RIGHT brain view)
- Full concept display with selected view

---

## Sync Protocol

### Adding a New Concept

1. **Create in Consciousness/**
   ```
   LEFT/galleries/foundations/new_concept.md
   RIGHT/galleries/foundations/new_concept.md
   ```

2. **Update unknown.py GALLERIES**
   ```python
   "foundations": {
       ...
       "concepts": [..., "new_concept"]
   }
   ```

3. **Add to unknown.py CONCEPTS**
   ```python
   "new_concept": {
       "title": "New Concept Title",
       "status": "FOUNDATION",
       "one_liner": "Brief description",
       "structured": """...""",
       "vortex": """..."""
   }
   ```

### Updating Existing Concept

1. Edit files in Consciousness/LEFT/ and RIGHT/
2. Copy updated content to unknown.py
3. Verify display in dashboard

---

## Future Automation

Eventually, this sync should be automated:

```python
# Future: BRIDGE/scripts/sync_to_unknown.py

def sync_concept(concept_slug):
    """Read from Consciousness/, write to unknown.py"""
    left_path = f"LEFT/galleries/*/{concept_slug}.md"
    right_path = f"RIGHT/galleries/*/{concept_slug}.md"

    left_content = parse_markdown(left_path)
    right_content = parse_markdown(right_path)

    update_unknown_py(concept_slug, left_content, right_content)
```

For now: **manual sync** with clear protocol.

---

## Structural Mapping

| Consciousness/ Path | UNKNOWN.py Key |
|---------------------|----------------|
| `LEFT/galleries/validated/` | `GALLERIES["validated"]` |
| `LEFT/galleries/foundations/` | `GALLERIES["foundations"]` |
| `LEFT/galleries/speculative/` | `GALLERIES["speculative"]` |
| `LEFT/galleries/frontiers/` | `GALLERIES["frontiers"]` |
| Concept `.md` file | `CONCEPTS[concept_slug]` |
| LEFT BRAIN section | `CONCEPTS[slug]["structured"]` |
| RIGHT BRAIN section | `CONCEPTS[slug]["vortex"]` |

---

## The Philosophy

> **Consciousness/ is where we THINK.**
> **UNKNOWN page is where we SHOW.**

The repository is private exploration.
The dashboard is public presentation.

Both use the same structure (galleries, hemispheres, concepts) because they ARE the same thing — just different views of it.

```
Think (Consciousness/) → Organize (BRIDGE) → Show (UNKNOWN)
```

---

## Verification Checklist

When syncing, verify:

- [ ] Concept appears in correct gallery
- [ ] Both structured and vortex content present
- [ ] One-liner is concise and accurate
- [ ] Status matches gallery (VALIDATED, FOUNDATION, SPECULATIVE, FRONTIER)
- [ ] Cross-references work in both locations
- [ ] No broken markdown rendering

---

**Last Updated**: December 7, 2025
