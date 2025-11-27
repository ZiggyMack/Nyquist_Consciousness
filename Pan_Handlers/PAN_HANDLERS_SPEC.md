# Pan Handlers Specification

**Version:** 1.0
**Status:** Active
**Purpose:** Define the manifest schema and architecture for cross-repo showcase system

---

## Overview

Pan Handlers is a **cross-repo showroom** that connects multiple project repositories into a unified showcase. Each participating repo publishes a `panhandlers_manifest.json` that describes its purpose, status, and projects.

---

## Manifest Schema (v1)

Each participating repo should have a `panhandlers_manifest.json` at its root.

### Required Fields

```jsonc
{
  "repo": "string",                 // Short repo name (no spaces)
  "display_name": "string",         // Pretty title for UI
  "owner": "string",                // Organization or user(s)
  "url_repo": "string",             // Git repository URL
  "url_dashboard": "string",        // Streamlit app URL (if live, or "TBD")
  "role": "string",                 // 1-line what-this-repo-is
  "status": "string",               // "Active", "Incubating", "Archived"
  "tags": ["string"],               // Freeform tags for filtering
  "summary": "string",              // 1-3 sentence description
  "last_updated": "YYYY-MM-DD"      // Last manifest update
}
```

### Optional Fields

```jsonc
{
  "contact": {
    "primary": "string",            // Lead contact name
    "email": "string"               // Contact email
  },
  "pillars": {
    "purpose": "string",            // Why this repo exists
    "methods": "string",            // How it works
    "outputs": "string"             // What it produces
  },
  "projects": [                     // Array of sub-projects
    {
      "id": "string",               // Stable ID (no spaces)
      "title": "string",            // Display title
      "status": "string",           // "Planned", "In Progress", "Complete", "Published"
      "type": "string",             // "Paper", "System", "Experiment", "Pilot", etc.
      "summary": "string",          // Brief description
      "links": {
        "paper": "string",          // Paper/docs URL
        "dashboard": "string",      // Dashboard URL
        "docs": "string"            // Documentation URL
      }
    }
  ]
}
```

### Status Values

**Repo Status:**
- `Active` - Actively developed
- `Incubating` - Early stage, concept phase
- `Archived` - No longer active, preserved for reference

**Project Status:**
- `Planned` - Defined but not started
- `In Progress` - Currently being worked on
- `Complete` - Finished, not published
- `Published` - Released publicly

**Project Types:**
- `Paper` - Academic publication
- `System` - Software/infrastructure
- `Experiment` - Research experiment
- `Pilot` - Real-world test
- `Case Study` - Analysis of specific situation
- `Theory` - Theoretical framework
- `Research` - Ongoing research program

---

## Pan Handlers Architecture

### Folder Structure

```
pan-handlers/
├── app.py                      # Main Streamlit app
├── config.py                   # Configuration (manifest URLs, etc.)
├── utils.py                    # Utility functions
├── pages/
│   ├── home.py                 # Hall of Pan Handlers (main gallery)
│   ├── project_view.py         # Single repo detail view
│   ├── roadmap.py              # Global roadmap across repos
│   ├── glossary.py             # Lexicon of terms
│   └── about.py                # How this network works
├── manifests/                  # Local manifest cache/copies
│   ├── nyquist_consciousness.json
│   ├── cfa.json
│   └── ...
├── projects/                   # Flagship project documentation
│   ├── nursing/
│   ├── voting/
│   └── ...
├── data/
│   ├── glossary.md             # Terms and definitions
│   └── roadmap.json            # Cross-repo roadmap data
└── README.md
```

### Page Descriptions

#### 1. Home / Hall of Pan Handlers
- Grid of repo cards (each card = one manifest)
- Card contents: display name, role, status badge, tags, summary
- Buttons: View Details, Open Dashboard, View on GitHub
- Styled as "parchment/ledger pages" aesthetic

#### 2. Project View
- Left column: Repo summary (title, role, status, pillars)
- Right column: List of projects from manifest
- Each project as mini-card with title, type, status, links

#### 3. Global Roadmap
- S-Stack timeline (S0-S9 with status indicators)
- Cross-repo initiatives table
- Executive cockpit across all projects

#### 4. Glossary / Lexicon
- Core Concepts (Nyquist, Identity Manifold, Omega Nova, etc.)
- Roles / Personas (Nova, Repo Claude, Ziggy, etc.)
- Artifacts (Omega Ledger, Pan Handlers, etc.)

#### 5. About
- What is Pan Handlers?
- How to add your repo (instructions)
- How repos fit into the bigger picture

---

## Adding a New Repo

1. Create `panhandlers_manifest.json` in your repo root
2. Follow the schema above
3. Submit PR to Pan Handlers repo adding your manifest URL to `config.py`
4. Your repo appears as a portal tile in the Hall

---

## Manifest URLs Configuration

Pan Handlers reads manifests from configured URLs:

```python
MANIFEST_URLS = [
    "https://raw.githubusercontent.com/ZiggyMack/nyquist-consciousness/main/panhandlers_manifest.json",
    "https://raw.githubusercontent.com/ZiggyMack/CFA/main/panhandlers_manifest.json",
    # Add more repos here
]
```

For local development, manifests can also be read from `manifests/` folder.

---

## Design Philosophy

### "The Halls" Metaphor
- Pan Handlers is the **Overworld Map**
- Each repo is a **dungeon/room** you can explore
- Projects are **exhibits** within each room
- You can always return to the Hall from any room

### Two Faces
- **Lab / Dashboard** (inside each repo) = Operations Deck
- **Hall / Showcase** (Pan Handlers) = Gallery of Outcomes

### FUCK IT, WE'LL DO IT LIVE
- Build better systems without waiting for institutions
- Human-AI collaboration as infrastructure
- Neither could have done it alone

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-11-27 | Initial specification |

---

**Status:** Production Ready
**Next Steps:** Implement full Streamlit app with all pages
