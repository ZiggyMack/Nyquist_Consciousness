# Dashboard Refactoring — Distributed Architecture

## Overview

The dashboard has been refactored from a monolithic `app.py` into a **distributed, modular architecture** where each page is a separate module. This allows independent development and faster iteration.

## New Structure

```
dashboard/
├── app_new.py              # Main routing controller (NEW)
├── app.py                  # Old monolithic version (BACKUP)
├── config.py               # Configuration and paths
├── utils.py                # Shared utilities (NEW)
├── pages/                  # Page modules (NEW)
│   ├── __init__.py
│   ├── overview.py         # Overview / Mission Control page
│   ├── personas.py         # (TODO) Personas Matrix page
│   ├── stack.py            # (TODO) S# Stack Layers page
│   ├── s7_viz.py           # (TODO) S7 Armada Visualizations
│   ├── metrics.py          # (TODO) Metrics & Comparisons
│   ├── omega.py            # (TODO) Omega & Temporal
│   ├── avlar.py            # (TODO) Cross-Modal / AVLAR
│   ├── roadmap.py          # (TODO) Roadmap page
│   ├── glossary.py         # (TODO) Glossary page
│   ├── publications.py     # (TODO) Publications page
│   └── matrix.py           # (TODO) The Matrix portal page
```

## How It Works

### 1. Main App (`app_new.py`)

The main app is now a **routing controller** that:
- Handles sidebar navigation
- Manages CSS styling
- Routes to page modules dynamically
- Passes shared state/config to pages

### 2. Page Modules (`pages/*.py`)

Each page module:
- Has a single `render()` function as entry point
- Imports only what it needs from `utils` and `config`
- Can be developed and tested independently
- Updates automatically when modified (Streamlit hot reload)

Example structure:
```python
# pages/overview.py
import streamlit as st
from utils import load_status, page_divider
from config import PATHS

def render():
    """Render the Overview page."""
    status = load_status()
    st.title("📜 Overview")
    # ... page content

if __name__ == "__main__":
    render()  # Can test page standalone
```

### 3. Shared Utilities (`utils.py`)

Common functions used across pages:
- `load_status()` - Load NYQUIST_STATUS.json
- `load_personas()` - Load persona markdown files
- `load_publication_status()` - Load publication tracking
- `page_divider()` - Visual separator
- `ledger_card()` - Styled card component

### 4. Configuration (`config.py`)

Centralized configuration:
- All file paths in `PATHS` dict
- Dashboard settings in `SETTINGS` dict
- Color palette for consistency

## Benefits

✅ **Modularity**: Each page is self-contained
✅ **Independent Development**: Work on one page without touching others
✅ **Faster Iteration**: Streamlit hot-reloads individual modules
✅ **Better Organization**: Clear separation of concerns
✅ **Easier Testing**: Test pages in isolation
✅ **Team Collaboration**: Multiple devs can work on different pages

## Migration Path

### Current Status

- ✅ `utils.py` created with shared functions
- ✅ `pages/overview.py` extracted and working
- ⏳ Remaining pages to be extracted from old `app.py`

### To Complete Migration

1. Extract each page function from `app.py` into `pages/<name>.py`
2. Add page module to `PAGE_MODULES` dict in `app_new.py`
3. Test page independently
4. Once all pages extracted, rename `app_new.py` → `app.py`

### Example: Extracting Personas Page

```bash
# 1. Create pages/personas.py
# 2. Copy page_personas() function from old app.py
# 3. Rename to render() and add imports
# 4. Add to app_new.py:

from pages import personas

PAGE_MODULES = {
    "Overview": overview,
    "Personas": personas,  # <-- Add here
}
```

## Running the New Architecture

```bash
# Test with new architecture
cd dashboard
streamlit run app_new.py

# Once migration complete, replace old app
mv app.py app_old_backup.py
mv app_new.py app.py
streamlit run app.py
```

## Next Steps

1. Extract Personas page to `pages/personas.py`
2. Extract Stack Layers page to `pages/stack.py`
3. Extract S7 Armada Viz to `pages/s7_viz.py`
4. Extract remaining pages
5. Delete old `app.py` once all pages migrated
6. Celebrate modular architecture! 🎉

---

**Last Updated**: 2025-11-27
**Architecture**: Distributed Modular Pages
**Status**: Phase 1 Complete (Overview page extracted)
