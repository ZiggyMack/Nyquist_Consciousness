# Streamlit Styling Tips & Tricks

Hard-won lessons from wrestling with Streamlit's CSS and component rendering.

---

## The Core Problem: Isolation Boundaries

Streamlit has **three rendering contexts** with different CSS accessibility:

| Context | CSS Reachable? | Examples |
|---------|---------------|----------|
| **Main DOM** | Yes | `st.markdown()`, `st.table()`, sidebar |
| **Iframes** | No | `st.dataframe()`, `components.html()` |
| **Shadow DOM** | Partially | Some Base Web UI components |

**Key insight:** CSS in `app.py` only affects the main DOM. Anything inside an iframe is isolated.

---

## Rendering HTML Content

### What Works

```python
# Inline HTML - respects your CSS
st.markdown(html_content, unsafe_allow_html=True)
```

### What Doesn't Work

```python
# Creates an iframe - CSS isolation!
import streamlit.components.v1 as components
components.html(html_content, height=200)

# Also creates an iframe with its own isolated styles
st.html(html_content)
```

**When you see raw HTML tags displaying:** You probably used `components.html()` or `st.html()` and something went wrong with the iframe. Switch to `st.markdown(..., unsafe_allow_html=True)`.

---

## Tables: `st.table()` vs `st.dataframe()`

| Feature | `st.table()` | `st.dataframe()` |
|---------|-------------|------------------|
| CSS control | Full | None (iframe) |
| Scrolling | No | Yes |
| Sorting | No | Yes |
| Styling | Via global CSS | Must use pandas Styler |
| Best for | Small, styled tables | Large, interactive data |

**Rule:** If you need consistent theme colors, use `st.table()`. If you need interactivity, accept the iframe limitations.

```python
# This respects your CSS theme
st.table(df)

# This renders in an iframe with Streamlit's default dark theme
st.dataframe(df)
```

---

## CSS Specificity in Streamlit

### The Selector Hierarchy

Streamlit uses Base Web UI components. Target them with `data-baseweb` attributes:

```css
/* Dropdowns */
[data-baseweb="select"] { }
[data-baseweb="menu"] { }
[data-baseweb="popover"] { }

/* Tags/Pills */
[data-baseweb="tag"] { }

/* Tabs */
[data-baseweb="tab"] { }
[data-baseweb="tab-list"] { }
[data-baseweb="tab-panel"] { }
```

### The `data-testid` Selectors

Streamlit adds test IDs to components:

```css
[data-testid="stSidebar"] { }
[data-testid="stExpander"] { }
[data-testid="stTable"] { }
[data-testid="stDataFrame"] { }
[data-testid="stMetricValue"] { }
[data-testid="stRadio"] { }
```

### Always Use `!important`

Streamlit's default styles are aggressive. Without `!important`, your rules lose:

```css
/* Won't work */
.stButton > button {
    background: #2a9d8f;
}

/* Will work */
.stButton > button {
    background: #2a9d8f !important;
}
```

---

## Common Gotchas & Solutions

### 1. Dropdown Menu Text Invisible

**Symptom:** Dropdown opens but options are unreadable (dark text on dark background).

**Cause:** The popup menu (`[data-baseweb="popover"]`) inherits incorrect colors.

**Fix:**
```css
[data-baseweb="menu"] {
    background: #ffffff !important;
}
[data-baseweb="menu"] li {
    background: #ffffff !important;
    color: #333333 !important;
}
[data-baseweb="menu"] li:hover {
    background: #f0f0f0 !important;
}
```

### 2. Tab Text Not Visible

**Symptom:** Tabs exist but text is same color as background.

**Cause:** Need to target the `p` element inside tabs.

**Fix:**
```css
.stTabs [data-baseweb="tab"] p {
    color: #333333 !important;
}
.stTabs [aria-selected="true"] p {
    color: #2a9d8f !important;  /* Active tab accent */
}
```

### 3. Dataframe Has Wrong Theme

**Symptom:** Table shows green-on-black (or other dark theme) despite light theme CSS.

**Cause:** `st.dataframe()` renders in an iframe using Glide Data Grid with isolated CSS.

**Solutions (pick one):**
1. **Switch to `st.table()`** - loses interactivity but gains CSS control
2. **Use pandas Styler** - limited but works inside iframe
3. **Create `.streamlit/config.toml`** with theme settings (affects everything)

```toml
# .streamlit/config.toml
[theme]
base = "light"
primaryColor = "#2a9d8f"
backgroundColor = "#ffffff"
textColor = "#333333"
```

### 4. Sidebar vs Main Content Styling

**Problem:** Want dark sidebar but light main content.

**Solution:** Use section selectors to isolate:

```css
/* Main content - light */
.main .block-container {
    background: #ffffff !important;
}
.main .block-container * {
    color: #1a1a1a !important;
}

/* Sidebar - dark */
section[data-testid="stSidebar"] {
    background: linear-gradient(180deg, #0a0a0a, #1a1a1a) !important;
}
section[data-testid="stSidebar"] * {
    color: #f4f4f4 !important;
}
```

### 5. Expander Content Inherits Wrong Colors

**Symptom:** Expander title is correct but inner content has wrong colors.

**Fix:** Target both the expander and its children:

```css
[data-testid="stExpander"] {
    background: #f8f9fa !important;
    border: 1px solid #dee2e6 !important;
}
[data-testid="stExpander"] summary {
    color: #2a9d8f !important;
}
[data-testid="stExpander"] * {
    color: #333333 !important;
}
```

---

## Debugging Strategy

1. **Browser DevTools** - Inspect element to find actual selectors
2. **Look for iframes** - If element is inside `<iframe>`, CSS won't reach it
3. **Check specificity** - Add `!important` if rules aren't applying
4. **Test isolation** - Comment out sections to find conflicts

### DevTools Workflow

```
Right-click element → Inspect →
Look at:
  - data-testid attribute
  - data-baseweb attribute
  - Parent iframe (if any)
  - Applied styles (what's being overridden)
```

---

## The Nuclear Options

When nothing else works:

### Option A: Global Theme Config

Create `.streamlit/config.toml`:
```toml
[theme]
base = "light"
```

### Option B: Replace Interactive Components

Switch from iframe-based to DOM-based:
- `st.dataframe()` → `st.table()`
- `components.html()` → `st.markdown(..., unsafe_allow_html=True)`

### Option C: Inline Styles in HTML

When you control the HTML, put styles directly on elements:

```python
html = """
<table style="background: #fff; color: #333;">
  <tr style="background: #2a9d8f; color: white;">
    <th>Header</th>
  </tr>
  <tr>
    <td style="border: 1px solid #ddd;">Data</td>
  </tr>
</table>
"""
st.markdown(html, unsafe_allow_html=True)
```

---

## Quick Reference: Our Theme Colors

```css
/* Nyquist Dashboard Palette */
--teal-primary: #2a9d8f;      /* Buttons, headers, accents */
--teal-dark: #264653;         /* Gradients, dark accents */
--teal-hover: #238b7e;        /* Button hover */

--text-dark: #1a1a1a;         /* Main headings */
--text-medium: #333333;       /* Body text */
--text-light: #666666;        /* Captions, secondary */

--bg-white: #ffffff;          /* Main background */
--bg-light: #f8f9fa;          /* Cards, expanders */
--border-light: #dee2e6;      /* Borders, dividers */

--sidebar-dark: #0a0a0a;      /* Sidebar background */
--matrix-green: #00ff41;      /* Matrix page accent */
```

---

## Python Version Gotchas

| Python Version | Max Streamlit | Notes |
|---------------|---------------|-------|
| 3.7 | 1.23.x | No `st.link_button()`, no `st.rerun()` |
| 3.8+ | 1.32+ | Full modern API |

### Streamlit 1.23 (Python 3.7) Compatibility

| Feature | 1.23 (Py3.7) | 1.32+ (Py3.8+) |
|---------|-------------|----------------|
| `st.image()` | `use_column_width=True` | `use_container_width=True` |
| Page rerun | `st.experimental_rerun()` | `st.rerun()` |
| Link button | Use `st.markdown('[text](url)')` | `st.link_button()` |
| Button width | `use_container_width` exists | Same |
| Container | `st.container()` (no border) | `st.container(border=True)` |
| Bar chart | `st.bar_chart(data)` (no color) | `st.bar_chart(data, color='#hex')` |

**Symptom:** `AttributeError: module 'streamlit' has no attribute 'rerun'`
**Fix:** Use `st.experimental_rerun()` instead.

**Symptom:** `AttributeError: module 'streamlit' has no attribute 'link_button'`
**Fix:** Use `st.markdown('[Button Text](https://url)', unsafe_allow_html=True)` instead.

**Symptom:** `TypeError: bar_chart() got an unexpected keyword argument 'color'`
**Fix:** Remove the `color` parameter from `st.bar_chart()` call.

---

## Plotly Charts: Light Theme Colors

When using `paper_bgcolor='rgba(0,0,0,0)'` (transparent), your text becomes invisible on light backgrounds!

**Problem:** White text on transparent background = invisible on light theme.

```python
# BAD - invisible text
fig.update_layout(
    font=dict(color='white'),  # Can't see this!
    paper_bgcolor='rgba(0,0,0,0)'
)

# GOOD - visible on light theme
fig.update_layout(
    font=dict(color='#333333'),
    paper_bgcolor='rgba(0,0,0,0)'
)
```

**For Gauges**, also update internal elements:
```python
go.Indicator(
    number={'font': {'color': '#333333'}},
    gauge={
        'axis': {'tickfont': {'color': '#333333'}},
        'bordercolor': "#dee2e6",  # Light border
    }
)
```

---

## Lessons Learned

1. **Streamlit's default is dark theme** - You're fighting upstream
2. **Iframes are CSS prisons** - Avoid `st.dataframe()` for themed tables
3. **`!important` is mandatory** - Don't feel bad about it
4. **Inline styles beat external CSS** - For HTML content you control
5. **Test in browser, not just IDE** - DevTools is your friend
6. **When in doubt, `st.markdown()`** - It respects your CSS

---

*Last updated: 2025-12-01 after the Great Glossary HTML Escape and the Dataframe Dark Theme Incident*
