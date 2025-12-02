# Matrix Page Specification
## Dimensional Transit Hub Theme

This document captures the design patterns and CSS techniques used in the Matrix page for replication across other dashboard pages.

---

## 1. Core Theme: Dimensional Transit Hub

The Matrix page is styled as a **sci-fi transit station** where projects and repos travel between dimensional portals. Key metaphors:
- **Platforms** = Connected repositories
- **Departures Board** = Project status listings
- **Looking Glass** = Central portal to Pan Handlers
- **Gates** = Section headers (GATE A, GATE B, etc.)

---

## 2. CSS Override Strategy

### The Problem
The main `app.py` has global light theme CSS with high specificity:
```css
.main .block-container, .main .block-container * {
    color: #1a1a1a !important;
}
```

### The Solution: Triple Specificity
All Matrix CSS uses **triple specificity selectors** to override:
```css
.stApp .main .block-container .your-class,
.main .block-container .your-class {
    /* your styles */
}
```

Always include both selectors for maximum compatibility.

---

## 3. Neon Sign Styles

### Available Badge Classes

| Class | Color | Use Case |
|-------|-------|----------|
| `.neon-live` | Magenta (#ff00ff) | External live deployments |
| `.neon-here` | Gold (#ffcc00) | Current location indicator |
| `.neon-active` | Blue (#00aaff) | Active/connected systems |
| `.neon-reflection` | Gold (#ffd700) | Mirror/partner systems |

### CSS for Neon Effect
```css
.neon-live {
    color: #ff00ff !important;
    padding: 0.3em 0.7em;
    font-size: 0.85em;  /* Increased for readability */
    border: 2px solid #ff00ff;
    text-shadow:
        0 0 5px #ff00ff,
        0 0 10px #ff00ff,
        0 0 20px #ff00ff;
    box-shadow:
        0 0 5px #ff00ff,
        0 0 10px rgba(255,0,255,0.5);
    animation: neonGlow 2s ease-in-out infinite, neonFlicker 4s linear infinite;
}
```

### Required Keyframes
```css
@keyframes neonGlow {
    0%, 100% { filter: brightness(1) drop-shadow(0 0 3px currentColor); }
    50% { filter: brightness(1.2) drop-shadow(0 0 8px currentColor) drop-shadow(0 0 15px currentColor); }
}

@keyframes neonFlicker {
    0%, 19.999%, 22%, 62.999%, 64%, 64.999%, 70%, 100% { opacity: 1; }
    20%, 21.999%, 63%, 63.999%, 65%, 69.999% { opacity: 0.4; }
}
```

---

## 4. Card Styles

### Platform Gate (Section containers)
```css
.platform-gate {
    background: linear-gradient(135deg, rgba(0,30,0,0.95) 0%, rgba(0,50,20,0.9) 100%);
    border: 2px solid #00ff41;
    border-radius: 15px;
    padding: 1.5em;
    position: relative;
    overflow: hidden;
    box-shadow:
        0 0 30px rgba(0,255,65,0.15),
        inset 0 0 50px rgba(0,255,65,0.05);
}
```

### Mirror Cards (Alice Through the Looking Glass)
Left and right cards that mirror each other around a central portal:

```css
/* Left mirror - normal orientation */
.mirror-left {
    border-left: 4px solid #00ffff;
    border-right: 1px solid rgba(0,255,65,0.3);
}

/* Right mirror - reflected/flipped */
.mirror-right {
    border-right: 4px solid #00ffff;
    border-left: 1px solid rgba(0,255,65,0.3);
    text-align: right;
}

.mirror-right .feature-grid {
    justify-content: flex-end;
}
```

### Portal Chamber (Central animated portal)
```css
.portal-chamber {
    background: linear-gradient(135deg, rgba(0,20,0,0.95) 0%, rgba(0,40,0,0.9) 50%, rgba(0,20,0,0.95) 100%);
    border: 2px solid #00ff41;
    border-radius: 20px;
    padding: 1.5em;
    box-shadow: 0 0 40px rgba(0,255,65,0.2), inset 0 0 60px rgba(0,255,65,0.05);
}
```

---

## 5. Portal Animation

### Spinning Portal Ring
```css
.portal-ring {
    width: 100px;
    height: 100px;
    border-radius: 50%;
    border: 3px solid #00ff41;
    animation: portalPulse 3s ease-in-out infinite;
    background: radial-gradient(circle, rgba(0,255,65,0.1) 0%, transparent 70%);
}

.portal-ring::before {
    content: '';
    position: absolute;
    width: 120%;
    height: 120%;
    border: 2px dashed rgba(0,255,65,0.3);
    border-radius: 50%;
    animation: portalSpin 8s linear infinite;
}

@keyframes portalSpin {
    0% { transform: rotate(0deg); }
    100% { transform: rotate(360deg); }
}

@keyframes portalPulse {
    0%, 100% {
        box-shadow: 0 0 30px rgba(0,255,65,0.4);
        transform: scale(1);
    }
    50% {
        box-shadow: 0 0 60px rgba(0,255,65,0.8), 0 0 100px rgba(0,255,65,0.4);
        transform: scale(1.02);
    }
}
```

---

## 6. Departure Board Style

Train station-style status display:

```css
.departure-board {
    background: linear-gradient(180deg, #0a0a0a 0%, #151515 100%);
    border: 3px solid #333;
    border-radius: 10px;
    font-family: 'Courier New', monospace;
    box-shadow: inset 0 0 20px rgba(0,0,0,0.8);
}

.departure-row {
    display: flex;
    align-items: center;
    padding: 0.8em;
    border-bottom: 1px solid #222;
}

.departure-dest {
    flex: 2;
    color: #ffaa00 !important;  /* Amber like train displays */
    font-weight: bold;
    text-shadow: 0 0 10px rgba(255,170,0,0.5);
}

.departure-platform {
    color: #00ff41 !important;
    font-size: 1.2em;
    font-weight: bold;
}
```

---

## 7. Tunnel Card (Header element)

Creates a perspective tunnel effect:

```css
.tunnel-card {
    background: radial-gradient(ellipse at center,
        rgba(0,50,20,0.9) 0%,
        rgba(0,20,10,0.95) 60%,
        rgba(0,10,5,1) 100%);
    border: 3px solid #00ff41;
    border-radius: 50% / 10%;
    padding: 2em;
    text-align: center;
    box-shadow:
        0 0 40px rgba(0,255,65,0.3),
        inset 0 0 80px rgba(0,255,65,0.1),
        inset 0 0 120px rgba(0,0,0,0.5);
    animation: tunnelPerspective 6s ease-in-out infinite;
}

@keyframes tunnelPerspective {
    0%, 100% { transform: perspective(500px) rotateX(2deg); }
    50% { transform: perspective(500px) rotateX(-1deg); }
}
```

---

## 8. Feature Tags

Small pill-shaped tags for listing features:

```css
.feature-tag {
    background: rgba(0,255,65,0.1);
    border: 1px solid rgba(0,255,65,0.3);
    border-radius: 15px;
    padding: 0.3em 0.7em;
    font-size: 0.75em;
    color: #00ff41 !important;
    font-family: 'Courier New', monospace;
    white-space: nowrap;
}

.feature-grid {
    display: flex;
    flex-wrap: wrap;
    gap: 0.4em;
}
```

---

## 9. Section Headers with Gate IDs

```html
<div class="platform-gate">
    <div class="platform-header">
        <h2 style="margin: 0;">📡 SECTION TITLE</h2>
        <span class="platform-id">GATE A</span>
    </div>
</div>
```

```css
.platform-header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding-bottom: 1em;
    border-bottom: 1px solid rgba(0,255,65,0.3);
}

.platform-id {
    font-family: 'Courier New', monospace;
    font-size: 0.8em;
    color: #00cc33 !important;
    background: rgba(0,255,65,0.1);
    padding: 0.3em 0.8em;
    border-radius: 4px;
    border: 1px solid rgba(0,255,65,0.3);
}
```

---

## 10. Color Palette

| Color | Hex | Use |
|-------|-----|-----|
| Matrix Green | #00ff41 | Primary text, borders, glows |
| Darker Green | #00cc33 | Secondary text |
| Black | #0a0a0a | Backgrounds |
| Magenta | #ff00ff | LIVE badges, portal borders |
| Cyan | #00ffff | Mirror borders, holographic effects |
| Gold | #ffcc00 | YOU ARE HERE, destination names |
| Blue | #00aaff | ACTIVE badges |
| Amber | #ffaa00 | Departure board destinations |

## 10.1 Recommended Icons

| Icon | Emoji | Use |
|------|-------|-----|
| Nyquist Consciousness | 📡 | Satellite dish - signals/frequency theme |
| Pan Handler Central | 🏛️ | Classical building - federation hub |
| Portal | 🌀 | Spiral - dimensional gateway |
| Current Location | 📍 | Pin marker |
| CFA Framework | ⚙️ | Gear - framework/engineering |

---

## 11. Implementation Checklist

To apply this theme to another page:

1. [ ] Add the CSS block at the start of `render()` function
2. [ ] Use `.stApp .main .block-container` prefix for all selectors
3. [ ] Include required `@keyframes` animations
4. [ ] Wrap content in `.platform-gate` containers for sections
5. [ ] Use neon badge classes for status indicators
6. [ ] Apply `!important` to color properties to override app.py
7. [ ] Test on both light and dark system themes

---

## 12. Page Structure

```
┌─────────────────────────────────────────┐
│  TUNNEL CARD (Page Header)              │
│  "DIMENSIONAL TRANSIT HUB"              │
├─────────────────────────────────────────┤
│  PHILOSOPHY QUOTE                       │
├─────────────────────────────────────────┤
│  PLATFORM GATE: Connected Platforms     │
│  ┌─────────┬─────────┬─────────┐       │
│  │ MIRROR  │ PORTAL  │ MIRROR  │       │
│  │  LEFT   │ CENTER  │  RIGHT  │       │
│  │(Nyquist)│(Looking)│  (CFA)  │       │
│  │         │ Glass)  │         │       │
│  └─────────┴─────────┴─────────┘       │
├─────────────────────────────────────────┤
│  PLATFORM GATE: Departures              │
│  ┌─────────────────────────────────┐   │
│  │  DEPARTURE BOARD                │   │
│  │  - Project 1     BOARDING    1  │   │
│  │  - Project 2     SCHEDULED   2  │   │
│  └─────────────────────────────────┘   │
├─────────────────────────────────────────┤
│  EXPANDER: Project Details              │
├─────────────────────────────────────────┤
│  PLATFORM GATE: Station Metrics         │
│  [Metric] [Metric] [Metric] [Metric]    │
├─────────────────────────────────────────┤
│  FOOTER                                 │
└─────────────────────────────────────────┘
```

---

*Last updated: Session implementing transit hub theme*
