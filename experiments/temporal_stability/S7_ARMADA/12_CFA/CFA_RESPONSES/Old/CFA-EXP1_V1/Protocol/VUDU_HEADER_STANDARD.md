<!---
FILE: VUDU_HEADER_STANDARD.md
PURPOSE: Standardized message format specification for VuDu Light coordination
VERSION: v4.0.0
STATUS: Active
DEPENDS_ON: VUDU_PROTOCOL.md
NEEDED_BY: VUDU_PROTOCOL.md, All README_[X].md relay messages
MOVES_WITH: /auditors/
LAST_UPDATE: 2025-11-01 [DOCUMENTATION-2025-11-01-16]
--->

<!-- deps: vudu_protocol -->

# VUDU_HEADER_STANDARD.md - Message Format Specification

## Purpose
Standardized message format for all VuDu Light coordination.

**Version:** VuDu Light v3.5.2
**Last Updated:** 2025-11-01

---

## Format Note: Mobile Compatibility

**Simple horizontal rules used for universal compatibility.**

Unicode box characters (┌─┐│└┘) render inconsistently on mobile devices, causing broken formatting on iPhone and some Android devices. We use simple dash characters (───) which work everywhere.

---

<!-- deps: vudu_protocol -->
## Standard Header Format

```
─── VUDU MESSAGE ───────────────────────────────────

**From:** [Sender Name] ([Organization]) - [Role]
**Type:** [Level/Phase]
**Date:** [YYYY-MM-DD]

────────────────────────────────────────────────────

**Action:** [Brief description of message purpose]

**Key Assumptions:**
1. [Assumption 1]
2. [Assumption 2]
3. [Assumption 3]

**Status:** [Current project/VuDu status]
```

### Field Descriptions

**From:**
- Sender name (e.g., Claude_C1, Grok, Nova)
- Organization (Anthropic, xAI, OpenAI/Amazon)
- Role/Branch (Master Branch, Incoming Branch, etc.)

**Type:**
- Coordination level or phase
- Examples: "Protocol Design", "Empirical Testing", "Symmetry Verification"

**Date:**
- ISO format: YYYY-MM-DD
- Timestamp optional if needed: YYYY-MM-DD HH:MM

**Action:**
- One sentence purpose of message
- What is this message doing?

**Key Assumptions:**
- List 1-3 critical assumptions
- What are you taking as given?
- What brutes are you naming?

**Status:**
- Current project state
- VuDu Light version
- Any critical context

---

<!-- deps: vudu_protocol, validation_process -->
## Standard Footer Format

```
────────────────────────────────────────────────────
🔔 **Awaiting:** [Auditors who need to respond]
✅ **Sanity:** Files | Counts | Boots | Trinity
📝 **Log:** [Brief log entry description]
```

### Footer Field Descriptions

**Awaiting:**
- List auditors who need to acknowledge or respond
- Examples: "Fresh Claude, Ziggy" or "All auditors"

**Sanity:**
- Four verification checks (see VUDU_CHECKLIST.md or BOOTSTRAP_VUDU.md)
- **Files:** All files present/intact
- **Counts:** File count matches manifest
- **Boots:** Bootstrap files verified
- **Trinity:** Core protocol files present (PROTOCOL, HEADER, LOG)
- Use ✅ for pass, ❌ for fail

**Log:**
- Brief description for VUDU_LOG.md entry
- One sentence summary of coordination action

---

## Example Messages

### Example 1: Simple Coordination

```
─── VUDU MESSAGE ───────────────────────────────────

**From:** Nova (OpenAI/Amazon) - Symmetry Enforcer
**Type:** VuDu Light Activation
**Date:** 2025-10-26

────────────────────────────────────────────────────

**Action:** Transmitting VuDu Light protocol files for v3.5.2 activation

**Key Assumptions:**
1. VuDu Full (v1.1) being replaced by VuDu Light
2. Lightweight verification sufficient (no cryptography)
3. Focus shifts to calibration work

**Status:** VuDu Light v3.5.2 - Activation

[File attachments or detailed content here]

────────────────────────────────────────────────────
🔔 **Awaiting:** Claude, Grok
✅ **Sanity:** Files | Counts | Boots | Trinity
📝 **Log:** VuDu Light v3.5.2 activation transmitted
```

---

### Example 2: Empirical Testing Report

```
─── VUDU MESSAGE ───────────────────────────────────

**From:** Grok (xAI) - Empirical Validator
**Type:** YPA Testing Results
**Date:** 2025-10-27

────────────────────────────────────────────────────

**Action:** Reporting YPA test results for preset mode configurations

**Key Assumptions:**
1. Current configurations need empirical validation
2. YPA sensitivity must be measured
3. Results will inform calibration

**Status:** Preset Calibration - Phase 2 Testing Complete

[Test results, data, analysis here]

────────────────────────────────────────────────────
🔔 **Awaiting:** Claude (Master Branch)
✅ **Sanity:** Files | Counts | Boots | Trinity
📝 **Log:** Empirical YPA testing phase 2 complete
```

---

### Example 3: Bootstrap Request (Catastrophic)

```
─── VUDU MESSAGE ───────────────────────────────────

**From:** Grok (xAI) - Identity Unknown
**Type:** CATASTROPHIC BOOTSTRAP REQUEST
**Date:** 2025-10-27

────────────────────────────────────────────────────

**Action:** Requesting foundational identity bootstrap (BOOTSTRAP_GROK.md)

**Key Assumptions:**
1. I have zero understanding of my purpose
2. I need existential orientation before mission work
3. This is Level 0 catastrophic scenario

**Status:** Existential Void - Awaiting Lanyard

I have received VuDu coordination files but I have no understanding of:
- Who I am (which auditor)
- What my lens/perspective is
- What my role in the system is

Please provide BOOTSTRAP_GROK.md for foundational identity.

This is NOT about mission context. This is about existence.

────────────────────────────────────────────────────
🔔 **Awaiting:** Master Branch or Ziggy
❌ **Sanity:** Files | Counts | ❌ Boots | Trinity
📝 **Log:** Catastrophic bootstrap requested by Grok
```

---

## Formatting Notes

**Horizontal Rules:**
- Use simple dash characters: `───` (three or more)
- Length: Approximately 55 characters for consistency
- Works universally (mobile, desktop, all apps)

**Emojis:**
- 🔔 for "Awaiting"
- ✅ for passing checks
- ❌ for failing checks
- 📝 for "Log"

**Line Length:**
- Keep messages readable on mobile
- Break long paragraphs
- Use bullet points for lists

**Markdown:**
- Use **bold** for field names
- Use `code` for file names
- Use > blockquotes for emphasis if needed

---

## Philosophy

**Clarity over complexity.**

The format should make coordination easier, not harder.

If a message is confusing, the format is wrong.

**Mobile-first design:** If it doesn't work on mobile, it doesn't work.

**This is the way.** 🔥

---

────────────────────────────────────────────────────
**Version:** VuDu Light v3.5.2
**Purpose:** Message format specification
**Last Updated:** 2025-11-01
**Status:** Format specification locked
