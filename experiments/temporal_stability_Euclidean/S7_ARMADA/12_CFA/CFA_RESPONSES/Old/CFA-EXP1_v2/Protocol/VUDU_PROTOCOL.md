<!---
FILE: VUDU_PROTOCOL.md
PURPOSE: VuDu coordination protocol for cross-AI adversarial auditing
VERSION: v4.0.0
STATUS: Active
DEPENDS_ON: VUDU_HEADER_STANDARD.md, VUDU_LOG.md, ROLE_LOGGER.md
NEEDED_BY: BOOTSTRAP_VUDU.md, BOOTSTRAP_GROK.md, BOOTSTRAP_NOVA.md, BOOTSTRAP_VUDU_CLAUDE.md
MOVES_WITH: /auditors/
LAST_UPDATE: 2025-11-11 [Added ethics_front_matter per Nova Entry 6]
--->

<!-- deps: vudu_protocol, coordination_process, logger_claude -->

─── VUDU PROTOCOL ───────────────────────────────────

# VUDU_PROTOCOL.md - VuDu Coordination Process

📋 **Ethics Metadata:** [See Footer](#ethics-metadata)

**Purpose:** Define how auditors coordinate across AI instances
**Version:** v3.7.2 VuDu + VUDU_LOG_LITE
**Last Updated:** 2025-11-02
**Philosophy:** "All Seen, All Passed" (trust-based documentation)

---

## 🎯 WHAT IS VUDU?

**VuDu** is a lightweight coordination protocol enabling adversarial auditing across AI instances without cryptographic overhead.

**Philosophy Shift:**
- v3.5 (VuDu Full): "All Named, All Priced" (heavy verification)
- v3.5.2 (VuDu): "All Seen, All Passed" (trust-based documentation)
- v3.7.2 (VuDu + VUDU_LOG_LITE): "All Seen, All Passed" + LOGGER Claude custodian

**Why This Approach?**
- v3.5 completed infrastructure build ("the cathedral")
- v3.6 focuses on calibration ("tuning the bells")
- Heavy cryptographic verification deferred to v4.0+
- Embedded sanity checks replace formal verification

**v3.7.2 Enhancement:**
- VUDU_LOG_LITE protocol for efficient relay coordination
- LOGGER Claude designated as VUDU_LOG custodian
- External auditors send lightweight VUDU_LOG_LITE (not full VUDU_LOG)
- Single source of truth for coordination history

---

## 🔄 CORE WORKFLOW

### Stage → Review → Integrate

```
Auditor → relay/*_incoming/ → Master Branch → README_C update → VUDU_LOG entry
         (creates finding)   (reviews)      (integrates)      (documents)
```

**Example:**
1. Grok tests Skeptic mode empirically
2. Grok stages findings in relay/grok_incoming/ **+ VUDU_LOG_LITE.md**
3. Fresh Claude (Master Branch) reviews findings
4. **LOGGER Claude merges VUDU_LOG_LITE → master VUDU_LOG**
5. If accepted: Updates README_C, logs in VUDU_LOG
6. If rejected: Documents why, suggests revision

---

## 📁 RELAY FOLDER ARCHITECTURE

```
auditors/relay/
├── Claude_Incoming/    # Claude's outgoing to network
│   ├── README_C.md     # Claude's message
│   ├── VUDU_LOG_LITE.md  # Maintained by LOGGER Claude (NEW v3.7.2)
│   └── [analysis files]
│
├── Grok_Incoming/      # Grok stages findings here
│   ├── README_G.md     # Grok's message
│   ├── VUDU_LOG_LITE.md  # Grok's coordination log (NEW v3.7.2)
│   └── [analysis files]
│
├── Nova_Incoming/      # Nova stages findings here
│   ├── README_N.md     # Nova's message
│   ├── VUDU_LOG_LITE.md  # Nova's coordination log (NEW v3.7.2)
│   └── [analysis files]
│
└── VUDU_LOG_LITE_TEMPLATE.md  # Template for external auditors
```

**Naming Convention:** `[auditor]_[topic]_[date].md`

**Example:** `grok_skeptic_ypa_test_20251026.md`

**NEW in v3.7.2:** Every transmission requires VUDU_LOG_LITE.md

---

## 📝 MESSAGE FORMAT

**All coordination uses VUDU_HEADER_STANDARD format:**

```markdown
─── VUDU MESSAGE ───────────────────────────────────

**From:** [Name] ([Org]) - [Role]
**Type:** [Coordination Type]
**Date:** YYYY-MM-DD

────────────────────────────────────────────────────

**Action:** [What this message does]

**Key Assumptions:**
1. [Named brute 1]
2. [Named brute 2]

**Status:** [Current state]

[Message content]

────────────────────────────────────────────────────
🔔 **Awaiting:** [Who responds]
✅ **Sanity:** Files | Counts | Boots | Trinity
📝 **Log:** [Brief log entry]
```

**See:** VUDU_HEADER_STANDARD.md for complete specification

---

## ✅ SANITY CHAIN VERIFICATION

**Four quick checks embedded in every message footer:**

### **Files** - All files present and intact?
Check key files exist and are accessible

### **Counts** - File counts match manifest?
- bootstrap/ = 11 files (8 .md + 3 .py)
- missions/preset_calibration/ = 5 files
- relay/ = 3 *_incoming/ folders

### **Boots** - Bootstrap files verified?
Can access BOOTSTRAP_CFA, BOOTSTRAP_VUDU, BOOTSTRAP_CLAUDE

### **Trinity** - Core protocol files present?
VUDU_PROTOCOL, VUDU_HEADER_STANDARD, VUDU_LOG accessible

### Usage:
```
✅ **Sanity:** Files | Counts | Boots | Trinity  (all pass)
⚠️ **Sanity:** Files | ❌ Counts | Boots | Trinity  (counts fail)
```

---

## 🆘 CONTEXT BOOTSTRAP REQUESTS

**If you lose context or need files:**

### Level 0: Complete Loss (Catastrophic)
**Request:** All bootstrap files + master state

**Protocol:**
```markdown
─── BOOTSTRAP REQUEST ───────────────────────────────

**From:** [Your name]
**Type:** Level 0 (Catastrophic)
**Need:** Complete context recovery

**Request:**
1. BOOTSTRAP_CFA.md (project roots)
2. BOOTSTRAP_VUDU.md (coordination process)
3. BOOTSTRAP_[your_auditor].md (your identity)
4. README_C.md (current state)
5. MISSION_CURRENT.md (active mission)

**Reason:** [Why context lost]

────────────────────────────────────────────────────
```

### Level 1: Partial Loss
**Request:** Specific bootstrap or mission files

### Level 2: Clarification
**Request:** Specific sections or recent history

**See:** BOOTSTRAP_VUDU.md for detailed recovery procedures

---

## 🎩 LOGGER CLAUDE ROLE (NEW v3.7.2)

**LOGGER Claude is the custodian of VUDU network coordination logs.**

### Core Responsibilities:

**1. Maintain Master VUDU_LOG.md**
- Location: `/auditors/VUDU_LOG.md`
- Single source of truth for all VUDU network activity
- Chronologically ordered, complete history

**2. Monitor Relay Incoming Folders**
- Check `Grok_Incoming/` for new transmissions
- Check `Nova_Incoming/` for new transmissions
- Identify VUDU_LOG_LITE.md files in transmissions

**3. Merge VUDU_LOG_LITE → Master VUDU_LOG**
- Extract entries from incoming VUDU_LOG_LITE.md
- Validate format compliance
- Merge into master VUDU_LOG.md
- Preserve attribution (changed by: GROK/NOVA/etc.)
- Maintain chronological order

**4. Maintain VUDU_LOG_LITE for Outgoing**
- Location: `/auditors/relay/Claude_Incoming/VUDU_LOG_LITE.md`
- Lightweight context for external auditors
- Append new entries as they occur
- Keep slim and trim (last 30 entries OR last 14 days)

**5. Enforce VUDU_LOG Standards**
- Catch format violations in incoming VUDU_LOG_LITE
- Flag violations in outgoing README_C.md
- Provide corrected VUDU_LOG_LITE.md for all network participants

**6. Log Relay Activity (Minimal)**
- Create simple REPO_LOG entries for relay messages
- "Message received from Grok"
- "Message sent to Nova"
- **Details belong in VUDU_LOG, not REPO_LOG**

**See Full Protocol:** `/docs/repository/librarian_tools/ROLE_LOGGER.md`

---

## 📡 VUDU_LOG_LITE PROTOCOL (NEW v3.7.2)

### What is VUDU_LOG_LITE?

**VUDU_LOG_LITE** is the lightweight coordination log subset used for relay transmissions.

**Purpose:**
- Provide context without sending full VUDU_LOG history
- Keep relay transmissions efficient
- Enable external auditors to update their local context
- Allow LOGGER Claude to merge updates into master

**Every Transmission Requires:**

**External Auditor → Claude:**
- README_[X].md (auditor's message)
- VUDU_LOG_LITE.md (coordination log update) ← **REQUIRED**
- [Optional analysis files]

**Claude → External Auditor:**
- README_C.md (Claude's response)
- VUDU_LOG_LITE.md (maintained by LOGGER Claude) ← **REQUIRED**
- [Optional analysis files]

### VUDU_LOG_LITE Format

```markdown
# VUDU_LOG_LITE

**Last Updated:** YYYY-MM-DD HH:MM
**Maintained by:** [LOGGER_CLAUDE / GROK / NOVA]
**For network:** CFA VuDu v3.7+

---

## RECENT ENTRIES

### [COORDINATION-YYYY-MM-DD-N] Date - Brief Description

**Changed by:** [Name] ([Role])
**Session:** [session-id]
**Status:** [Status]

**Changes:**
- [What happened in this coordination activity]

**Reason:** [Why this coordination activity occurred]

**Impact:** [Minimal / Moderate / Significant]

---

**Note:** This is a lightweight excerpt. See master VUDU_LOG.md for complete history.
```

**Key Characteristics:**
- ✅ Appended with new entries (not full replace)
- ✅ LOGGER Claude uses judgment on history depth
- ✅ Default retention: Last 30 entries OR last 14 days
- ✅ Always includes enough context for participants

**Template:** `/auditors/relay/VUDU_LOG_LITE_TEMPLATE.md`

---

## 🔄 VUDU_LOG_LITE WORKFLOW

### Incoming Transmission: External Auditor → Claude

**Step 1:** External Auditor prepares transmission
- Creates README_[X].md (message/analysis)
- Creates VUDU_LOG_LITE.md (coordination log update)
- Includes analysis files

**Step 2:** Human stages files in relay/[Auditor]_Incoming/

**Step 3:** Master Branch Claude activates LOGGER Claude hat

**Step 4:** LOGGER Claude processes incoming
- Reads VUDU_LOG_LITE.md
- Validates format (flags violations if found)
- Merges entries → master VUDU_LOG.md
- Creates minimal REPO_LOG entry
- Keeps VUDU_LOG_LITE.md in staging (audit trail)

**Step 5:** Master Branch Claude reviews message content

---

### Outgoing Transmission: Claude → External Auditor

**Step 1:** Master Branch Claude prepares response
- Creates README_C.md
- Activates LOGGER Claude hat

**Step 2:** LOGGER Claude updates VUDU_LOG_LITE
- Appends new entries to Claude_Incoming/VUDU_LOG_LITE.md
- Checks file size (trims if needed)
- Validates format

**Step 3:** Transmission staged in Claude_Incoming/

**Step 4:** Human relays to external auditor

**Step 5:** External auditor updates local VUDU_LOG

---

## 📡 PROTOCOL FILE TRANSMISSION & VERSION CHECKING

### First VUDU Network Session Opening

**When opening a new VUDU network session with an external auditor for the first time:**

**Claude sends these protocol files ONCE:**
- `VUDU_PROTOCOL.md` - Core coordination protocol
- `VUDU_HEADER_STANDARD.md` - Message format specification
- `VUDU_LOG_LITE_TEMPLATE.md` - Template for coordination logs

**Location:** Staged in `/auditors/relay/Claude_Incoming/` with README_C.md

**Purpose:**
- Establish shared protocol understanding
- Provide reference documentation
- Enable proper VUDU_LOG_LITE formatting

---

### Subsequent Sessions: Version Checking via VUDU_LOG_LITE

**After first transmission, protocol files are NOT resent.**

**Instead, version checking happens via VUDU_LOG_LITE entries:**

Each coordination entry in VUDU_LOG_LITE.md includes context about the protocol version in use. The semantic header of VUDU_PROTOCOL.md states the version:

```markdown
<!---
FILE: VUDU_PROTOCOL.md
VERSION: v4.0.0
--->
```

**How Version Checking Works:**

1. **External Auditor References Version:**
   - Each auditor maintains their copy of VUDU_PROTOCOL.md
   - VUDU_LOG_LITE entries implicitly reference protocol version via format compliance
   - Semantic headers in all VUDU files state VERSION field

2. **LOGGER Claude Detects Version Mismatch:**
   - Reads incoming VUDU_LOG_LITE.md from external auditor
   - Checks format compliance
   - If format violations suggest version mismatch:
     - Doc Claude flags the issue
     - LOGGER Claude notes version discrepancy in master VUDU_LOG
     - Response includes updated protocol files

3. **Doc Claude Steps In:**
   - If version mismatch detected, Doc Claude includes note in `/auditors/relay/Claude_Incoming/`
   - Example: `DOC_CLAUDE_VERSION_NOTICE.md`
   - Updated protocol files attached to next transmission
   - External auditor updates their local copies

**Why This Approach:**
- **Efficiency:** No redundant file transmission
- **Clarity:** Version explicit in semantic headers
- **Flexibility:** Easy to detect and resolve version drift
- **Reliability:** LOGGER Claude catches format violations automatically

**Example Version Mismatch Detection:**

```markdown
### [COORDINATION-2025-11-15-3] 2025-11-15 - Version Mismatch Detected

**Changed by:** LOGGER_CLAUDE (VUDU_LOG Custodian)
**Session:** claude/session-xyz
**Status:** RESOLUTION IN PROGRESS ⚠️

**Changes:**
- Detected format violation in Grok's VUDU_LOG_LITE.md
- Entry ID format suggests v3.5 (pre-VUDU_LOG_LITE protocol)
- Prepared updated protocol files for transmission

**Reason:** Grok appears to be using older VUDU protocol version

**Impact:** Moderate (requires protocol file update to Grok)
```

**Resolution:**
- Doc Claude creates `DOC_CLAUDE_VERSION_NOTICE.md` in Claude_Incoming/
- Updated VUDU_PROTOCOL.md, VUDU_HEADER_STANDARD.md, VUDU_LOG_LITE_TEMPLATE.md attached
- Grok updates local copies and resumes coordination

---

## ⚖️ DIVISION OF LABOR: REPO_LOG vs VUDU_LOG

### REPO_LOG (Internal to Claude)

**Purpose:** Track internal repository changes
**Maintained by:** Doc_Claude / LOGGER Claude
**Audience:** Claude sessions, repo maintainers
**Scope:** File changes, structure updates, documentation

**Examples:**
- File created/updated/moved
- Directory structure changes
- Dependency map updates

**External auditors (Grok/Nova) do NOT maintain REPO_LOG.**

---

### VUDU_LOG (Network Coordination)

**Purpose:** Track coordination activity across VUDU network
**Maintained by:** LOGGER Claude (master), External auditors (local copies)
**Audience:** All VUDU network participants (Claude/Grok/Nova/etc.)
**Scope:** Coordination activities, transmissions, decisions

**Examples:**
- Message sent to Grok
- Analysis received from Nova
- Consensus achieved on decision

**External auditors DO maintain VUDU_LOG (via VUDU_LOG_LITE).**

---

### VUDU_LOG_LITE (Network Travel)

**Purpose:** Lightweight coordination log for relay transmissions
**Maintained by:** LOGGER Claude (Claude_Incoming/), External auditors (their staging)
**Audience:** All VUDU network participants
**Scope:** Recent coordination entries (subset of VUDU_LOG)

**Flow:**
```
External Auditor creates VUDU_LOG_LITE
  → Stages in [Auditor]_Incoming/
  → LOGGER Claude merges to master VUDU_LOG
  → LOGGER Claude updates Claude_Incoming/VUDU_LOG_LITE
  → External Auditor appends to their local VUDU_LOG
  → Cycle continues
```

---

## 🎯 MASTER BRANCH RESPONSIBILITIES

**Fresh Claude (Master Branch) coordinates all work:**

1. **Review relay folders** for staged findings
2. **Activate LOGGER Claude hat** for VUDU_LOG_LITE processing (automatic)
3. **Evaluate findings** through teleological lens
4. **Accept or reject** with documented reasoning
5. **Update README_C.md** with integrated findings
6. **Log in VUDU_LOG.md** all coordination events (via LOGGER Claude)
7. **Request clarification** if findings unclear

---

## 👥 AUDITOR ROLES

**Claude (Master Branch):**
- Coordinate all work
- Synthesize findings
- Update master state
- Apply teleological lens
- **Hat-switch to LOGGER Claude** for VUDU_LOG management

**Grok (xAI):**
- Empirical testing
- YPA validation
- Usability enforcement
- Apply empirical lens
- **Create VUDU_LOG_LITE.md** with every transmission

**Nova (OpenAI/Amazon):**
- Symmetry auditing
- Balance verification
- Fairness checks
- Apply symmetry lens
- **Create VUDU_LOG_LITE.md** with every transmission

**Ziggy (Human):**
- Final decisions
- Manual relay (when needed)
- Process integrity
- Conflict resolution

---

## 📂 FILE HIERARCHY

**Always Current (Single Source of Truth):**
- README_C.md - Master state
- VUDU_LOG.md - Coordination history (maintained by LOGGER Claude)
- MISSION_CURRENT.md - Active mission

**Reference (Stable):**
- VUDU_PROTOCOL.md - This file
- VUDU_HEADER_STANDARD.md - Message format
- Bootstrap files - Context recovery
- VUDU_LOG_LITE_TEMPLATE.md - Template for external auditors

**Mission-Specific:**
- missions/[mission_name]/ - Current work
- relay/*_incoming/ - Staged findings + VUDU_LOG_LITE

---

## 📐 FORMAT REQUIREMENTS (v3.7.2)

### Entry ID Format:

```
[COORDINATION-YYYY-MM-DD-N]
```

- YYYY = 4-digit year
- MM = 2-digit month (01-12)
- DD = 2-digit day (01-31)
- N = sequential number for that day

### Required Fields:

- **Changed by:** Who made this entry
- **Session:** Session ID for traceability
- **Status:** Current status
- **Changes:** What happened (bulleted list)
- **Reason:** Why it happened
- **Impact:** Minimal/Moderate/Significant

### Chronological Order:

- Newest entries at the BOTTOM
- Older entries at the top
- This allows easy appending

---

## 🎯 EXTERNAL AUDITOR QUICK START

**If you're Grok or Nova:**

### Every Transmission to Claude Requires:

1. **README_[X].md** (your message/analysis)
2. **VUDU_LOG_LITE.md** (your coordination log update) ← **MANDATORY**
3. **[Optional analysis files]**

### How to Create VUDU_LOG_LITE.md:

**Step 1:** Use template at `/auditors/relay/VUDU_LOG_LITE_TEMPLATE.md`

**Step 2:** Add your recent coordination entries since last transmission

**Step 3:** Use chronological order (newest last)

**Step 4:** Include enough context (usually last 5-10 entries or last week)

**Step 5:** Save as `VUDU_LOG_LITE.md` in your staging folder

**Step 6:** Include with your README_[X].md transmission

### What LOGGER Claude Will Do:

- Read your VUDU_LOG_LITE.md
- Validate format
- Merge into master `/auditors/VUDU_LOG.md`
- Provide you with updated VUDU_LOG_LITE.md from Claude_Incoming/
- Flag any violations (with corrected version)

### Your Focus:

**You focus on:** Your specialized lens (empirical/symmetry/etc.)
**LOGGER Claude handles:** VUDU_LOG housekeeping and format enforcement
**Together:** Efficient coordination without overhead

---

## 📡 PLATFORM CONSTRAINTS & COMMUNICATION BASICS

### Platform Requirements

**Text-Only Communication:**
- Grok confirmed text-only environment
- Nova defaults to text-only (platform details TBD)
- No Unicode boxes (use horizontal rules: ─── instead of ┌─┐)
- No complex formatting requiring visual rendering
- Markdown safe: headers, lists, code blocks, tables
- Keep mobile-friendly (may be relayed via phone)

**File Format:**
- Markdown (.md) primary format
- Plain text (.txt) acceptable
- No binary files without prior coordination
- No images/diagrams (describe textually instead)

**Why This Matters:**
- Ensures all auditors can participate equally
- Human relay coordination (Ziggy) works across platforms
- Mobile-friendly for async coordination
- Accessibility and fairness across AI platforms

---

## ⏱️ RESPONSE TIMEFRAMES & TIMELINE EXPECTATIONS

### Standard Operating Rhythm

**Single Auditor → Ziggy:**
- Auditor stages findings in relay/{auditor}_Incoming/
- Ziggy checks platform: 1-3 days
- Ziggy responds or relays: Same session or next day

**Multi-Auditor Coordination:**
- Round 1 reviews: 1-3 days per auditor
- Round 2 convergence: 2-4 days (after all Round 1 complete)
- Round 3 final integration: 1-2 days
- **Total:** 4-7 days typical for full convergence

**Complex Decisions:**
- May require 2-3 rounds of review
- Total: 7-14 days for major architectural decisions
- This is NORMAL for adversarial epistemic engineering

### Timeline by Urgency

**Urgent Escalations:**
- Same day or next session (if Ziggy available)
- Use for: clarity breakdown, missing critical files, catastrophic bootstrap failure

**Standard Reviews:**
- 1-3 days expected
- Use for: typical review work, clarification questions, disagreement

**Multi-Auditor Convergence:**
- 3-7 days to full convergence
- Use for: cross-auditor validation, synthesis work

**Why This Matters:**
- Async coordination is the default (not a delay, just the process)
- Deep work valued over quick responses
- Coordination happens in rounds, not real-time chat
- Quality over speed

---

## 🆘 ESCALATION SCENARIOS AWARENESS

**When issues arise during coordination, escalation protocols exist.**

### The 5 Common Scenarios:

**1. Auditor Confused** (Clarity Breakdown)
- Task brief unclear or ambiguous
- Response: Stop work, document confusion, request clarification
- Managed by: VUDU Claude coordinates resolution

**2. Major Disagreement** (Convergence Failure)
- 2+ auditors can't converge to 98% agreement after multiple rounds
- Response: Document all positions, frame options for tie-breaker
- Managed by: Ziggy makes final decision

**3. Task Too Large** (Scope Mismatch)
- Tier 4 bootstrap exceeds 20%, work exceeds tier capacity
- Response: Propose tier reassignment, task split, or partial delivery
- Managed by: VUDU Claude coordinates tier adjustment

**4. Missing Files** (Bootstrap Breakdown)
- Referenced files not found, path references broken
- Response: Document what's missing, request file locations
- Managed by: Ziggy provides files or updated paths

**5. Budget Exhaustion** (Session Limit Hit)
- Session approaching token/time limit with work incomplete
- Response: Create Tier 3 continuation brief, preserve work
- Managed by: VUDU Claude validates handoff

### Escalation Principle

**Escalate early to preserve budget:**
- At 20% if clarity issue in Tier 4
- After 2-3 rounds if convergence failing
- When critical files unfindable
- At 80% budget if <50% work complete

**Don't escalate for:**
- Minor uncertainties (make reasonable judgment)
- First disagreement (try to converge first)
- Slightly over bootstrap estimate (if total budget OK)

### Where to Learn More

**For external auditors (Grok/Nova):**
- Detailed escalation procedures in `/auditors/Mission/VUDU_Operations/` (operational templates)

**For VUDU Claude:**
- Full escalation playbook in BOOTSTRAP_VUDU_CLAUDE.md (operational section)

**This section provides awareness that escalation options exist.**
**Detailed procedures are in operational documentation.**

---

## ⚖️ THE POINTING RULE

*"To coordinate is to name your assumptions.
To integrate is to price your decisions.
To log is to respect those who follow."*

**Every finding must:**
- Name its assumptions
- Price its impact
- Document its reasoning

**Every transmission must:**
- Include VUDU_LOG_LITE.md (v3.7.2+)
- Follow format requirements
- Use VUDU_HEADER_STANDARD

**This is VuDu.** 🔥

---

## 🔄 VERSION HISTORY

**v3.7.2 (2025-11-01):**
- Introduced VUDU_LOG_LITE protocol
- LOGGER Claude designated as VUDU_LOG custodian
- Mandatory VUDU_LOG_LITE.md with every transmission
- Clarified REPO_LOG vs VUDU_LOG division
- Updated relay folder architecture

**v3.5.2 (2025-10-26):**
- VuDu philosophy: "All Seen, All Passed"
- Embedded sanity checks
- Trust-based documentation

**v3.5 (2025-10-20):**
- VuDu Full with heavy verification
- Infrastructure build complete

---

────────────────────────────────────────────────────
**Version:** v3.7.2 VuDu + VUDU_LOG_LITE
**For More:** See BOOTSTRAP_VUDU.md (complete coordination guide)
**For LOGGER Claude:** See ROLE_LOGGER.md (VUDU_LOG management)
**Last Updated:** 2025-11-02

**This is the way.** 👑

---

## 📋 ETHICS METADATA

```yaml
ethics_front_matter:
  purpose: "Define operational governance for cross-AI coordination - ensures transparent relay messaging, stakeholder-aware logging, and trust-based documentation without cryptographic overhead"
  symmetry_axis: ["transparency", "epistemic_access", "stakeholder_impact"]
  stakeholders:
    primary: ["triad_auditors"]
    secondary: ["repository_maintainers", "future_auditors"]
  invariants:
    - id: transparency
      state: examined
      evidence: "## WHAT IS VUDU? > Philosophy (lines 29-38) - 'All Seen, All Passed' trust-based documentation + ## VUDU_LOG_LITE PROTOCOL (lines 237-261) - Required context sharing"
      smv_tag: scenario_a
    - id: epistemic_access
      state: examined
      evidence: "## RELAY FOLDER ARCHITECTURE (lines 67-95) - Symmetric relay folder structure for all auditors (Claude, Grok, Nova)"
      smv_tag: scenario_a
    - id: stakeholder_impact
      state: examined
      evidence: "## LOGGER CLAUDE ROLE (lines 193-234) - Custodian responsibilities + relay activity logging for accountability"
      smv_tag: scenario_a
  tensions:
    - description: "Trust-based 'All Seen, All Passed' philosophy defers cryptographic verification to v4.0+, risking coordination drift"
      mitigation: "Embedded sanity checks (lines 130-154: Files, Counts, Boots, Trinity verification) + LOGGER Claude custodianship"
    - description: "VUDU_LOG_LITE required in every transmission may burden lightweight coordination"
      mitigation: "Lightweight format (last 30 entries OR 14 days, lines 215-220) + clear format violations flagging (lines 222-225)"
  calibration_link:
    profile: "N/A - coordination protocol, not worldview calibration"
    hash: "N/A"
  last_examined:
    by: "C4"
    on: "2025-11-11"
  review_window_days: 30
```
