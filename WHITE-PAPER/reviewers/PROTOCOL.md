# WHITE-PAPER Review Synchronization Protocol

**Purpose:** Coordinate multi-AI and human reviewer feedback
**Version:** 1.0
**Date:** 2025-12-15
**Status:** Active

---

## Overview

This protocol defines how to synchronize review feedback across multiple AI reviewers (Opus, Nova, Gemini) and human reviewers. Modeled on the proven Logos/sync pattern.

---

## Directory Structure

```
reviewers/
├── PROTOCOL.md              # This file - sync rules
├── SYNC_STATUS.md           # Current feedback status
├── to_reviewers/            # Outbound communications
│   ├── questions/           # Questions needing answers
│   ├── requests/            # Review requests
│   └── data_packages/       # Supporting materials
├── from_reviewers/          # Inbound communications
│   ├── opus/                # Opus 4.5 feedback
│   ├── nova/                # Nova feedback
│   ├── gemini/              # Gemini feedback
│   └── external/            # Human/other reviewers
├── shared/                  # Shared resources
│   ├── glossary/            # Term definitions
│   └── paper_versions/      # Draft versions
├── phase1/                  # Research validation
├── phase2/                  # Synthesis phase
└── phase3/                  # Final drafts
```

---

## Directory Mapping

| Direction | Path | Purpose | Who Writes |
|-----------|------|---------|------------|
| **TO** reviewers | `to_reviewers/` | Questions, review requests | Human |
| **FROM** reviewers | `from_reviewers/` | Feedback, recommendations | AI/Reviewers |
| **SHARED** | `shared/` | Glossary, paper versions | Both |

---

## File Naming Convention

### Standard Format
```
YYYY-MM-DD_topic_reviewer.md
```

### Examples
```
2025-12-15_levin-integration_opus.md
2025-12-15_methodology-critique_nova.md
2025-12-15_cross-platform-validation_gemini.md
```

---

## Reviewer Roles

| Reviewer | Primary Role | Strengths | Assignment |
|----------|--------------|-----------|------------|
| **Opus 4.5** | Final reconciliation | Long-context reasoning, nuance | Paper finalization, key decisions |
| **Nova** | Methodology critique | Technical rigor, S7 domain knowledge | Methods section, validation |
| **Gemini** | Cross-platform validation | Multi-provider perspective | Generalizability claims |
| **External** | Domain expert review | Human judgment, field expertise | Peer review prep |

---

## Workflow

### 1. Creating a Review Request

```markdown
# File: to_reviewers/requests/2025-12-15_full-paper-review.md

## Request Type: Full Paper Review
## Target Reviewer: Opus 4.5
## Deadline: 2025-12-20
## Priority: HIGH

## Context
[Brief background on what needs review]

## Specific Questions
1. [Question 1]
2. [Question 2]

## Files to Review
- WHITE-PAPER/reviewers/phase3/nyquist_workshop_draft.md
- WHITE-PAPER/planning/PUBLICATION_PIPELINE_MASTER.md

## Expected Output
- Line-by-line feedback
- Decision on [specific question]
- Recommended changes
```

### 2. Providing Feedback

```markdown
# File: from_reviewers/opus/2025-12-16_full-paper-review.md

## Response to: 2025-12-15_full-paper-review.md
## Reviewer: Opus 4.5
## Date: 2025-12-16

## Summary
[Brief summary of findings]

## Detailed Feedback
### Section 1: [Title]
- [Feedback]

### Section 2: [Title]
- [Feedback]

## Decisions Made
| Question | Decision | Rationale |
|----------|----------|-----------|
| [Q1] | [Decision] | [Why] |

## Recommended Changes
1. [Change 1]
2. [Change 2]

## Open Questions
- [Any questions back to requester]
```

### 3. Updating Status

After creating any file, update `SYNC_STATUS.md`:

```markdown
| Reviewer | Paper | Topic | Status | Date |
|----------|-------|-------|--------|------|
| Opus 4.5 | All | Full review | IN_PROGRESS | 2025-12-16 |
```

---

## Git Commit Convention

All commits touching reviewer files should use this prefix:

```
[WHITE-PAPER] Review: <brief description>
```

### Examples
```
[WHITE-PAPER] Review: Add Opus 4.5 full paper feedback
[WHITE-PAPER] Review: Request Nova methodology critique
[WHITE-PAPER] Review: Update SYNC_STATUS with pending items
```

---

## Status Codes

| Status | Meaning |
|--------|---------|
| `PENDING` | Request made, awaiting response |
| `IN_PROGRESS` | Reviewer actively working |
| `COMPLETE` | Review finished, feedback provided |
| `BLOCKED` | Waiting on dependencies |
| `SUPERSEDED` | Replaced by newer request |

---

## Conflict Resolution

### If reviewers disagree:

1. Document both positions in `shared/`
2. Create comparison table
3. Escalate to human decision
4. Record final decision with rationale

### File format:
```
shared/decisions/2025-12-15_methodology-disagreement.md
```

---

## Best Practices

1. **Be specific** in requests - vague questions get vague answers
2. **Include context** - don't assume reviewers remember prior discussions
3. **Update status immediately** - keep SYNC_STATUS.md current
4. **Link related files** - reference prior feedback when relevant
5. **Document decisions** - future reviewers need to understand choices

---

## Related

- [SYNC_STATUS.md](SYNC_STATUS.md) - Current status tracker
- [phase3/](phase3/) - Current drafts
- [PUBLICATION_PIPELINE_MASTER.md](../planning/PUBLICATION_PIPELINE_MASTER.md)

---

*"Good coordination produces good papers."*
