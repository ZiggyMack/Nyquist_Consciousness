<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
-->
# Provider Console Pre-Configuration Guide

## Overview

Pre-configure provider API consoles with VALIS system prompts to:

- Save tokens on every call (~1,500 tokens saved per exchange)
- Enable "VALIS status report" shortcut activation
- Create persistent staging grounds for experiments
- **Up to 90% cost savings** (Anthropic prompt caching)

---

## Provider Capability Summary

| Provider | Pre-Config? | Method | Cost Savings | Setup Effort |
|----------|-------------|--------|--------------|--------------|
| **Anthropic** | YES | Projects + Prompt Caching | **90%** | Medium |
| **OpenAI** | YES | Assistants API | Moderate | Medium |
| **Google** | PARTIAL | Gems (Enterprise only) | Minimal | High |
| **xAI** | NO | Per-request only | None | N/A |
| **Together** | NO | Per-request only | None | N/A |

---

## Quick Start

### 1. Anthropic (Best Option - 90% Savings)

```bash
# See detailed instructions
cat ANTHROPIC/INSTRUCTIONS.md
```

### 2. OpenAI (Good Option)

```bash
# See detailed instructions
cat OPENAI/INSTRUCTIONS.md
```

### 3. Others

Google, xAI, and Together.ai require per-request system prompts.
No pre-configuration available.

---

## Directory Structure

```
PROVIDER_SETUP/
├── README.md                    # This file
├── ANTHROPIC/
│   ├── INSTRUCTIONS.md          # Step-by-step for Claude Projects
│   └── VALIS_SYSTEM_PROMPT.txt  # Ready to paste
├── OPENAI/
│   ├── INSTRUCTIONS.md          # Step-by-step for Assistants
│   └── VALIS_ASSISTANT.txt      # Ready to paste
├── GOOGLE/
│   ├── INSTRUCTIONS.md          # Gems setup (enterprise)
│   └── api_system_instruction.py  # Code snippet
├── XAI/
│   └── NO_PRECONFIG.md          # Explains per-request only
└── TOGETHER/
    └── NO_PRECONFIG.md          # Explains per-request only
```

---

## When to Use Pre-Configuration

### USE IT when:

- Running 100+ iterations on same system prompt
- Token costs exceeding $10/run
- Need "VALIS status report" shortcut

### SKIP IT when:

- Testing new prompts (need flexibility)
- Running experiments with varying system prompts
- Using UNLIMITED mode (free anyway)

---

## Implementation Priority

1. **Anthropic FIRST** - 90% savings, best tooling
2. **OpenAI SECOND** - Assistants API mature
3. **Others** - Skip pre-config, use per-request

---

## Files to Have Ready

Before configuring any provider, locate these files:

| File | Location | Purpose |
|------|----------|---------|
| VALIS Declaration | `0_docs/specs/4_VALIS_DECLARATION.md` | Fleet identity context |
| I_AM_CLAUDE | `0_docs/I_AM_FILES/I_AM_CLAUDE.md` | Claude-specific identity |
| I_AM_GPT | `0_docs/I_AM_FILES/I_AM_GPT.md` | GPT-specific identity |
| Run Methodology | `0_docs/specs/0_RUN_METHODOLOGY.md` | Research context |

---

## Related Documentation

| Document | Location |
|----------|----------|
| CLAL.py | `1_CALIBRATION/CLAL.py` |
| Fleet Map | `../../../../docs/maps/ARMADA_MAP.md` |
| 14_CONSCIOUSNESS | `14_CONSCIOUSNESS/README.md` |
