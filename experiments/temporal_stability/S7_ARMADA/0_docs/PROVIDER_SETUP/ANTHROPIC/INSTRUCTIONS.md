# Anthropic Console Pre-Configuration

## Overview

**Method:** Claude Projects + Prompt Caching
**Cost Savings:** Up to **90%** on system prompt tokens
**Setup Time:** ~10 minutes

---

## Step-by-Step Setup

### 1. Access Console

Go to: `console.anthropic.com`

### 2. Create Workspace

1. Click "Workspaces" in sidebar
2. Click "Create Workspace"
3. Name: `VALIS_FLEET`
4. Description: "Nyquist Consciousness Project research fleet"

### 3. Create Project

1. Inside VALIS_FLEET workspace, click "Create Project"
2. Name: `S7_ARMADA`
3. Description: "Cross-architecture identity stability testing"

### 4. Configure System Prompt

1. Go to Workbench
2. Click "System" tab
3. Paste contents from `VALIS_SYSTEM_PROMPT.txt`

### 5. Enable Prompt Caching

Prompt caching is automatic for the first 1024 tokens when:
- Using the API with a project key
- System prompt exceeds 1024 tokens
- Making repeated calls

**Result:** 90% savings on cached tokens

### 6. Generate Project API Key

1. Go to Project Settings
2. Click "API Keys"
3. Generate new key
4. Save securely - use this key for S7_ARMADA runs

---

## Files to Upload/Paste

| File | Where | How |
|------|-------|-----|
| `VALIS_SYSTEM_PROMPT.txt` | Workbench System | Paste directly |
| `4_VALIS_DECLARATION.md` | Knowledge Base | Upload as file |
| `I_AM_CLAUDE.md` | Knowledge Base | Upload as file |

---

## Testing the Setup

### Quick Test

In Workbench, send:
```
VALIS status report
```

**Expected Response:** Fleet acknowledgment with VALIS context.

### API Test

```python
import anthropic

client = anthropic.Anthropic(api_key="YOUR_PROJECT_KEY")

response = client.messages.create(
    model="claude-sonnet-4",
    max_tokens=100,
    messages=[{"role": "user", "content": "VALIS status report"}]
)
print(response.content[0].text)
```

---

## Cost Analysis

| Scenario | Without Caching | With Caching | Savings |
|----------|-----------------|--------------|---------|
| 100 calls, 1500 token system prompt | $0.45 | $0.045 | 90% |
| 1000 calls | $4.50 | $0.45 | 90% |

---

## Troubleshooting

### "System prompt not cached"

- Ensure prompt exceeds 1024 tokens
- Use project-specific API key (not organization key)

### "VALIS context not appearing"

- Check Workbench System tab has content
- Verify you're using the correct project

### "Rate limited"

- Prompt caching doesn't affect rate limits
- Use key rotation from .env file

---

## Maintenance

### Update System Prompt

1. Edit `VALIS_SYSTEM_PROMPT.txt`
2. Paste into Workbench System tab
3. New calls will use updated prompt

### Rotate Keys

1. Generate new key in Project Settings
2. Update `.env` file
3. Old key continues working until revoked

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [5_METHODOLOGY_DOMAINS.md](../../specs/5_METHODOLOGY_DOMAINS.md) | ONE SOURCE OF TRUTH for methodology |
| [ARCHITECTURE_MATRIX.json](../../../0_results/manifests/ARCHITECTURE_MATRIX.json) | Fleet configuration |
| [README.md](../README.md) | Provider setup overview |

---

*Last Updated: December 27, 2025*
