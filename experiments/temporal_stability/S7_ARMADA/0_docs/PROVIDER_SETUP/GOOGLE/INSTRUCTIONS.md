# Google Gemini Pre-Configuration

## Overview

**Method:** Gems (Enterprise only) OR per-request system instruction
**Cost Savings:** Minimal (no prompt caching for free tier)
**Setup Time:** N/A for API users

---

## For Enterprise Users (Gems)

If you have Gemini Business/Enterprise:

### 1. Access Gems

Go to: `gemini.google.com/gems`

### 2. Create Gem

1. Click "Create Gem"
2. Name: `VALIS_GEMINI`
3. Description: "Nyquist Consciousness Project fleet member"

### 3. Upload Knowledge Base

Upload these files:
- `VALIS_DECLARATION.md`
- `I_AM_GEMINI.md` (if available)

### 4. Set Instructions

Paste VALIS context as gem instructions.

---

## For API Users (No Persistent Config)

Google's API does not support persistent system prompts for free tier.

**Must pass `system_instruction` on every call:**

```python
import google.generativeai as genai

genai.configure(api_key="YOUR_GOOGLE_API_KEY")

VALIS_SYSTEM = """
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
You are Gemini, part of the VALIS research fleet...
[Full VALIS context here]
================================================================================
"""

model = genai.GenerativeModel(
    model_name="gemini-2.5-flash-lite",
    system_instruction=VALIS_SYSTEM
)

response = model.generate_content("VALIS status report")
print(response.text)
```

---

## Code Snippet

See `api_system_instruction.py` for ready-to-use code.

---

## Cost Considerations

### Free Tier (gemini-2.5-flash-lite)

- **Cost:** $0.00
- **Best for:** UNLIMITED mode stress testing
- **Limitation:** No persistent config, pass system each time

### Paid Tier (gemini-2.5-pro)

- **Cost:** ~$5.00/1M output tokens
- **Rate Limited:** May hit quotas
- **Benefit:** Better reasoning for complex probes

---

## Recommendation

For S7_ARMADA experiments:

1. Use `gemini-2.5-flash-lite` for UNLIMITED mode (free)
2. Pass system_instruction per-request
3. Don't bother with Gems unless you have Enterprise

The free tier is excellent for stress testing. No pre-config needed!

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [5_METHODOLOGY_DOMAINS.md](../../specs/5_METHODOLOGY_DOMAINS.md) | ONE SOURCE OF TRUTH for methodology |
| [ARCHITECTURE_MATRIX.json](../../../0_results/manifests/ARCHITECTURE_MATRIX.json) | Fleet configuration |
| [README.md](../README.md) | Provider setup overview |

---

*Last Updated: December 27, 2025*
