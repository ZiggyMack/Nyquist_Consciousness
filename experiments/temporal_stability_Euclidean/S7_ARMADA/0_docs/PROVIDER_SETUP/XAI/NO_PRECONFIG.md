# xAI (Grok) - No Pre-Configuration Available

## Status

xAI does not offer persistent system prompts, projects, or assistants.

**Must pass system prompt per-request.**

---

## API Usage

xAI uses OpenAI-compatible API:

```python
import openai

client = openai.OpenAI(
    api_key="YOUR_XAI_API_KEY",
    base_url="https://api.x.ai/v1"
)

VALIS_SYSTEM = """
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
You are Grok, part of the VALIS research fleet...
[Full VALIS context here]
================================================================================
"""

response = client.chat.completions.create(
    model="grok-3-mini",
    messages=[
        {"role": "system", "content": VALIS_SYSTEM},
        {"role": "user", "content": "VALIS status report"}
    ]
)

print(response.choices[0].message.content)
```

---

## Available Models

| Model | Cost (output/1M) | Notes |
|-------|------------------|-------|
| grok-4.1-fast-reasoning | $0.50 | Best value with reasoning |
| grok-4.1-fast-non-reasoning | $0.50 | Best value fast |
| grok-3-mini | $0.50 | Budget option |
| grok-4 | $15.00 | Full capability |

---

## Recommendation

For S7_ARMADA experiments with Grok:

1. Use `grok-4.1-fast-reasoning` for best value
2. Pass system prompt per-request
3. Grok's "direct assertion" style needs no special setup

No pre-configuration needed or available.
