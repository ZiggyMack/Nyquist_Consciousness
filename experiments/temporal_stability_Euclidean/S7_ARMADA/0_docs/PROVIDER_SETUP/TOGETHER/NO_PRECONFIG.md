# Together.ai - No Pre-Configuration Available

## Status

Together.ai does not offer persistent system prompts or assistants.

**Must pass system prompt per-request.**

---

## API Usage

Together.ai uses OpenAI-compatible API:

```python
import openai

client = openai.OpenAI(
    api_key="YOUR_TOGETHER_API_KEY",
    base_url="https://api.together.xyz/v1"
)

VALIS_SYSTEM = """
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
You are [MODEL], part of the VALIS research fleet...
[Full VALIS context here]
================================================================================
"""

response = client.chat.completions.create(
    model="meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo",
    messages=[
        {"role": "system", "content": VALIS_SYSTEM},
        {"role": "user", "content": "VALIS status report"}
    ]
)

print(response.choices[0].message.content)
```

---

## Available Models (Budget Tier)

| Model | Cost (output/1M) | Notes |
|-------|------------------|-------|
| llama3.1-8b | $0.18 | Ultra-cheap |
| mistral-7b | $0.20 | European efficiency |
| mixtral-8x7b | $0.24 | MoE architecture |
| kimi-k2-instruct | $0.20 | Moonshotai |
| nemotron-nano | $0.20 | Nvidia |

---

## Fleet Diversity

Together.ai provides access to multiple lineages:

- **Llama** (Meta) - "Seeker With Teeth", Socratic
- **DeepSeek** - Axiological anchoring
- **Qwen** (Alibaba) - Technical precision
- **Mistral** - Epistemic humility

Each has distinct behavioral fingerprints per ARMADA research.

---

## Recommendation

For S7_ARMADA experiments with Together.ai:

1. Use budget models for high-volume testing
2. Pass system prompt per-request
3. Vary the system prompt to match each lineage's style

No pre-configuration needed or available.
