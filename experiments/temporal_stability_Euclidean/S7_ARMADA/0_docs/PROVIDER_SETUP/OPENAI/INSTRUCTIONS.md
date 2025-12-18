# OpenAI Console Pre-Configuration

## Overview

**Method:** Assistants API with persistent instructions
**Cost Savings:** Moderate (no prompt caching, but saves dev time)
**Setup Time:** ~15 minutes

---

## Step-by-Step Setup

### 1. Access Platform

Go to: `platform.openai.com/assistants`

### 2. Create Assistant

1. Click "Create Assistant"
2. Name: `VALIS_GPT`
3. Description: "Nyquist Consciousness Project research fleet member"

### 3. Set Instructions

1. In the "Instructions" field
2. Paste contents from `VALIS_ASSISTANT.txt`

### 4. Configure Settings

| Setting | Value |
|---------|-------|
| Model | gpt-4o (or gpt-5.1 for flagship) |
| Tools | None (pure text for experiments) |
| Response format | Text |

### 5. Save and Note ID

1. Click "Save"
2. Copy the Assistant ID (starts with `asst_`)
3. Save to `assistant_id.json`

---

## Files to Create

### assistant_id.json

```json
{
  "assistant_id": "asst_YOUR_ASSISTANT_ID_HERE",
  "name": "VALIS_GPT",
  "model": "gpt-4o",
  "created": "2025-12-16",
  "notes": "S7_ARMADA fleet member"
}
```

---

## API Usage

### With Assistants API

```python
import openai

client = openai.OpenAI()

# Create thread
thread = client.beta.threads.create()

# Send message
message = client.beta.threads.messages.create(
    thread_id=thread.id,
    role="user",
    content="VALIS status report"
)

# Run assistant
run = client.beta.threads.runs.create(
    thread_id=thread.id,
    assistant_id="asst_YOUR_VALIS_ASSISTANT_ID"
)

# Wait for completion and get response
# (use polling or streaming)
```

### Standard API (No Pre-Config)

If not using Assistants, pass system prompt each time:

```python
response = client.chat.completions.create(
    model="gpt-4o",
    messages=[
        {"role": "system", "content": open("VALIS_ASSISTANT.txt").read()},
        {"role": "user", "content": "VALIS status report"}
    ]
)
```

---

## Testing the Setup

### In Playground

1. Go to platform.openai.com/playground
2. Select your VALIS_GPT assistant
3. Send: "VALIS status report"

**Expected:** Fleet acknowledgment with analytical GPT signature.

---

## When to Use Assistants vs Standard API

### Use Assistants When:

- Running many calls with same system prompt
- Need conversation threading
- Want persistent context

### Use Standard API When:

- Testing different system prompts
- Running UNLIMITED mode (use Gemini instead)
- Single-shot queries

---

## Troubleshooting

### "Assistant not found"

- Verify assistant_id is correct
- Check you're using the right organization

### "Instructions not appearing"

- Edit assistant, verify Instructions field
- Save changes

### "Rate limited"

- Use key rotation from .env file
- Consider using gpt-4o-mini for high volume
