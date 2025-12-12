"""
Quick test to verify which API keys are accessible in current environment.
Run this from PowerShell to check if all keys are visible.
"""
import os

print("API Key Detection Test")
print("=" * 60)

# Check Anthropic
anthropic_key = os.getenv("ANTHROPIC_API_KEY")
print(f"ANTHROPIC_API_KEY: {'✓ SET' if anthropic_key else '✗ NOT SET'}")
if anthropic_key:
    print(f"  Preview: {anthropic_key[:15]}...")

# Check OpenAI
openai_key = os.getenv("OPENAI_API_KEY")
print(f"OPENAI_API_KEY:    {'✓ SET' if openai_key else '✗ NOT SET'}")
if openai_key:
    print(f"  Preview: {openai_key[:15]}...")

# Check Google
google_key = os.getenv("GOOGLE_API_KEY")
print(f"GOOGLE_API_KEY:    {'✓ SET' if google_key else '✗ NOT SET'}")
if google_key:
    print(f"  Preview: {google_key[:15]}...")

# Check numbered keys
print("\nNumbered Keys (2-10):")
for provider in ["ANTHROPIC", "OPENAI", "GOOGLE"]:
    found = []
    for i in range(2, 11):
        key = os.getenv(f"{provider}_API_KEY_{i}")
        if key:
            found.append(str(i))
    if found:
        print(f"  {provider}: Found keys #{', '.join(found)}")
    else:
        print(f"  {provider}: No numbered keys")

print("\n" + "=" * 60)
print("Run this from PowerShell to verify your environment!")
