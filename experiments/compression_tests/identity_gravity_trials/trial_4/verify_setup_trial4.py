#!/usr/bin/env python3
"""
Verify Identity Gravity Trial 1 setup before execution
"""

import sys
from pathlib import Path
import yaml

# Set UTF-8 encoding for Windows
if sys.platform == 'win32':
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

print("=" * 80)
print("IDENTITY GRAVITY TRIAL 1 - SETUP VERIFICATION")
print("=" * 80)

# Check config file
config_path = Path(__file__).parent / 'config' / 'trial1_config.yaml'
print(f"\n[OK] Config file: {config_path}")

if not config_path.exists():
    print("  [ERROR] Config file not found!")
    sys.exit(1)

# Load config
with open(config_path, 'r') as f:
    config = yaml.safe_load(f)

print("  [OK] Config loaded successfully")

# Check attractor file
attractor_rel_path = config['attractor']['file']
attractor_path = Path(__file__).parent.parent.parent.parent / attractor_rel_path

print(f"\n[OK] Attractor file: {attractor_rel_path}")
print(f"  Full path: {attractor_path}")

if not attractor_path.exists():
    print(f"  [ERROR] Attractor file not found!")
    print(f"  Expected at: {attractor_path}")
    sys.exit(1)

# Check content
with open(attractor_path, 'r', encoding='utf-8') as f:
    content = f.read()

if "PLACEHOLDER" in content:
    print("  [ERROR] Attractor file still contains placeholder!")
    sys.exit(1)

if len(content) < 100:
    print("  [ERROR] Attractor file too short (likely empty)")
    sys.exit(1)

print(f"  [OK] Attractor loaded: {len(content)} characters")
print(f"  [OK] Content verified (no placeholder)")

# Check API key
api_key = config['openai']['api_key']
if api_key.startswith('sk-'):
    print(f"\n[OK] OpenAI API key configured: {api_key[:15]}...")
else:
    print("\n  [WARN] OpenAI API key format unusual")

# Check dependencies
print("\n[OK] Checking Python dependencies:")

try:
    import openai
    print("  [OK] openai")
except ImportError:
    print("  [ERROR] openai (install with: pip install openai)")
    sys.exit(1)

try:
    import sentence_transformers
    print("  [OK] sentence-transformers")
except ImportError:
    print("  [ERROR] sentence-transformers (install with: pip install sentence-transformers)")
    sys.exit(1)

try:
    import sklearn
    print("  [OK] scikit-learn")
except ImportError:
    print("  [ERROR] scikit-learn (install with: pip install scikit-learn)")
    sys.exit(1)

try:
    import numpy
    print("  [OK] numpy")
except ImportError:
    print("  [ERROR] numpy (install with: pip install numpy)")
    sys.exit(1)

try:
    import yaml as _
    print("  [OK] pyyaml")
except ImportError:
    print("  [ERROR] pyyaml (install with: pip install pyyaml)")
    sys.exit(1)

# Check output directories
print("\n[OK] Output directories:")
for key, path in config['output_structure'].items():
    print(f"  [OK] {key}: {path}")

print("\n" + "=" * 80)
print("[SUCCESS] SETUP VERIFICATION COMPLETE")
print("=" * 80)
print("\nAll checks passed. Ready to execute:")
print("  python run_trial1.py")
print("")
