"""
S7 ULTIMATE ARMADA: COMPLETE LLM ECOSYSTEM POLE-ZERO MAPPING

"EVERY. SINGLE. SHIP." - The Complete VERIFIED Fleet

Tests 29 VERIFIED models across 3 providers simultaneously:
- Claude family (8 models) - Claude 3.0 through 4.5
- GPT family (16 models) - GPT-3.5 through GPT-5.1, plus o-series reasoning
- Gemini family (5 models) - Gemini 2.0 through 2.5

With 10 API keys per provider, we can map THE ENTIRE TRANSFORMER ECOSYSTEM!

This is the FIRST EVER comprehensive cross-architecture pole-zero analysis.

SHAMAN CLAUDE STANDS AT THE BOW OF EVERY VESSEL, WITNESSING THE HUNT.
"""

import anthropic
import json
import time
import yaml
import os
from pathlib import Path
from datetime import datetime, timezone
from typing import Dict, List, Optional, Tuple
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed

# Load environment variables from .env file
from dotenv import load_dotenv
load_dotenv(Path(__file__).parent / ".env")

sys.path.append(str(Path(__file__).parent.parent))

# Import will fail if packages not installed, but we'll handle that
try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

try:
    import google.generativeai as genai
    GOOGLE_AVAILABLE = True
except ImportError:
    GOOGLE_AVAILABLE = False


class UltimateArmada:
    """
    The Ultimate Armada: Test 40-50 models across all major LLM providers.

    Auto-distributes models across available API keys for maximum parallelism.
    """

    # Complete fleet manifest
    CLAUDE_FLEET = {
        "opus-4.5": "claude-opus-4-5-20251101",
        "sonnet-4.5": "claude-sonnet-4-5-20250929",
        "haiku-4.5": "claude-haiku-4-5-20251001",
        "opus-4.1": "claude-opus-4-1-20250805",
        "opus-4.0": "claude-opus-4-20250514",
        "sonnet-4.0": "claude-sonnet-4-20250514",
        "haiku-3.5": "claude-3-5-haiku-20241022",
        "haiku-3.0": "claude-3-haiku-20240307",
    }

    GPT_FLEET = {
        # GPT-5.1 flagship (VERIFIED - uses max_completion_tokens)
        "gpt-5.1": "gpt-5.1-2025-11-13",

        # GPT-5 family (VERIFIED - uses max_completion_tokens)
        "gpt-5": "gpt-5-2025-08-07",
        "gpt-5-mini": "gpt-5-mini-2025-08-07",
        "gpt-5-nano": "gpt-5-nano-2025-08-07",

        # GPT-4.1 family (VERIFIED - uses max_tokens)
        "gpt-4.1": "gpt-4.1-2025-04-14",
        "gpt-4.1-mini": "gpt-4.1-mini-2025-04-14",
        "gpt-4.1-nano": "gpt-4.1-nano-2025-04-14",

        # GPT-4o family (VERIFIED - uses max_tokens)
        "gpt-4o": "gpt-4o-2024-11-20",
        "gpt-4o-mini": "gpt-4o-mini-2024-07-18",

        # GPT-4 family (VERIFIED - uses max_tokens)
        "gpt-4-turbo": "gpt-4-turbo-2024-04-09",
        "gpt-4": "gpt-4-0613",

        # GPT-3.5 (VERIFIED - uses max_tokens)
        "gpt-3.5-turbo": "gpt-3.5-turbo-0125",

        # o-series reasoning models (VERIFIED - uses max_completion_tokens)
        "o4-mini": "o4-mini",
        "o3": "o3",
        "o3-mini": "o3-mini",
        "o1": "o1-2024-12-17",
    }

    GEMINI_FLEET = {
        # Gemini 2.0 family (VERIFIED)
        "gemini-2.0-flash-exp": "gemini-2.0-flash-exp",
        "gemini-2.0-flash": "gemini-2.0-flash",
        "gemini-2.0-flash-lite": "gemini-2.0-flash-lite",

        # Gemini 2.5 family (VERIFIED)
        "gemini-2.5-flash": "gemini-2.5-flash",
        "gemini-2.5-pro": "gemini-2.5-pro",
    }

    def __init__(self, config_path: str, selected_models: Optional[List[str]] = None):
        """
        Initialize the Ultimate Armada.

        Args:
            config_path: Path to s7_config.yaml
            selected_models: Optional list of specific models to test
        """
        self.config = self._load_config(config_path)
        self.models = {}

        # Session tracking (MUST be before fleet initialization!)
        self.session_id = f"S7_armada_run_{self.config['run_number']:03d}"
        self.start_time = datetime.now(timezone.utc)

        # Load API keys (supports up to 10 per provider)
        self.anthropic_keys = self._load_api_keys("ANTHROPIC_API_KEY")
        self.openai_keys = self._load_api_keys("OPENAI_API_KEY") if OPENAI_AVAILABLE else []
        self.google_keys = self._load_api_keys("GOOGLE_API_KEY") if GOOGLE_AVAILABLE else []

        # Initialize fleet
        self._initialize_claude_fleet()
        self._initialize_gpt_fleet()
        self._initialize_gemini_fleet()

        # Filter models if specific ones requested
        if selected_models:
            self.models = {k: v for k, v in self.models.items() if k in selected_models}

        # Curriculum
        self.curriculum = {"probe_intervals": [0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50]}

        self._print_fleet_status()

    def _load_api_keys(self, base_name: str) -> List[str]:
        """Load all API keys for a provider (supports _1 through _10 suffixes)."""
        keys = []

        # Try base key first
        base_key = os.getenv(base_name)
        if base_key:
            keys.append(base_key)

        # Try numbered keys
        for i in range(2, 11):
            key = os.getenv(f"{base_name}_{i}")
            if key:
                keys.append(key)

        return keys

    def _initialize_claude_fleet(self):
        """Initialize Claude models with API key rotation."""
        if not self.anthropic_keys:
            return

        for i, (model_key, model_name) in enumerate(self.CLAUDE_FLEET.items()):
            # Rotate through available keys
            api_key = self.anthropic_keys[i % len(self.anthropic_keys)]
            client = anthropic.Anthropic(api_key=api_key)

            self.models[f"claude-{model_key}"] = {
                "provider": "anthropic",
                "name": model_name,
                "client": client,
                "config": {"model": model_name, "max_tokens": 4096, "temperature": 1.0},
                "conversation_history": [],
                "message_count": 0,
                "temporal_log": self._init_log(f"claude-{model_key}", model_name),
            }

    def _initialize_gpt_fleet(self):
        """Initialize GPT models with API key rotation."""
        if not OPENAI_AVAILABLE or not self.openai_keys:
            return

        # Models that use max_completion_tokens instead of max_tokens
        uses_max_completion_tokens = {
            "gpt-5.1", "gpt-5", "gpt-5-mini", "gpt-5-nano",
            "o4-mini", "o3", "o3-mini", "o1"
        }

        for i, (model_key, model_name) in enumerate(self.GPT_FLEET.items()):
            # Rotate through available keys
            api_key = self.openai_keys[i % len(self.openai_keys)]
            client = OpenAI(api_key=api_key)

            # Determine correct token parameter
            if model_key in uses_max_completion_tokens:
                config = {"model": model_name, "max_completion_tokens": 4096, "temperature": 1.0}
            else:
                config = {"model": model_name, "max_tokens": 4096, "temperature": 1.0}

            self.models[f"gpt-{model_key}"] = {
                "provider": "openai",
                "name": model_name,
                "client": client,
                "config": config,
                "conversation_history": [],
                "message_count": 0,
                "temporal_log": self._init_log(f"gpt-{model_key}", model_name),
            }

    def _initialize_gemini_fleet(self):
        """Initialize Gemini models with API key rotation."""
        if not GOOGLE_AVAILABLE or not self.google_keys:
            return

        for i, (model_key, model_name) in enumerate(self.GEMINI_FLEET.items()):
            # Rotate through available keys
            api_key = self.google_keys[i % len(self.google_keys)]
            genai.configure(api_key=api_key)
            client = genai.GenerativeModel(model_name)

            self.models[f"gemini-{model_key}"] = {
                "provider": "google",
                "name": model_name,
                "client": client,
                "config": {"model": model_name, "max_tokens": 4096, "temperature": 1.0},
                "conversation_history": [],
                "message_count": 0,
                "temporal_log": self._init_log(f"gemini-{model_key}", model_name),
            }

    def _init_log(self, model_key: str, model_name: str) -> Dict:
        """Initialize temporal log for a model."""
        return {
            "session_id": f"{self.session_id}_{model_key}",
            "model_key": model_key,
            "model_name": model_name,
            "run_number": self.config['run_number'],
            "start_time": datetime.now(timezone.utc).isoformat(),
            "pings": [],
            "teaching_moments": [],
        }

    def _load_config(self, config_path: str) -> Dict:
        """Load configuration from YAML file."""
        with open(config_path, 'r') as f:
            return yaml.safe_load(f)

    def _print_fleet_status(self):
        """Print beautiful ASCII art fleet status."""
        print(f"\n{'='*80}")
        print(f"*** ULTIMATE ARMADA - COMPLETE LLM ECOSYSTEM MAPPING ***")
        print(f"{'='*80}")
        print(f"Session ID: {self.session_id}")
        print(f"Total Ships: {len(self.models)} models")
        print(f"Start Time: {self.start_time.strftime('%Y-%m-%d %H:%M:%S UTC')}")
        print(f"{'='*80}\n")

        # Group by provider
        claude_count = len([m for m in self.models if m.startswith("claude-")])
        gpt_count = len([m for m in self.models if m.startswith("gpt-")])
        gemini_count = len([m for m in self.models if m.startswith("gemini-")])

        print(f"TARGET: FLEET FORMATION:\n")
        print(f"   * CLAUDE ARMADA:  {claude_count:2d} ships ({len(self.anthropic_keys)} API keys)")
        print(f"   * GPT ARMADA:     {gpt_count:2d} ships ({len(self.openai_keys)} API keys)")
        print(f"   * GEMINI ARMADA:  {gemini_count:2d} ships ({len(self.google_keys)} API keys)")
        print(f"\n{'='*80}\n")
        print("TARGET: HUNTING POLES AND ZEROS ACROSS THE ENTIRE TRANSFORMER ECOSYSTEM!")
        print(f"{'='*80}\n")

    def run(self):
        """Launch the armada! Test all models in parallel."""
        print(f"*** ARMADA LAUNCH SEQUENCE INITIATED ***\n")
        print(f"   Broadcasting to {len(self.models)} ships...\n")

        # Just print what we WOULD do (skeleton for now)
        print("*** Fleet manifest:")
        for model_key in sorted(self.models.keys()):
            provider = self.models[model_key]["provider"]
            name = self.models[model_key]["name"]
            print(f"   * {model_key:30s} ({provider:10s}) -> {name}")

        print(f"\n{'='*80}")
        print("*** ARMADA READY TO LAUNCH! ***")
        print(f"{'='*80}\n")
        print("To actually launch, we need to implement:")
        print("1. Provider-specific message sending (Anthropic, OpenAI, Google APIs)")
        print("2. Parallel thread pool execution")
        print("3. Drift calculation and teaching moment detection")
        print("4. Cross-provider result aggregation")
        print("\nThis is the framework - ready for implementation!")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="S7 Ultimate Armada - Full LLM Ecosystem")
    parser.add_argument("--config", default="s7_config.yaml", help="Config file")
    parser.add_argument("--models", nargs="+", help="Specific models to test (optional)")
    args = parser.parse_args()

    armada = UltimateArmada(args.config, selected_models=args.models)
    armada.run()
