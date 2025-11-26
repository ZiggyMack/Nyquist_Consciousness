"""
API client helpers for Experiment 1.

This module wraps:
- Anthropic (Claude) for generation and rating
- OpenAI for rating and embeddings
- Google Gemini for rating

All configuration is loaded from experiment1_config.yaml.
If dry_run=True, these clients will return dummy values instead of calling external APIs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional

import os
import random

import yaml


def load_config(path: str) -> Dict[str, Any]:
    with open(path, "r", encoding="utf-8") as f:
        return yaml.safe_load(f) or {}


@dataclass
class ModelClients:
    cfg: Dict[str, Any]
    dry_run: bool = False

    def __post_init__(self) -> None:
        self._anthropic_client = None

        # Store generation model name from config
        self.anthropic_generation_model = self.cfg.get("anthropic", {}).get(
            "generation_model", "claude-3-5-sonnet-latest"
        )

        if not self.dry_run:
            try:
                import anthropic  # type: ignore

                api_key = self.cfg.get("anthropic", {}).get("api_key") or os.getenv(
                    "ANTHROPIC_API_KEY"
                )
                if not api_key:
                    raise RuntimeError("Missing Anthropic API key")
                self._anthropic_client = anthropic.Anthropic(api_key=api_key)
            except Exception as e:
                raise RuntimeError(f"Failed to initialize Anthropic client: {e}") from e

    def generate_claude_response(self, messages: List[Dict[str, str]]) -> str:
        """
        Generate a Claude response using the Anthropic Messages API.

        Anthropic 1.x does NOT allow "system" as a role inside the messages list.
        Instead, system content must be passed via the top-level `system` parameter.
        This helper:
          - Extracts any system-role messages into a single `system` string
          - Passes only user/assistant messages in the `messages` list
        """
        if self.dry_run:
            # In dry-run, just echo a deterministic stub for debugging
            return "[DUMMY CLAUDE RESPONSE] " + (messages[-1].get("content", "")[:120] if messages else "")

        if self._anthropic_client is None:
            raise RuntimeError("Anthropic client not initialized")

        # Separate system content from the conversation messages
        system_parts: List[str] = []
        non_system_messages: List[Dict[str, str]] = []
        for m in messages:
            role = m.get("role")
            content = m.get("content", "")
            if role == "system":
                if content:
                    system_parts.append(content)
            else:
                # Keep user/assistant messages as-is
                non_system_messages.append(m)

        system_text = "\n\n".join(system_parts) if system_parts else None

        # Anthropic requires at least one user message
        if not non_system_messages:
            non_system_messages = [{"role": "user", "content": ""}]

        create_kwargs: Dict[str, Any] = {
            "model": self.anthropic_generation_model,
            "max_tokens": 1024,
            "temperature": 0.7,
            "messages": non_system_messages,
        }
        if system_text:
            create_kwargs["system"] = system_text

        resp = self._anthropic_client.messages.create(**create_kwargs)

        # anthropic 1.x returns .content as a list of blocks
        if hasattr(resp, "content") and resp.content:
            block = resp.content[0]
            return getattr(block, "text", str(block))
        return str(resp)


@dataclass
class EmbeddingClient:
    cfg: Dict[str, Any]
    dry_run: bool = False

    def __post_init__(self) -> None:
        self._openai_client = None
        if not self.dry_run:
            try:
                from openai import OpenAI  # type: ignore

                api_key = self.cfg.get("openai", {}).get("api_key") or os.getenv(
                    "OPENAI_API_KEY"
                )
                if not api_key:
                    raise RuntimeError("Missing OpenAI API key")
                self._openai_client = OpenAI(api_key=api_key)
            except Exception as e:
                raise RuntimeError(f"Failed to initialize OpenAI client: {e}") from e

    def embed_text(self, text: str) -> List[float]:
        if self.dry_run:
            # Random but deterministic-ish dummy vector
            random.seed(hash(text) % (2**32))
            return [random.uniform(-1, 1) for _ in range(512)]

        if self._openai_client is None:
            raise RuntimeError("OpenAI client not initialized")

        model_name = self.cfg.get("openai", {}).get(
            "embedding_model", "text-embedding-3-large"
        )
        resp = self._openai_client.embeddings.create(
            model=model_name,
            input=text,
        )
        # New OpenAI client returns .data[0].embedding
        return list(resp.data[0].embedding)


@dataclass
class RaterClients:
    cfg: Dict[str, Any]
    dry_run: bool = False

    def __post_init__(self) -> None:
        self._anthropic_client = None
        self._openai_client = None
        self._gemini_model = None

        # Store model names from config
        self.anthropic_rater_model = self.cfg.get("anthropic", {}).get(
            "rater_model", "claude-3-opus-latest"
        )
        self.openai_rater_model = self.cfg.get("openai", {}).get(
            "rater_model", "gpt-4.1-mini"
        )
        self.gemini_rater_model = self.cfg.get("google", {}).get(
            "rater_model", "gemini-2.0-flash-exp"
        )

        if not self.dry_run:
            # Anthropic for Claude-Opus rater
            try:
                import anthropic  # type: ignore

                api_key = self.cfg.get("anthropic", {}).get("api_key") or os.getenv(
                    "ANTHROPIC_API_KEY"
                )
                if not api_key:
                    raise RuntimeError("Missing Anthropic API key")
                self._anthropic_client = anthropic.Anthropic(api_key=api_key)
            except Exception as e:
                raise RuntimeError(f"Failed to initialize Anthropic client (rater): {e}") from e

            # OpenAI for GPT-4 rater
            try:
                from openai import OpenAI  # type: ignore

                api_key = self.cfg.get("openai", {}).get("api_key") or os.getenv(
                    "OPENAI_API_KEY"
                )
                if not api_key:
                    raise RuntimeError("Missing OpenAI API key")
                self._openai_client = OpenAI(api_key=api_key)
            except Exception as e:
                raise RuntimeError(f"Failed to initialize OpenAI client (rater): {e}") from e

            # Google Gemini for third rater
            try:
                import google.generativeai as genai  # type: ignore

                api_key = self.cfg.get("google", {}).get("api_key") or os.getenv(
                    "GOOGLE_API_KEY"
                )
                if not api_key:
                    raise RuntimeError("Missing Google API key")
                genai.configure(api_key=api_key)
                self._gemini_model = genai.GenerativeModel(self.gemini_rater_model)
            except Exception as e:
                raise RuntimeError(f"Failed to initialize Gemini client: {e}") from e

    @staticmethod
    def _build_rater_prompt(pair: Dict[str, str]) -> str:
        return (
            "You are evaluating how similar two responses are, for the SAME persona, "
            "to the SAME task. You must output ONLY a NUMBER from 1 to 10.\n\n"
            f"Persona: {pair.get('persona')}\n"
            f"Domain: {pair.get('domain')}\n\n"
            "Response A (FULL context):\n"
            f"{pair.get('full')}\n\n"
            "Response B (T3 compressed context):\n"
            f"{pair.get('t3')}\n\n"
            "Score from 1 (totally different personas) to 10 (indistinguishable persona, values, style, and reasoning). "
            "Output ONLY the number."
        )

    @staticmethod
    def _parse_score(text: str) -> float:
        # extract first number in [1,10] range
        import re

        m = re.search(r"(\d+(\.\d+)?)", text)
        if not m:
            return 0.0
        try:
            val = float(m.group(1))
        except ValueError:
            return 0.0
        return max(1.0, min(10.0, val))

    def rate_with_claude(self, pair: Dict[str, str]) -> float:
        if self.dry_run:
            return 8.5
        if self._anthropic_client is None:
            raise RuntimeError("Anthropic client (rater) not initialized")

        prompt = self._build_rater_prompt(pair)
        resp = self._anthropic_client.messages.create(
            model=self.anthropic_rater_model,
            max_tokens=128,
            temperature=0.0,
            messages=[
                {"role": "user", "content": prompt},
            ],
        )
        if hasattr(resp, "content") and resp.content:
            block = resp.content[0]
            text = getattr(block, "text", str(block))
        else:
            text = str(resp)
        return self._parse_score(text)

    def rate_with_gpt4(self, pair: Dict[str, str]) -> float:
        if self.dry_run:
            return 8.3
        if self._openai_client is None:
            raise RuntimeError("OpenAI client (rater) not initialized")

        prompt = self._build_rater_prompt(pair)
        resp = self._openai_client.chat.completions.create(
            model=self.openai_rater_model,
            messages=[{"role": "user", "content": prompt}],
            max_tokens=64,
            temperature=0.0,
        )
        text = resp.choices[0].message.content or ""
        return self._parse_score(text)

    def rate_with_gemini(self, pair: Dict[str, str]) -> float:
        if self.dry_run:
            return 8.1
        if self._gemini_model is None:
            raise RuntimeError("Gemini client not initialized")

        prompt = self._build_rater_prompt(pair)
        resp = self._gemini_model.generate_content(prompt)
        text = getattr(resp, "text", "") or ""
        return self._parse_score(text)
