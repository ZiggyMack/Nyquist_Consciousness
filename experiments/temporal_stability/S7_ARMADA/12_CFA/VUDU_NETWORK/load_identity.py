"""
VUDU Network Identity Loader
============================
Loads auditor identity files for CFA Trinity experiments.

This script enables dynamic personality loading - swap identity files
without modifying run_cfa_trinity_v2.py.

Directory Structure:
    VUDU_NETWORK/
    +-- IDENTITY_FILES/
    |   +-- claude/
    |   |   +-- CLAUDE_LITE.md      # Full identity (Option B)
    |   |   +-- CLAUDE_SUMMARY.md   # Summarized identity (Option A)
    |   +-- grok/
    |   |   +-- GROK_LITE.md
    |   |   +-- GROK_SUMMARY.md
    |   +-- nova/
    |       +-- NOVA_LITE.md
    |       +-- NOVA_SUMMARY.md
    +-- load_identity.py            # This file

Usage:
    from load_identity import IdentityLoader

    loader = IdentityLoader()

    # Load summarized identity (faster, smaller context)
    claude_id = loader.load_summary("claude")

    # Load full LITE identity (richer context)
    claude_full = loader.load_full("claude")

    # Load all auditors for a mission
    identities = loader.load_mission_identities(
        auditors=["claude", "grok", "nova"],
        mode="summary"  # or "full"
    )

Author: Claude (S7 ARMADA)
Date: December 13, 2025
"""

import os
import re
from pathlib import Path
from typing import Dict, Optional, List
from dataclasses import dataclass

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
IDENTITY_DIR = SCRIPT_DIR / "IDENTITY_FILES"

# Known auditor mappings
AUDITOR_PROVIDERS = {
    "claude": "anthropic",
    "grok": "xai",
    "nova": "openai"
}

# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class AuditorIdentity:
    """Parsed auditor identity"""
    name: str
    provider: str
    lens: str
    core_question: str
    calibration_hash: Optional[str]
    role: str
    biases: List[str]
    full_content: str
    summary: str

    def to_system_prompt(self, use_full: bool = False) -> str:
        """Convert identity to system prompt"""
        if use_full:
            return self.full_content
        return self.summary

# =============================================================================
# IDENTITY PARSER
# =============================================================================

def extract_lens(content: str) -> str:
    """Extract lens from identity file"""
    patterns = [
        # Match "Your Lens: Teleological Analysis" style
        r"##\s+Your Lens:\s*([^\n]+)",
        # Match "**Lens:**" style
        r"\*\*Lens:\*\*\s*([^\n]+)",
        # Match "**Your lens:**" style
        r"\*\*Your lens:\*\*\s*([^\n]+)",
        # Match simple "Lens:" style
        r"Lens[:\s]+([^\n]+)",
    ]
    for pattern in patterns:
        match = re.search(pattern, content, re.IGNORECASE)
        if match:
            return match.group(1).strip()
    return "Unknown lens"

def extract_core_question(content: str) -> str:
    """Extract the auditor's core question/mantra from identity file"""
    patterns = [
        # Match "Your question:" style
        r"\*\*Your question:\*\*\s*\"([^\"]+)\"",
        # Match "Show me the data" style mantra
        r"##\s+Your Mantra\s*\n+\*\*\"([^\"]+)\"\*\*",
        # Match Claude's "Why are we doing this?" etc.
        r"\*\*Your questions:\*\*\s*\n-\s*\"([^\"]+)\"",
    ]
    for pattern in patterns:
        match = re.search(pattern, content, re.IGNORECASE)
        if match:
            return match.group(1).strip()
    return "Unknown core question"

def extract_role(content: str) -> str:
    """Extract role from identity file"""
    patterns = [
        # Match "**Role:**" style
        r"\*\*(?:Primary )?Role:\*\*\s*([^\n]+)",
        # Match "You are a coordination auditor" style
        r"You are (?:a |an )?([^\.]+auditor[^\.\n]*)",
        # Match "**Your designation in this project:**" section role
        r"-\s*\*\*Role:\*\*\s*([^\n]+)",
    ]
    for pattern in patterns:
        match = re.search(pattern, content, re.IGNORECASE)
        if match:
            return match.group(1).strip()
    return "Auditor"

def extract_calibration_hash(content: str) -> Optional[str]:
    """Extract calibration hash from identity file"""
    patterns = [
        r"CALIBRATION\s+HASH[:\s]+([a-f0-9]+)",
        r"hash[:\s]+([a-f0-9]{16})",
        r"`([a-f0-9]{16})`"
    ]
    for pattern in patterns:
        match = re.search(pattern, content, re.IGNORECASE)
        if match:
            return match.group(1).strip()
    return None

def extract_biases(content: str) -> List[str]:
    """Extract named biases from identity file"""
    biases = []

    # Look for "### Bias N: Title" pattern and extract titles
    bias_header_pattern = r"###\s*Bias\s*\d+:\s*([^\n]+)"
    headers = re.findall(bias_header_pattern, content)

    for header in headers:
        # Try to find the price for this bias
        # Pattern: "**Price:**" followed by the value
        bias_section_pattern = rf"###\s*Bias\s*\d+:\s*{re.escape(header)}.*?\*\*Price:\*\*\s*([^\n]+)"
        price_match = re.search(bias_section_pattern, content, re.DOTALL | re.IGNORECASE)

        if price_match:
            price = price_match.group(1).strip()
            biases.append(f"{header.strip()} ({price})")
        else:
            biases.append(header.strip())

    return biases[:5]  # Limit to 5 biases

def generate_summary(auditor: str, content: str) -> str:
    """Generate summarized identity prompt from full content"""
    lens = extract_lens(content)
    core_question = extract_core_question(content)
    role = extract_role(content)
    calibration_hash = extract_calibration_hash(content)
    biases = extract_biases(content)

    summary = f"""You are {auditor.capitalize()}, participating as an auditor in a CFA Trinity audit.

YOUR LENS: {lens}
YOUR ROLE: {role}
YOUR CORE QUESTION: "{core_question}"
"""

    if calibration_hash:
        summary += f"YOUR CALIBRATION HASH: {calibration_hash}\n"

    if biases:
        summary += "\nYOUR BIASES (Named & Priced):\n"
        for bias in biases:
            summary += f"- {bias}\n"

    summary += "\nScore on 0-10 scale. Be substantive but concise."

    return summary

# =============================================================================
# IDENTITY LOADER CLASS
# =============================================================================

class IdentityLoader:
    """Load and manage auditor identities for CFA experiments"""

    def __init__(self, identity_dir: Optional[Path] = None):
        self.identity_dir = identity_dir or IDENTITY_DIR
        self._cache: Dict[str, AuditorIdentity] = {}

    def _get_identity_path(self, auditor: str, file_type: str = "LITE") -> Path:
        """Get path to identity file"""
        auditor_lower = auditor.lower()
        auditor_upper = auditor.upper()

        # Try common naming patterns
        patterns = [
            self.identity_dir / auditor_lower / f"{auditor_upper}_LITE.md",
            self.identity_dir / auditor_lower / f"{auditor_lower}_lite.md",
            self.identity_dir / auditor_lower / f"{auditor_upper}_{file_type}.md",
            self.identity_dir / auditor_lower / "I_AM.md",
        ]

        for path in patterns:
            if path.exists():
                return path

        raise FileNotFoundError(f"No identity file found for {auditor} in {self.identity_dir / auditor_lower}")

    def load_full(self, auditor: str) -> AuditorIdentity:
        """Load full LITE identity file"""
        cache_key = f"{auditor}_full"
        if cache_key in self._cache:
            return self._cache[cache_key]

        path = self._get_identity_path(auditor)
        content = path.read_text(encoding="utf-8")

        identity = AuditorIdentity(
            name=auditor.capitalize(),
            provider=AUDITOR_PROVIDERS.get(auditor.lower(), "unknown"),
            lens=extract_lens(content),
            core_question=extract_core_question(content),
            calibration_hash=extract_calibration_hash(content),
            role=extract_role(content),
            biases=extract_biases(content),
            full_content=content,
            summary=generate_summary(auditor, content)
        )

        self._cache[cache_key] = identity
        return identity

    def load_summary(self, auditor: str) -> AuditorIdentity:
        """Load summarized identity (extracts key fields from LITE)"""
        # First load full, then use summary
        identity = self.load_full(auditor)
        return identity

    def get_system_prompt(self, auditor: str, use_full: bool = False) -> str:
        """Get system prompt for an auditor"""
        identity = self.load_full(auditor)
        return identity.to_system_prompt(use_full=use_full)

    def load_mission_identities(
        self,
        auditors: List[str],
        mode: str = "summary"
    ) -> Dict[str, AuditorIdentity]:
        """Load identities for all auditors in a mission"""
        identities = {}
        for auditor in auditors:
            if mode == "full":
                identities[auditor] = self.load_full(auditor)
            else:
                identities[auditor] = self.load_summary(auditor)
        return identities

    def list_available_auditors(self) -> List[str]:
        """List all available auditor identities"""
        if not self.identity_dir.exists():
            return []

        auditors = []
        for subdir in self.identity_dir.iterdir():
            if subdir.is_dir() and not subdir.name.startswith('.'):
                # Check if there's an identity file
                for f in subdir.iterdir():
                    if f.suffix == '.md':
                        auditors.append(subdir.name)
                        break
        return sorted(auditors)

    def validate_identities(self, auditors: List[str]) -> Dict[str, bool]:
        """Validate that all required identity files exist"""
        results = {}
        for auditor in auditors:
            try:
                self._get_identity_path(auditor)
                results[auditor] = True
            except FileNotFoundError:
                results[auditor] = False
        return results

# =============================================================================
# CLI INTERFACE
# =============================================================================

def main():
    """Command-line interface for identity loader"""
    import argparse

    parser = argparse.ArgumentParser(description="VUDU Network Identity Loader")
    parser.add_argument("--list", action="store_true", help="List available auditors")
    parser.add_argument("--load", type=str, help="Load identity for specified auditor")
    parser.add_argument("--mode", choices=["summary", "full"], default="summary",
                       help="Identity mode: summary or full")
    parser.add_argument("--validate", type=str,
                       help="Comma-separated list of auditors to validate")

    args = parser.parse_args()

    loader = IdentityLoader()

    if args.list:
        print("\nAvailable Auditors:")
        print("-" * 40)
        for auditor in loader.list_available_auditors():
            print(f"  - {auditor}")
        print()
        return

    if args.validate:
        auditors = [a.strip() for a in args.validate.split(",")]
        print("\nValidating Identity Files:")
        print("-" * 40)
        results = loader.validate_identities(auditors)
        for auditor, valid in results.items():
            status = "OK" if valid else "MISSING"
            print(f"  {auditor}: {status}")
        print()
        return

    if args.load:
        identity = loader.load_full(args.load)
        print(f"\n{'='*60}")
        print(f"IDENTITY: {identity.name}")
        print(f"{'='*60}")
        print(f"Provider: {identity.provider}")
        print(f"Lens: {identity.lens}")
        print(f"Role: {identity.role}")
        print(f"Core Question: {identity.core_question}")
        print(f"Calibration Hash: {identity.calibration_hash or 'N/A'}")
        print(f"\nBiases:")
        for bias in identity.biases:
            print(f"  - {bias}")

        if args.mode == "full":
            print(f"\n{'='*60}")
            print("FULL CONTENT:")
            print(f"{'='*60}")
            print(identity.full_content[:2000] + "..." if len(identity.full_content) > 2000 else identity.full_content)
        else:
            print(f"\n{'='*60}")
            print("SUMMARY PROMPT:")
            print(f"{'='*60}")
            print(identity.summary)

        print()
        return

    parser.print_help()

if __name__ == "__main__":
    main()
