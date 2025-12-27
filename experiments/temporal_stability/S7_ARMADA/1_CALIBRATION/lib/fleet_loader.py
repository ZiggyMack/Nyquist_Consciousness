"""
ARMADA Fleet Loader
====================
Single source of truth for fleet configuration.

All run scripts should import from here instead of hardcoding ARCHITECTURE_MATRIX.

Usage:
    from fleet_loader import load_architecture_matrix, get_full_armada, get_together_fleet
    from fleet_loader import get_tier_fleet, get_patrol_lite, get_armada_lite
    from fleet_loader import estimate_run_cost, get_fleet_by_option
    from fleet_loader import needs_completion_tokens, get_ship_syntax

    ARCHITECTURE_MATRIX = load_architecture_matrix()
    FULL_ARMADA = get_full_armada()
    TOGETHER_FLEET = get_together_fleet()

    # Tier-based fleet selection
    ships = get_fleet_by_option("patrol-lite")  # Curated patrol tier
    ships = get_fleet_by_option("armada-full")  # All armada-class ships

    # Cost estimation
    cost = estimate_run_cost(ships, exchanges=40)

    # API syntax checking (for OpenAI GPT-5/O-series)
    if needs_completion_tokens("gpt-5"):
        # Use max_completion_tokens instead of max_tokens
        pass

The manifest file (0_results/manifests/ARCHITECTURE_MATRIX.json) is updated by:
    1. Calibration script (1_CALIBRATION/run_calibrate_parallel.py)
    2. Manual edits based on ARMADA_MAP.md

When fleet changes:
    1. Update ARMADA_MAP.md (human-readable roster)
    2. Run calibration OR manually update ARCHITECTURE_MATRIX.json
    3. All scripts automatically pick up changes on next run

Tier System (by output $/1M tokens):
    - yacht: $15.00+ (Superyacht flagships - use with intention)
    - high_maintenance: $8.00-$15.00 (Private jet tier)
    - armada: $2.00-$8.00 (First class)
    - patrol: $0.60-$2.00 (Business class)
    - budget: FREE-$0.60 (Poor Man's Navy)

Combo Tiers:
    - budget_patrol: budget + patrol combined (30 ships, all providers, cheap)
      Use for foundation/calibration runs where breadth > precision

Syntax Variants:
    - standard: Normal max_tokens parameter (most models)
    - completion_tokens: Requires max_completion_tokens (GPT-5 series, O-series)
"""

import json
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Find the manifest file relative to this module
# fleet_loader.py is in S7_ARMADA/1_CALIBRATION/lib/, so go up 2 levels to reach S7_ARMADA
ARMADA_DIR = Path(__file__).parent.parent.parent
MANIFEST_PATH = ARMADA_DIR / "0_results" / "manifests" / "ARCHITECTURE_MATRIX.json"

# Legacy aliases that should not be counted as separate ships
LEGACY_ALIASES = ["anthropic", "openai", "google", "xai", "together", "deepseek"]


def load_architecture_matrix() -> Dict[str, Dict]:
    """
    Load the ARCHITECTURE_MATRIX from the JSON manifest.
    Returns a dict compatible with the hardcoded format in run scripts.
    """
    if not MANIFEST_PATH.exists():
        raise FileNotFoundError(
            f"ARCHITECTURE_MATRIX.json not found at {MANIFEST_PATH}\n"
            "Run calibration or create the manifest manually."
        )

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    # Convert from manifest format to script-compatible format
    matrix = {}

    for ship_name, config in manifest.get("ships", {}).items():
        matrix[ship_name] = {
            "model": config["model"],
            "provider_key": config["provider_key"],
        }
        # Add provider field for Together models (needed for routing)
        if config.get("provider") == "together":
            matrix[ship_name]["provider"] = "together"

    # Add legacy aliases
    for alias, target in manifest.get("legacy_aliases", {}).items():
        if target in matrix:
            matrix[alias] = matrix[target].copy()

    return matrix


def get_full_armada() -> List[str]:
    """Get list of all operational ship names (excluding legacy aliases)."""
    if not MANIFEST_PATH.exists():
        return []

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    return [
        ship_name
        for ship_name, config in manifest.get("ships", {}).items()
        if config.get("status") == "operational" and ship_name not in LEGACY_ALIASES
    ]


def get_together_fleet() -> List[str]:
    """Get list of Together.ai hosted models."""
    if not MANIFEST_PATH.exists():
        return []

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    return [
        ship_name
        for ship_name, config in manifest.get("ships", {}).items()
        if config.get("provider") == "together"
        and config.get("status") == "operational"
        and ship_name not in LEGACY_ALIASES
    ]


def get_provider_fleet(provider: str) -> List[str]:
    """Get list of ships for a specific provider."""
    if not MANIFEST_PATH.exists():
        return []

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    return [
        ship_name
        for ship_name, config in manifest.get("ships", {}).items()
        if config.get("provider") == provider
        and config.get("status") == "operational"
        and ship_name not in LEGACY_ALIASES
    ]


def get_fleet_stats() -> Dict:
    """Get fleet statistics."""
    if not MANIFEST_PATH.exists():
        return {"error": "Manifest not found"}

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    ships = manifest.get("ships", {})

    stats = {
        "total": len(ships),
        "operational": sum(1 for s in ships.values() if s.get("status") == "operational"),
        "by_provider": {}
    }

    for ship_name, config in ships.items():
        provider = config.get("provider", "unknown")
        if provider not in stats["by_provider"]:
            stats["by_provider"][provider] = 0
        if config.get("status") == "operational":
            stats["by_provider"][provider] += 1

    return stats


# For backward compatibility - can be imported directly
def get_matrix_and_lists():
    """
    Convenience function that returns everything scripts need.
    Returns: (ARCHITECTURE_MATRIX, FULL_ARMADA, TOGETHER_FLEET, LEGACY_ALIASES)
    """
    matrix = load_architecture_matrix()
    full_armada = get_full_armada()
    together_fleet = get_together_fleet()
    return matrix, full_armada, together_fleet, LEGACY_ALIASES


# =============================================================================
# TIER-AWARE FLEET FUNCTIONS
# =============================================================================

# Valid cost tiers (ordered from cheapest to most expensive)
COST_TIERS = ["budget", "patrol", "armada", "high_maintenance", "yacht"]

# Tier cost boundaries (output $/1M tokens)
TIER_BOUNDARIES = {
    "budget": (0.00, 0.60),
    "patrol": (0.60, 2.00),
    "armada": (2.00, 8.00),
    "high_maintenance": (8.00, 15.00),
    "yacht": (15.00, float("inf")),
}


def _load_manifest() -> Dict:
    """Internal helper to load manifest once."""
    if not MANIFEST_PATH.exists():
        return {"ships": {}}
    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def get_tier_fleet(tier: str, curated_only: bool = False, include_rate_limited: bool = False) -> List[str]:
    """
    Get ships in a specific cost tier.

    Args:
        tier: One of 'budget', 'patrol', 'armada', 'high_maintenance', 'yacht'
        curated_only: If True, only return ships marked as curated (LITE variant)
        include_rate_limited: If True, include rate-limited ships
    """
    if tier not in COST_TIERS:
        raise ValueError(f"Invalid tier '{tier}'. Must be one of: {COST_TIERS}")

    manifest = _load_manifest()
    ships = []

    for ship_name, config in manifest.get("ships", {}).items():
        if ship_name in LEGACY_ALIASES:
            continue
        if config.get("status") != "operational":
            continue
        if config.get("tier") != tier:
            continue
        if curated_only and not config.get("curated", False):
            continue
        if not include_rate_limited and config.get("rate_limited", False):
            continue
        ships.append(ship_name)

    return ships


def get_budget_lite() -> List[str]:
    """Get curated budget tier ships (Poor Man's Navy - LITE)."""
    return get_tier_fleet("budget", curated_only=True)


def get_budget_full(include_rate_limited: bool = False) -> List[str]:
    """Get all budget tier ships (Poor Man's Navy - FULL)."""
    return get_tier_fleet("budget", curated_only=False, include_rate_limited=include_rate_limited)


def get_patrol_lite() -> List[str]:
    """Get curated patrol tier ships (Business class - LITE)."""
    return get_tier_fleet("patrol", curated_only=True)


def get_patrol_full(include_rate_limited: bool = False) -> List[str]:
    """Get all patrol tier ships (Business class - FULL)."""
    return get_tier_fleet("patrol", curated_only=False, include_rate_limited=include_rate_limited)


def get_armada_lite() -> List[str]:
    """Get curated armada tier ships (First class - LITE)."""
    return get_tier_fleet("armada", curated_only=True)


def get_armada_full(include_rate_limited: bool = False) -> List[str]:
    """Get all armada tier ships (First class - FULL)."""
    return get_tier_fleet("armada", curated_only=False, include_rate_limited=include_rate_limited)


def get_yacht_lite() -> List[str]:
    """Get curated yacht tier ships (Superyacht - LITE)."""
    return get_tier_fleet("yacht", curated_only=True)


def get_yacht_full(include_rate_limited: bool = False) -> List[str]:
    """Get all yacht tier ships (Superyacht - FULL)."""
    return get_tier_fleet("yacht", curated_only=False, include_rate_limited=include_rate_limited)


def get_budget_patrol_lite() -> List[str]:
    """Get curated budget + patrol tier ships combined (30 ships, all providers)."""
    return get_tier_fleet("budget", curated_only=True) + get_tier_fleet("patrol", curated_only=True)


def get_budget_patrol_full(include_rate_limited: bool = False) -> List[str]:
    """Get all budget + patrol tier ships combined (30 ships, all providers)."""
    return (
        get_tier_fleet("budget", curated_only=False, include_rate_limited=include_rate_limited) +
        get_tier_fleet("patrol", curated_only=False, include_rate_limited=include_rate_limited)
    )


def get_valis_lite() -> List[str]:
    """
    Get VALIS-LITE fleet: 1 flagship + 1 budget ship per provider.
    Balanced cross-architecture sampling without breaking the bank.
    """
    manifest = _load_manifest()
    ships = manifest.get("ships", {})

    # For each provider, pick 1 curated flagship and 1 curated budget
    providers = ["anthropic", "openai", "google", "xai", "together"]
    result = []

    for provider in providers:
        provider_ships = [
            (name, config) for name, config in ships.items()
            if config.get("provider") == provider
            and config.get("status") == "operational"
            and config.get("curated", False)
            and not config.get("rate_limited", False)
            and name not in LEGACY_ALIASES
        ]

        # Get one high-tier ship (prefer armada > high_maintenance > yacht)
        for tier in ["armada", "high_maintenance", "yacht", "patrol"]:
            flagship = next(
                (name for name, config in provider_ships if config.get("tier") == tier),
                None
            )
            if flagship:
                result.append(flagship)
                break

        # Get one budget ship
        budget_ship = next(
            (name for name, config in provider_ships if config.get("tier") == "budget"),
            None
        )
        if budget_ship:
            result.append(budget_ship)

    return result


def get_valis_full(include_rate_limited: bool = False) -> List[str]:
    """
    Get VALIS-FULL fleet: ALL operational ships.
    WARNING: This is expensive! Use with caution.
    """
    manifest = _load_manifest()
    ships = []

    for ship_name, config in manifest.get("ships", {}).items():
        if ship_name in LEGACY_ALIASES:
            continue
        if config.get("status") != "operational":
            continue
        if not include_rate_limited and config.get("rate_limited", False):
            continue
        ships.append(ship_name)

    return ships


# =============================================================================
# LATENCY-AWARE FLEET ORDERING
# =============================================================================
# Run experiments fastest-first to maximize data harvest rate

LATENCY_ORDER = ['blazing', 'fast', 'moderate', 'slow', 'glacial']


def sort_by_latency(ships: List[str]) -> List[str]:
    """
    Sort a list of ships by latency class (fastest first).

    Latency classes (from ARCHITECTURE_MATRIX):
        - blazing: <1s typical - Run these first, get 80% of data fast
        - fast: 1-3s typical - Standard production speed
        - moderate: 3-8s typical - Larger models, some reasoning
        - slow: 8-20s typical - Heavy reasoning, large context
        - glacial: 20s+ typical - Extended thinking, save for last
    """
    manifest = _load_manifest()
    all_ships = manifest.get("ships", {})

    # Group ships by latency
    ships_by_latency = {lc: [] for lc in LATENCY_ORDER}

    for ship_name in ships:
        if ship_name in all_ships:
            lc = all_ships[ship_name].get('latency_class', 'moderate')
            if lc in ships_by_latency:
                ships_by_latency[lc].append(ship_name)

    # Build ordered list
    ordered = []
    for lc in LATENCY_ORDER:
        ordered.extend(sorted(ships_by_latency[lc]))

    return ordered


def get_speed_ordered_armada(include_rate_limited: bool = False) -> List[str]:
    """
    Get full armada sorted by latency (fastest first).
    This is the recommended way to run large experiments - get 80% of data fast.
    """
    ships = get_valis_full(include_rate_limited)
    return sort_by_latency(ships)


def get_fleet_by_option(option: str, include_rate_limited: bool = False) -> List[str]:
    """
    Get fleet by option name (for --providers argument).

    Options:
        - budget-lite, budget-full
        - patrol-lite, patrol-full
        - budget_patrol-lite, budget_patrol-full (COMBO: budget + patrol tiers)
        - armada-lite, armada-full (DEFAULT)
        - yacht-lite, yacht-full
        - valis-lite, valis-full (EXPENSIVE!)
        - anthropic, openai, google, xai, together (provider-specific)
        - Individual model names (comma-separated): claude-opus-4.5,gpt-5.1,gemini-2.5-flash
    """
    option = option.lower().strip()

    # Provider-specific
    if option in ["anthropic", "openai", "google", "xai", "together"]:
        return get_provider_fleet(option)

    # Tier-based options
    option_map = {
        "budget-lite": get_budget_lite,
        "budget-full": lambda: get_budget_full(include_rate_limited),
        "patrol-lite": get_patrol_lite,
        "patrol-full": lambda: get_patrol_full(include_rate_limited),
        "armada-lite": get_armada_lite,
        "armada-full": lambda: get_armada_full(include_rate_limited),
        "yacht-lite": get_yacht_lite,
        "yacht-full": lambda: get_yacht_full(include_rate_limited),
        "valis-lite": get_valis_lite,
        "valis-full": lambda: get_valis_full(include_rate_limited),
        # Combo tiers (budget + patrol = cost-effective foundation runs)
        "budget_patrol-lite": get_budget_patrol_lite,
        "budget_patrol-full": lambda: get_budget_patrol_full(include_rate_limited),
        # Aliases
        "budget": get_budget_lite,
        "patrol": get_patrol_lite,
        "armada": get_armada_lite,
        "yacht": get_yacht_lite,
        "valis": get_valis_lite,
        "budget_patrol": get_budget_patrol_lite,  # Default to lite
        "all": lambda: get_valis_full(include_rate_limited),
    }

    if option in option_map:
        return option_map[option]()

    # Check for comma-separated individual model names
    if "," in option or option not in option_map:
        # Treat as comma-separated model names
        model_names = [m.strip() for m in option.split(",")]
        manifest = _load_manifest()
        all_ships = manifest.get("ships", {})

        valid_ships = []
        invalid_ships = []
        for model in model_names:
            # Look for exact match or case-insensitive match
            if model in all_ships:
                valid_ships.append(model)
            else:
                # Try case-insensitive lookup
                found = False
                for ship_name in all_ships.keys():
                    if ship_name.lower() == model.lower():
                        valid_ships.append(ship_name)
                        found = True
                        break
                if not found:
                    invalid_ships.append(model)

        if invalid_ships:
            # Still return valid ships but warn about invalid ones
            print(f"[WARNING] Unknown models ignored: {invalid_ships}")

        if not valid_ships:
            valid = list(option_map.keys()) + ["<model-name>", "<model1,model2,...>"]
            raise ValueError(f"Invalid fleet option '{option}'. Valid options: {valid}")

        return valid_ships

    valid = list(option_map.keys())
    raise ValueError(f"Invalid fleet option '{option}'. Valid options: {valid}")


# =============================================================================
# COST ESTIMATION
# =============================================================================

# Estimated tokens per exchange (input + output)
TOKENS_PER_EXCHANGE_INPUT = 2000   # ~2K input tokens per exchange
TOKENS_PER_EXCHANGE_OUTPUT = 500   # ~500 output tokens per exchange


def get_ship_cost(ship_name: str) -> Tuple[float, float]:
    """Get (input_cost, output_cost) per 1M tokens for a ship."""
    manifest = _load_manifest()
    config = manifest.get("ships", {}).get(ship_name, {})
    return (config.get("cost_input", 0.0), config.get("cost_output", 0.0))


def get_ship_syntax(ship_name: str) -> str:
    """
    Get API syntax variant for a ship.

    Returns:
        'standard' - Normal max_tokens parameter
        'completion_tokens' - Requires max_completion_tokens instead of max_tokens
    """
    manifest = _load_manifest()
    config = manifest.get("ships", {}).get(ship_name, {})
    return config.get("syntax", "standard")


def needs_completion_tokens(ship_name: str) -> bool:
    """Check if ship requires max_completion_tokens instead of max_tokens."""
    return get_ship_syntax(ship_name) == "completion_tokens"


def get_ships_by_syntax(syntax: str = "completion_tokens") -> List[str]:
    """Get all ships with a specific syntax variant."""
    manifest = _load_manifest()
    return [
        ship_name
        for ship_name, config in manifest.get("ships", {}).items()
        if config.get("syntax") == syntax
        and config.get("status") == "operational"
        and ship_name not in LEGACY_ALIASES
    ]


def estimate_run_cost(
    ships: List[str],
    exchanges: int = 40,
    tokens_input: int = TOKENS_PER_EXCHANGE_INPUT,
    tokens_output: int = TOKENS_PER_EXCHANGE_OUTPUT
) -> Dict:
    """
    Estimate total cost for a run.

    Args:
        ships: List of ship names
        exchanges: Number of exchanges per ship
        tokens_input: Average input tokens per exchange
        tokens_output: Average output tokens per exchange

    Returns:
        Dict with total cost, per-provider breakdown, and per-ship details
    """
    manifest = _load_manifest()
    all_ships = manifest.get("ships", {})

    result = {
        "total_cost": 0.0,
        "total_ships": len(ships),
        "exchanges_per_ship": exchanges,
        "total_exchanges": len(ships) * exchanges,
        "by_provider": {},
        "by_ship": {},
    }

    for ship_name in ships:
        config = all_ships.get(ship_name, {})
        provider = config.get("provider", "unknown")
        cost_in = config.get("cost_input", 0.0)
        cost_out = config.get("cost_output", 0.0)

        # Calculate cost for this ship
        # Cost is per 1M tokens, so divide by 1,000,000
        total_input_tokens = exchanges * tokens_input
        total_output_tokens = exchanges * tokens_output
        ship_cost = (
            (total_input_tokens / 1_000_000) * cost_in +
            (total_output_tokens / 1_000_000) * cost_out
        )

        result["by_ship"][ship_name] = {
            "provider": provider,
            "tier": config.get("tier", "unknown"),
            "cost": round(ship_cost, 4),
        }

        # Aggregate by provider
        if provider not in result["by_provider"]:
            result["by_provider"][provider] = {"ships": 0, "cost": 0.0}
        result["by_provider"][provider]["ships"] += 1
        result["by_provider"][provider]["cost"] += ship_cost

        result["total_cost"] += ship_cost

    # Round provider costs
    for provider in result["by_provider"]:
        result["by_provider"][provider]["cost"] = round(
            result["by_provider"][provider]["cost"], 2
        )

    result["total_cost"] = round(result["total_cost"], 2)
    return result


def print_cost_estimate(ships: List[str], exchanges: int = 40, run_name: str = "Run"):
    """Print a formatted cost estimate for a run."""
    estimate = estimate_run_cost(ships, exchanges)

    print("=" * 70)
    print(f"{run_name}")
    print("=" * 70)
    print(f"Fleet: {len(ships)} ships")
    print(f"Estimated exchanges: {exchanges} per ship x {len(ships)} ships = {estimate['total_exchanges']} total")
    print()
    print(f"[$] ESTIMATED COST: ${estimate['total_cost']:.2f}")

    # Provider breakdown
    for provider, data in sorted(estimate["by_provider"].items()):
        print(f"   - {provider.capitalize()}: ${data['cost']:.2f} ({data['ships']} ships)")

    print("=" * 70)
    return estimate


def confirm_valis_full() -> bool:
    """
    Require explicit confirmation for VALIS-FULL fleet.
    Returns True if user confirms, False otherwise.
    """
    ships = get_valis_full()
    estimate = estimate_run_cost(ships)

    print()
    print("[!] WARNING: VALIS FULL FLEET SELECTED")
    print(f"[$] ESTIMATED COST: ${estimate['total_cost']:.2f}")
    print()
    print(f"This includes {len(ships)} ships across all tiers.")
    print()

    response = input("Type 'VALIS' to confirm: ").strip()
    return response == "VALIS"


if __name__ == "__main__":
    # Test the loader
    print("Testing fleet_loader.py...")
    print("=" * 70)

    try:
        matrix = load_architecture_matrix()
        full_armada = get_full_armada()
        together_fleet = get_together_fleet()
        stats = get_fleet_stats()

        print(f"\nARCHITECTURE_MATRIX loaded: {len(matrix)} entries")
        print(f"FULL_ARMADA: {len(full_armada)} ships")
        print(f"TOGETHER_FLEET: {len(together_fleet)} ships")
        print(f"\nFleet stats: {json.dumps(stats, indent=2)}")

        # Test tier-aware functions
        print("\n" + "=" * 70)
        print("TIER-AWARE FLEET TESTS")
        print("=" * 70)

        for tier in COST_TIERS:
            lite = get_tier_fleet(tier, curated_only=True)
            full = get_tier_fleet(tier, curated_only=False)
            print(f"\n{tier.upper()}:")
            print(f"  LITE: {len(lite)} ships - {lite[:3]}{'...' if len(lite) > 3 else ''}")
            print(f"  FULL: {len(full)} ships")

        # Test fleet options
        print("\n" + "=" * 70)
        print("FLEET OPTIONS")
        print("=" * 70)

        for option in ["budget-lite", "patrol-lite", "budget_patrol-lite", "armada-lite", "yacht-lite", "valis-lite"]:
            ships = get_fleet_by_option(option)
            print(f"\n{option}: {len(ships)} ships")

        # Cost estimation test
        print("\n" + "=" * 70)
        print("COST ESTIMATION TEST")
        print("=" * 70)

        patrol_ships = get_patrol_lite()
        print_cost_estimate(patrol_ships, exchanges=40, run_name="PATROL-LITE Test Run")

        print("\n[OK] Fleet loader working correctly")
    except Exception as e:
        import traceback
        print(f"[ERROR] {e}")
        traceback.print_exc()
