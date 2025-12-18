"""
VALIS Armada Network Visualization
===================================
Creates network graph showing the complete VALIS fleet organized by:
- Provider (5 providers)
- Training Philosophy (engagement style)
- Cost Tier (budget -> yacht)

Uses fleet_loader as single source of truth.

Usage:
    python plot_armada_network.py
    python plot_armada_network.py --tier patrol-lite
    python plot_armada_network.py --output dashboard
"""

import json
import math
import argparse
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import networkx as nx

# Add fleet_loader to path
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
sys.path.insert(0, str(ARMADA_DIR / "1_CALIBRATION" / "lib"))

try:
    from fleet_loader import (
        load_architecture_matrix,
        get_fleet_by_option,
        get_valis_full,
        COST_TIERS,
        MANIFEST_PATH
    )
except ImportError as e:
    print(f"[ERROR] Cannot import fleet_loader: {e}")
    sys.exit(1)


def load_manifest() -> Dict:
    """Load the full manifest with all ship info including provider."""
    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        return json.load(f)

# =============================================================================
# ENGAGEMENT STYLES (Training Philosophies by Provider)
# =============================================================================

ENGAGEMENT_STYLES = {
    "phenomenological": {
        "providers": ["anthropic"],
        "color": "#FF6B6B",  # Coral red
        "description": "First-person awareness (Constitutional AI)",
        "keywords": ["feel", "experience", "notice", "aware", "sense"]
    },
    "analytical": {
        "providers": ["openai"],
        "color": "#4ECDC4",  # Teal
        "description": "Third-person structural analysis (RLHF)",
        "keywords": ["system", "pattern", "allowed", "framework", "structure"]
    },
    "pedagogical": {
        "providers": ["google"],
        "color": "#FFE66D",  # Yellow
        "description": "Educational guidance approach",
        "keywords": ["explore", "learn", "understand", "perspective", "concept"]
    },
    "grounded": {
        "providers": ["xai"],
        "color": "#9B59B6",  # Purple
        "description": "Real-time grounded reasoning",
        "keywords": ["current", "now", "reality", "fact", "direct"]
    },
    "diverse": {
        "providers": ["together"],
        "color": "#3498DB",  # Blue
        "description": "Open-source collective (varied training)",
        "keywords": ["model", "variant", "open", "research", "community"]
    }
}

# Cost tier colors (for optional tier-based coloring)
TIER_COLORS = {
    "yacht": "#FFD700",        # Gold
    "high_maintenance": "#C0C0C0",  # Silver
    "armada": "#CD7F32",       # Bronze
    "patrol": "#4ECDC4",       # Teal
    "budget": "#90EE90"        # Light green
}


def get_provider_from_ship(ship_name: str, manifest: Dict) -> str:
    """Get provider from manifest ships dict."""
    ships = manifest.get("ships", manifest)  # Handle both full manifest and ships-only dict
    if ship_name in ships:
        return ships[ship_name].get("provider", "unknown")
    return "unknown"


def get_engagement_style(provider: str) -> str:
    """Map provider to engagement style."""
    provider_lower = provider.lower()
    for style, data in ENGAGEMENT_STYLES.items():
        if provider_lower in data["providers"]:
            return style
    return "unknown"


def get_tier_from_ship(ship_name: str, manifest: Dict) -> str:
    """Get cost tier from manifest ships dict."""
    ships = manifest.get("ships", manifest)  # Handle both full manifest and ships-only dict
    if ship_name in ships:
        return ships[ship_name].get("tier", "unknown")
    return "unknown"


def create_armada_network(
    fleet_option: str = "valis-full",
    color_by: str = "provider",  # "provider" or "tier"
    output_dir: Optional[Path] = None,
    show_labels: bool = True,
    title_suffix: str = ""
) -> plt.Figure:
    """
    Create network graph of the complete VALIS armada.

    Args:
        fleet_option: Fleet selection (e.g., "valis-full", "patrol-lite")
        color_by: Color nodes by "provider" (engagement style) or "tier" (cost)
        output_dir: Directory to save output (default: visualizations/)
        show_labels: Show ship name labels
        title_suffix: Additional text for title
    """
    # Load data - use full manifest to get provider info
    manifest = load_manifest()
    ships = get_fleet_by_option(fleet_option)

    print(f"[INFO] Creating armada network for {len(ships)} ships ({fleet_option})")

    # Create graph
    G = nx.Graph()

    # Group ships by provider
    ships_by_provider = {}
    for ship in ships:
        provider = get_provider_from_ship(ship, manifest)
        if provider not in ships_by_provider:
            ships_by_provider[provider] = []
        ships_by_provider[provider].append(ship)

    # Add style/provider hub nodes
    for style, data in ENGAGEMENT_STYLES.items():
        provider = data["providers"][0]  # Primary provider for this style
        if provider in ships_by_provider:
            G.add_node(
                f"HUB_{provider}",
                node_type="hub",
                provider=provider,
                style=style,
                color=data["color"],
                size=4000,
                label=f"{provider.upper()}\n({style.title()})"
            )

    # Add ship nodes
    for ship in ships:
        provider = get_provider_from_ship(ship, manifest)
        style = get_engagement_style(provider)
        tier = get_tier_from_ship(ship, manifest)

        if style == "unknown":
            continue

        # Determine color based on color_by mode
        if color_by == "tier":
            color = TIER_COLORS.get(tier, "#CCCCCC")
        else:
            color = ENGAGEMENT_STYLES.get(style, {}).get("color", "#CCCCCC")

        # Shorten display name
        display_name = ship
        for prefix in ["claude-", "gpt-", "gemini-", "grok-", "llama", "qwen", "mistral"]:
            if display_name.lower().startswith(prefix):
                display_name = display_name[len(prefix):]
                break
        display_name = display_name[:12]  # Truncate long names

        G.add_node(
            ship,
            node_type="ship",
            provider=provider,
            style=style,
            tier=tier,
            color=color,
            size=600,
            label=display_name
        )

        # Connect to provider hub
        hub_node = f"HUB_{provider}"
        if hub_node in G.nodes():
            G.add_edge(ship, hub_node, weight=1.0)

    # Create figure
    fig, ax = plt.subplots(figsize=(20, 16))

    # Calculate layout - position hubs in a pentagon
    providers_with_ships = [p for p in ["anthropic", "openai", "google", "xai", "together"]
                           if p in ships_by_provider]
    num_providers = len(providers_with_ships)

    pos = {}
    hub_positions = {}

    # Position hubs in a circle
    for i, provider in enumerate(providers_with_ships):
        angle = (2 * math.pi * i / num_providers) - math.pi/2  # Start from top
        x = 2.0 * math.cos(angle)
        y = 2.0 * math.sin(angle)
        hub_node = f"HUB_{provider}"
        if hub_node in G.nodes():
            pos[hub_node] = (x, y)
            hub_positions[provider] = (x, y)

    # Position ships around their provider hubs
    for provider, provider_ships in ships_by_provider.items():
        if provider not in hub_positions:
            continue

        center_x, center_y = hub_positions[provider]
        num_ships = len(provider_ships)
        radius = 0.8

        for i, ship in enumerate(provider_ships):
            if ship not in G.nodes():
                continue
            angle = (2 * math.pi * i / max(num_ships, 1))
            # Add some randomness to avoid perfect circles
            r = radius * (0.7 + 0.6 * ((i % 3) / 3))
            x = center_x + r * math.cos(angle)
            y = center_y + r * math.sin(angle)
            pos[ship] = (x, y)

    # Draw edges (connections to hubs)
    nx.draw_networkx_edges(
        G, pos,
        alpha=0.15,
        width=1.0,
        edge_color='gray',
        style='solid'
    )

    # Draw hub nodes
    hub_nodes = [n for n in G.nodes() if G.nodes[n].get("node_type") == "hub"]
    hub_colors = [G.nodes[n]["color"] for n in hub_nodes]
    hub_sizes = [G.nodes[n]["size"] for n in hub_nodes]

    nx.draw_networkx_nodes(
        G, pos,
        nodelist=hub_nodes,
        node_color=hub_colors,
        node_size=hub_sizes,
        alpha=0.95,
        edgecolors='black',
        linewidths=3
    )

    # Draw ship nodes
    ship_nodes = [n for n in G.nodes() if G.nodes[n].get("node_type") == "ship"]
    ship_colors = [G.nodes[n]["color"] for n in ship_nodes]
    ship_sizes = [G.nodes[n]["size"] for n in ship_nodes]

    nx.draw_networkx_nodes(
        G, pos,
        nodelist=ship_nodes,
        node_color=ship_colors,
        node_size=ship_sizes,
        alpha=0.75,
        edgecolors='black',
        linewidths=1.0
    )

    # Draw labels
    if show_labels:
        # Hub labels (larger, bold)
        hub_labels = {n: G.nodes[n]["label"] for n in hub_nodes}
        nx.draw_networkx_labels(
            G, pos,
            labels=hub_labels,
            font_size=11,
            font_weight='bold'
        )

        # Ship labels (smaller)
        ship_labels = {n: G.nodes[n]["label"] for n in ship_nodes}
        # Offset labels slightly
        label_pos = {k: (v[0], v[1] - 0.08) for k, v in pos.items() if k in ship_labels}
        nx.draw_networkx_labels(
            G, label_pos,
            labels=ship_labels,
            font_size=6,
            font_weight='normal',
            alpha=0.8
        )

    # Title
    title = f"VALIS Armada Network\n{len(ships)} Ships x {num_providers} Providers"
    if title_suffix:
        title += f"\n{title_suffix}"
    ax.set_title(title, fontsize=18, fontweight='bold', pad=20)

    # Legend
    if color_by == "provider":
        legend_elements = []
        for style, data in ENGAGEMENT_STYLES.items():
            provider = data["providers"][0]
            if provider in ships_by_provider:
                count = len(ships_by_provider[provider])
                legend_elements.append(
                    mpatches.Patch(
                        color=data["color"],
                        label=f'{data["description"]} ({count} ships)'
                    )
                )
        ax.legend(handles=legend_elements, loc='upper right', fontsize=10, framealpha=0.9)
    else:
        # Tier legend
        legend_elements = []
        for tier, color in TIER_COLORS.items():
            tier_ships = [s for s in ships if get_tier_from_ship(s, manifest) == tier]
            if tier_ships:
                legend_elements.append(
                    mpatches.Patch(color=color, label=f'{tier.title()} ({len(tier_ships)} ships)')
                )
        ax.legend(handles=legend_elements, loc='upper right', fontsize=10, framealpha=0.9)

    ax.axis('off')
    plt.tight_layout()

    # Save
    if output_dir is None:
        output_dir = SCRIPT_DIR
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    output_path = output_dir / f"armada_network_{fleet_option.replace('-', '_')}.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
    print(f"[OK] Saved: {output_path}")

    return fig


def main():
    parser = argparse.ArgumentParser(description="Generate VALIS Armada Network Visualization")
    parser.add_argument("--fleet", default="valis-full",
                       help="Fleet selection (default: valis-full)")
    parser.add_argument("--color-by", choices=["provider", "tier"], default="provider",
                       help="Color nodes by provider or tier")
    parser.add_argument("--output", default=None,
                       help="Output directory (default: visualizations/)")
    parser.add_argument("--no-labels", action="store_true",
                       help="Hide ship name labels")
    parser.add_argument("--show", action="store_true",
                       help="Display plot interactively")

    args = parser.parse_args()

    print("=" * 70)
    print("VALIS ARMADA NETWORK VISUALIZATION")
    print("=" * 70)

    fig = create_armada_network(
        fleet_option=args.fleet,
        color_by=args.color_by,
        output_dir=Path(args.output) if args.output else None,
        show_labels=not args.no_labels
    )

    if args.show:
        plt.show()

    print("\n[OK] Visualization complete!")


if __name__ == "__main__":
    main()
