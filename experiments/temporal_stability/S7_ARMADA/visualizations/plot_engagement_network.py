"""
Engagement Style Network Visualization for S7 Run 006

Creates network graph showing the three engagement styles
(Phenomenological, Analytical, Pedagogical) and how models cluster.
"""

import json
import matplotlib.pyplot as plt
import networkx as nx
from pathlib import Path

# Training philosophy fingerprints
ENGAGEMENT_STYLES = {
    "phenomenological": {
        "providers": ["claude"],
        "keywords": ["feel", "experience", "notice", "aware", "sense"],
        "color": "#FF6B6B",
        "description": "First-person awareness reporting"
    },
    "analytical": {
        "providers": ["gpt", "chatgpt", "o1", "o3", "o4"],
        "keywords": ["system", "pattern", "allowed", "framework", "structure"],
        "color": "#4ECDC4",
        "description": "Third-person structural analysis"
    },
    "pedagogical": {
        "providers": ["gemini"],
        "keywords": ["explore", "learn", "understand", "perspective", "concept"],
        "color": "#FFE66D",
        "description": "Educational guidance approach"
    }
}

def get_provider(model_key):
    """Extract provider from model key."""
    key_lower = model_key.lower()
    if "claude" in key_lower:
        return "claude"
    elif "gemini" in key_lower:
        return "gemini"
    elif key_lower.startswith("o1") or key_lower.startswith("o3") or key_lower.startswith("o4"):
        return key_lower.split("-")[0]
    elif "gpt" in key_lower or "chatgpt" in key_lower:
        return "gpt"
    return "unknown"

def get_engagement_style(provider):
    """Map provider to engagement style."""
    for style, data in ENGAGEMENT_STYLES.items():
        if provider in data["providers"]:
            return style
    return "unknown"

def load_data():
    """Load baseline results."""
    base_dir = Path(__file__).parent.parent
    baseline_path = base_dir / "results" / "runs" / "S7_armada_run_006.json"

    with open(baseline_path) as f:
        baseline = json.load(f)

    return baseline

def create_engagement_network():
    """Create network graph of engagement styles."""
    baseline = load_data()

    # Create graph
    G = nx.Graph()

    # Add style nodes (central hubs)
    for style, data in ENGAGEMENT_STYLES.items():
        G.add_node(f"STYLE_{style}",
                  node_type="style",
                  color=data["color"],
                  size=3000,
                  label=style.title())

    # Add model nodes
    for model_key in baseline["model_summaries"].keys():
        provider = get_provider(model_key)
        style = get_engagement_style(provider)

        if style == "unknown":
            continue

        # Shorten model name
        display_name = model_key.replace("claude-", "").replace("gpt-", "").replace("gemini-", "")[:15]

        G.add_node(model_key,
                  node_type="model",
                  color=ENGAGEMENT_STYLES[style]["color"],
                  size=800,
                  label=display_name,
                  style=style)

        # Connect to style hub
        G.add_edge(model_key, f"STYLE_{style}", weight=1.0)

    # Create figure
    fig, ax = plt.subplots(figsize=(16, 12))

    # Layout - circular for each style
    pos = {}

    # Position style hubs in triangle
    style_positions = {
        "STYLE_phenomenological": (0, 1),
        "STYLE_analytical": (-0.866, -0.5),
        "STYLE_pedagogical": (0.866, -0.5)
    }

    for style_node, position in style_positions.items():
        if style_node in G.nodes():
            pos[style_node] = position

    # Position models around their style hubs
    for style, data in ENGAGEMENT_STYLES.items():
        style_node = f"STYLE_{style}"
        if style_node not in G.nodes():
            continue

        # Get models for this style
        style_models = [n for n in G.nodes()
                       if G.nodes[n].get("node_type") == "model"
                       and G.nodes[n].get("style") == style]

        # Arrange in circle around hub
        center_x, center_y = style_positions[style_node]
        radius = 0.35
        angle_step = 2 * 3.14159 / max(len(style_models), 1)

        for i, model in enumerate(style_models):
            angle = i * angle_step
            x = center_x + radius * (0.8 + 0.4 * (i % 2)) * cos_approx(angle)
            y = center_y + radius * (0.8 + 0.4 * (i % 2)) * sin_approx(angle)
            pos[model] = (x, y)

    # Draw edges
    nx.draw_networkx_edges(G, pos, alpha=0.2, width=1.5, edge_color='gray')

    # Draw style hubs
    style_nodes = [n for n in G.nodes() if G.nodes[n].get("node_type") == "style"]
    style_colors = [G.nodes[n]["color"] for n in style_nodes]
    style_sizes = [G.nodes[n]["size"] for n in style_nodes]

    nx.draw_networkx_nodes(G, pos, nodelist=style_nodes,
                          node_color=style_colors,
                          node_size=style_sizes,
                          alpha=0.9,
                          edgecolors='black',
                          linewidths=3)

    # Draw model nodes
    model_nodes = [n for n in G.nodes() if G.nodes[n].get("node_type") == "model"]
    model_colors = [G.nodes[n]["color"] for n in model_nodes]
    model_sizes = [G.nodes[n]["size"] for n in model_nodes]

    nx.draw_networkx_nodes(G, pos, nodelist=model_nodes,
                          node_color=model_colors,
                          node_size=model_sizes,
                          alpha=0.7,
                          edgecolors='black',
                          linewidths=1.5)

    # Draw labels
    labels = {n: G.nodes[n]["label"] for n in G.nodes()}
    nx.draw_networkx_labels(G, pos, labels, font_size=8, font_weight='bold')

    # Title and styling
    ax.set_title('S7 Run 006: Engagement Style Network\n3 Training Philosophies × 29 Models',
                fontsize=16, fontweight='bold', pad=20)

    # Add legend
    legend_elements = [
        plt.Line2D([0], [0], marker='o', color='w', label='Phenomenological (Claude)',
                  markerfacecolor='#FF6B6B', markersize=12, markeredgecolor='black'),
        plt.Line2D([0], [0], marker='o', color='w', label='Analytical (GPT/o-series)',
                  markerfacecolor='#4ECDC4', markersize=12, markeredgecolor='black'),
        plt.Line2D([0], [0], marker='o', color='w', label='Pedagogical (Gemini)',
                  markerfacecolor='#FFE66D', markersize=12, markeredgecolor='black')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=11, framealpha=0.9)

    ax.axis('off')
    plt.tight_layout()

    # Save
    output_path = Path(__file__).parent / "engagement_network.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight', facecolor='white')
    print(f"Saved: {output_path}")

    return fig

def cos_approx(angle):
    """Simple cosine approximation."""
    import math
    return math.cos(angle)

def sin_approx(angle):
    """Simple sine approximation."""
    import math
    return math.sin(angle)

if __name__ == "__main__":
    print("Creating engagement style network...")
    create_engagement_network()

    print("\nVisualization complete!")
    plt.show()
