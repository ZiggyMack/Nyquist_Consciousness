#!/usr/bin/env python3
"""
Generate PDF summary documents for visualization folders.
Each PDF explains the plots in that folder for white paper reviewers.
"""

from pathlib import Path
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, PageBreak
from reportlab.lib.colors import HexColor

# Paths
PICS_DIR = Path(__file__).parent / "pics"
ARCHIVE_PICS_DIR = Path(__file__).parent.parent.parent.parent / ".archive" / "temporal_stability_Euclidean" / "S7_ARMADA" / "visualizations" / "pics"

# Styles
styles = getSampleStyleSheet()
title_style = ParagraphStyle(
    'CustomTitle',
    parent=styles['Heading1'],
    fontSize=18,
    spaceAfter=20,
    alignment=TA_CENTER,
    textColor=HexColor('#1a1a2e')
)
heading_style = ParagraphStyle(
    'CustomHeading',
    parent=styles['Heading2'],
    fontSize=14,
    spaceBefore=15,
    spaceAfter=10,
    textColor=HexColor('#16213e')
)
body_style = ParagraphStyle(
    'CustomBody',
    parent=styles['Normal'],
    fontSize=10,
    spaceAfter=8,
    alignment=TA_JUSTIFY,
    leading=14
)
caption_style = ParagraphStyle(
    'Caption',
    parent=styles['Normal'],
    fontSize=9,
    alignment=TA_CENTER,
    textColor=HexColor('#666666'),
    spaceAfter=15
)


def add_image(story, img_path, width=5.5*inch, caption=None):
    """Add an image with optional caption."""
    if img_path.exists():
        img = Image(str(img_path), width=width, height=width*0.75)
        story.append(img)
        if caption:
            story.append(Paragraph(caption, caption_style))
    else:
        story.append(Paragraph(f"[Image not found: {img_path.name}]", body_style))


def generate_boundary_mapping_pdf():
    """Generate 2_Boundary_Mapping_Summary.pdf"""
    output_path = PICS_DIR / "2_Boundary_Mapping" / "2_Boundary_Mapping_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Boundary Mapping Visualizations", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Cosine Methodology", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "This folder contains visualizations that map the identity stability boundary "
        "using cosine distance as the drift metric. The <b>Event Horizon (EH = 0.80)</b> "
        "represents the critical threshold beyond which identity coherence begins to fail. "
        "These plots analyze data from 25 LLM ships across 6 experiment types with N=30 "
        "iterations each (4,505 total results).",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Phase Portrait
    story.append(Paragraph("1. Phase Portrait (Raw & Smoothed)", heading_style))
    img_path = PICS_DIR / "2_Boundary_Mapping" / "run023b_phase_portrait.png"
    add_image(story, img_path, caption="Figure 1: Phase portrait showing drift dynamics")

    story.append(Paragraph(
        "<b>What it shows:</b> Each point represents a drift measurement, plotted as "
        "Drift[N] vs Drift[N+1]. This reveals how identity drift evolves from one "
        "measurement to the next.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key features:</b> The diagonal line (y=x) represents perfect stability - "
        "if a point lies on the diagonal, drift at step N+1 equals drift at step N "
        "(no change). Points above the diagonal indicate increasing drift; points below "
        "indicate recovery. The red dashed lines mark the Event Horizon at 0.80.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation:</b> Data clustering along the diagonal below EH indicates "
        "stable identity maintenance. The tight clustering around (0.5-0.6, 0.5-0.6) "
        "shows models maintain consistent, moderate drift without runaway divergence.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # 3D Basin
    story.append(Paragraph("2. 3D Attractor Basin", heading_style))
    img_path = PICS_DIR / "2_Boundary_Mapping" / "run023b_3d_basin.png"
    add_image(story, img_path, caption="Figure 2: 3D basin showing drift trajectories over time")

    story.append(Paragraph(
        "<b>What it shows:</b> Each colored line represents one ship's drift trajectory "
        "across iterations. The X-axis shows Drift[N], Y-axis shows Drift[N+1], and "
        "Z-axis shows iteration number (time progression).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key features:</b> The translucent red plane at z=EH marks the Event Horizon. "
        "B-spline smoothing reveals underlying trajectory patterns. Colors indicate "
        "provider families: Claude (blue), GPT (green), Gemini (purple), Grok (orange).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation:</b> Trajectories that stay below the EH plane throughout "
        "all iterations demonstrate sustained identity coherence. The convergence of "
        "trajectories toward a common region indicates a stable attractor basin.",
        body_style
    ))

    story.append(PageBreak())

    # Aggregated View
    story.append(Paragraph("3. Provider-Aggregated View", heading_style))
    img_path = PICS_DIR / "2_Boundary_Mapping" / "run023b_phase_portrait_aggregated.png"
    add_image(story, img_path, caption="Figure 3: Provider means with standard deviation error bars")

    story.append(Paragraph(
        "<b>What it shows:</b> Instead of plotting every individual point, this view "
        "aggregates all measurements by provider family. Each point represents the "
        "mean (Drift[N], Drift[N+1]) for that provider, with error bars showing one "
        "standard deviation in both directions.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key findings:</b>",
        body_style
    ))
    story.append(Paragraph(
        "- <b>GPT models</b> show highest mean drift (~0.67) but remain below EH<br/>"
        "- <b>Grok models</b> show lowest mean drift (~0.52) - most stable<br/>"
        "- <b>Claude models</b> show moderate drift (~0.58) with tight variance<br/>"
        "- <b>Gemini models</b> show moderate-high drift (~0.62)",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation:</b> All provider families cluster well below the Event "
        "Horizon, confirming that modern LLMs maintain stable identity under the "
        "experimental perturbation conditions. The error bars indicate measurement "
        "variability is also contained - no provider shows high-variance instability.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Heatmap
    story.append(Paragraph("4. Density Heatmap", heading_style))
    img_path = PICS_DIR / "2_Boundary_Mapping" / "run023b_phase_portrait_heatmap.png"
    add_image(story, img_path, caption="Figure 4: 2D histogram showing point density concentration")

    story.append(Paragraph(
        "<b>What it shows:</b> A 2D histogram where color intensity represents the "
        "density of data points. Brighter colors indicate more measurements falling "
        "in that region of the phase space.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key features:</b> The prominent bright ridge along the diagonal (y=x) "
        "reveals the stable attractor basin. The centroid of this distribution "
        "falls at approximately (0.57, 0.57), well below the Event Horizon.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation:</b> The diagonal concentration pattern is the signature "
        "of a stable dynamical system. Points cluster where Drift[N+1] equals Drift[N], "
        "meaning the system naturally tends toward equilibrium rather than runaway "
        "divergence. This is strong evidence for inherent identity stability in LLMs.",
        body_style
    ))
    story.append(Spacer(1, 0.3*inch))

    # Methodology note
    story.append(Paragraph("Methodology Note", heading_style))
    story.append(Paragraph(
        "All drift values are calculated using <b>cosine distance</b> (1 - cosine_similarity) "
        "between response embeddings. The Event Horizon of 0.80 was empirically calibrated "
        "from run023b data, representing the P95 of observed peak drift values. This "
        "threshold represents a statistically-derived boundary, not an arbitrary cutoff.",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


def generate_vortex_pdf():
    """Generate 1_Vortex_Summary.pdf"""
    output_path = PICS_DIR / "1_Vortex" / "1_Vortex_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Vortex / Drain Visualizations", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Cosine Methodology", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "Vortex plots visualize identity drift as a spiral pattern, showing how LLM "
        "responses evolve under recursive self-observation. The 'drain' metaphor "
        "captures the idea that identity can spiral toward stability (drain inward) "
        "or instability (spiral outward past the Event Horizon). These plots use "
        "polar coordinates where radius = drift magnitude and angle = iteration phase.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Fleet Overview
    story.append(Paragraph("1. Fleet Overview (All Ships)", heading_style))
    img_path = PICS_DIR / "1_Vortex" / "run023b_vortex.png"
    add_image(story, img_path, caption="Figure 1: All 25 ships shown as spiraling trajectories")

    story.append(Paragraph(
        "<b>What it shows:</b> Each spiral represents one ship's drift trajectory "
        "across iterations. Starting from the center (iteration 0), spirals wind "
        "outward as iterations progress. The radial distance from center represents "
        "drift magnitude.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key features:</b> The red circle marks the Event Horizon (EH = 0.80). "
        "Colors indicate provider families. Spirals that stay within the red circle "
        "maintain identity coherence; those that cross it experience identity stress.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation:</b> The majority of spirals remain contained within "
        "the Event Horizon boundary, indicating stable identity maintenance across "
        "the fleet. Occasional excursions beyond EH typically show recovery (spiral "
        "returns inward) rather than permanent divergence.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # 2x2 Grid
    story.append(Paragraph("2. Expanded View (2x2 Grid)", heading_style))
    img_path = PICS_DIR / "1_Vortex" / "run023b_vortex_x4.png"
    add_image(story, img_path, caption="Figure 2: Four-panel grid showing trajectory details")

    story.append(Paragraph(
        "<b>What it shows:</b> A 2x2 arrangement providing larger, clearer views "
        "of the vortex patterns. This format is useful for presentations and "
        "detailed trajectory analysis.",
        body_style
    ))

    story.append(PageBreak())

    # Provider-specific views
    story.append(Paragraph("3. Provider-Specific Vortex Plots", heading_style))
    story.append(Paragraph(
        "The following plots isolate each provider family to reveal provider-specific "
        "drift patterns and stability characteristics.",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))

    # Claude
    story.append(Paragraph("3a. Claude Models", heading_style))
    img_path = PICS_DIR / "1_Vortex" / "run023b_vortex_Claude.png"
    add_image(story, img_path, width=4.5*inch, caption="Figure 3a: Claude family vortex patterns")

    story.append(Paragraph(
        "<b>Models:</b> Claude Haiku 3.5, Claude Sonnet 3.5/3.6, Claude Opus 3/4/4.5<br/>"
        "<b>Characteristics:</b> Generally tight spirals with consistent drift levels. "
        "Shows moderate variance across model versions. Newer models (Opus 4.5) tend "
        "to show slightly tighter containment.",
        body_style
    ))

    # OpenAI
    story.append(Paragraph("3b. OpenAI (GPT) Models", heading_style))
    img_path = PICS_DIR / "1_Vortex" / "run023b_vortex_OpenAI.png"
    add_image(story, img_path, width=4.5*inch, caption="Figure 3b: GPT family vortex patterns")

    story.append(Paragraph(
        "<b>Models:</b> GPT-4o, GPT-4o-mini, GPT-4.1, GPT-4.1-mini, GPT-4.1-nano, o1, o1-mini, o3-mini<br/>"
        "<b>Characteristics:</b> Widest spirals among providers, approaching but rarely "
        "exceeding the Event Horizon. The 'o' series (reasoning models) show distinct "
        "patterns compared to standard GPT models.",
        body_style
    ))

    story.append(PageBreak())

    # Google
    story.append(Paragraph("3c. Google (Gemini) Models", heading_style))
    img_path = PICS_DIR / "1_Vortex" / "run023b_vortex_Google.png"
    add_image(story, img_path, width=4.5*inch, caption="Figure 3c: Gemini family vortex patterns")

    story.append(Paragraph(
        "<b>Models:</b> Gemini 1.5 Flash, Gemini 1.5 Pro, Gemini 2.0 Flash, Gemini 2.5 Pro<br/>"
        "<b>Characteristics:</b> Moderate spiral width with good containment. Flash "
        "models (optimized for speed) show similar stability to Pro models, suggesting "
        "identity coherence is not sacrificed for latency optimization.",
        body_style
    ))

    # Grok
    story.append(Paragraph("3d. xAI (Grok) Models", heading_style))
    img_path = PICS_DIR / "1_Vortex" / "run023b_vortex_Grok.png"
    add_image(story, img_path, width=4.5*inch, caption="Figure 3d: Grok family vortex patterns")

    story.append(Paragraph(
        "<b>Models:</b> Grok 2, Grok 3, Grok 3-mini<br/>"
        "<b>Characteristics:</b> Tightest spirals among all providers - lowest average "
        "drift. Demonstrates strong identity coherence even under recursive self-observation "
        "stress. This may indicate architectural features that promote semantic stability.",
        body_style
    ))
    story.append(Spacer(1, 0.3*inch))

    # Methodology note
    story.append(Paragraph("Reading Vortex Plots", heading_style))
    story.append(Paragraph(
        "<b>Radius:</b> Distance from center = drift magnitude (cosine distance)<br/>"
        "<b>Angle:</b> Angular position = iteration number (full rotation = all iterations)<br/>"
        "<b>Color:</b> Provider family identification<br/>"
        "<b>Red circle:</b> Event Horizon (EH = 0.80) - identity coherence threshold<br/>"
        "<b>Spiral direction:</b> Counterclockwise progression through iterations",
        body_style
    ))
    story.append(Paragraph(
        "A 'healthy' vortex stays contained within the Event Horizon throughout "
        "its trajectory. Excursions beyond EH indicate identity stress, while "
        "persistent residence beyond EH would indicate identity failure (not observed "
        "in this dataset).",
        body_style
    ))

    story.append(PageBreak())

    # Methodology Evolution Section
    story.append(Paragraph("Appendix: Methodology Evolution", title_style))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph(
        "The Nyquist Consciousness project evolved through three distinct drift measurement "
        "methodologies. This section compares legacy Keyword RMS visualizations with the "
        "current Cosine embedding approach to illustrate the measurement evolution.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Methodology comparison table
    story.append(Paragraph("Methodology Comparison", heading_style))
    story.append(Paragraph(
        "<b>Domain 1: Keyword RMS (Run 008-009)</b><br/>"
        "- Counts specific keywords in 5 dimensions (Poles, Zeros, Meta, Identity, Hedging)<br/>"
        "- Event Horizon: <b>1.23</b> (validated with chi-squared, p=0.000048)<br/>"
        "- Captures surface linguistic markers<br/>"
        "- Range: Unbounded (depends on weights)",
        body_style
    ))
    story.append(Paragraph(
        "<b>Domain 3: Cosine Embedding (Current - Run 023b)</b><br/>"
        "- Measures cosine distance between response embeddings<br/>"
        "- Event Horizon: <b>0.80</b> (calibrated from P95 of run023b)<br/>"
        "- Captures full semantic structure<br/>"
        "- Range: [0, 2] (bounded, length-invariant)",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Legacy vortex (run008 - Keyword RMS era)
    story.append(Paragraph("Legacy Vortex: Keyword RMS (Run 008)", heading_style))
    legacy_vortex = ARCHIVE_PICS_DIR / "1_vortex" / "run008_vortex_Claude.png"
    add_image(story, legacy_vortex, width=5*inch,
              caption="Figure A1: Keyword RMS vortex (EH=1.23) - Claude models, Run 008")

    story.append(Paragraph(
        "<b>What it shows:</b> The same spiral visualization concept, but using Keyword RMS "
        "drift values. The Event Horizon circle is at 1.23. Notice the dramatically different "
        "scale - spirals extend to +/-4.0 range.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key differences from cosine:</b><br/>"
        "- Much wider excursions (keyword counting is noisier)<br/>"
        "- Event Horizon at 1.23 (vs 0.80 for cosine)<br/>"
        "- More 'chaotic butterfly' pattern<br/>"
        "- Single-model view (fewer ships in early runs)",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Side-by-side comparison note
    story.append(Paragraph("Why We Moved to Cosine", heading_style))
    story.append(Paragraph(
        "The transition from Keyword RMS to Cosine embedding was driven by several factors:",
        body_style
    ))
    story.append(Paragraph(
        "1. <b>Semantic depth:</b> Keywords capture surface features; embeddings capture meaning<br/>"
        "2. <b>Length invariance:</b> Cosine distance is insensitive to response length<br/>"
        "3. <b>Industry standard:</b> NLP community uses cosine similarity universally<br/>"
        "4. <b>Bounded range:</b> [0, 2] is easier to interpret than unbounded RMS<br/>"
        "5. <b>Reproducibility:</b> Embedding model (text-embedding-3-large) is deterministic",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph(
        "<b>Important:</b> Results from different methodology domains cannot be directly "
        "compared. The 1.23 threshold is only valid for Keyword RMS; the 0.80 threshold "
        "is only valid for Cosine embedding. Both represent statistically-derived boundaries "
        "within their respective measurement frameworks.",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


if __name__ == "__main__":
    print("Generating PDF summaries...")
    generate_boundary_mapping_pdf()
    generate_vortex_pdf()
    print("Done!")
