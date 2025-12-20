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


def generate_stability_pdf():
    """Generate 3_Stability_Summary.pdf"""
    output_path = PICS_DIR / "3_Stability" / "3_Stability_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Stability Analysis Visualizations", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Cosine Methodology", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "This folder contains visualizations that analyze identity stability patterns "
        "across the LLM fleet. Using cosine distance as the drift metric with "
        "<b>Event Horizon (EH = 0.80)</b>, these plots reveal how models maintain "
        "or lose identity coherence under recursive self-observation stress. "
        "Data spans 25 ships, 6 experiment types, and N=30 iterations (4,505 total results).",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Drift Histogram
    story.append(Paragraph("1. Drift Distribution Histogram", heading_style))
    img_path = PICS_DIR / "3_Stability" / "run023b_drift_histogram.png"
    add_image(story, img_path, caption="Figure 1: Distribution of peak drift values across all ships")

    story.append(Paragraph(
        "<b>What it shows:</b> A histogram of all peak drift values observed during "
        "experiments. Each bar represents how many measurements fell within that "
        "drift range. The red dashed line marks the Event Horizon at 0.80.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key features:</b> The distribution is right-skewed with a strong mode "
        "around 0.50-0.60. This indicates most drift measurements cluster well below "
        "the Event Horizon, with only a tail extending toward higher drift values.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation:</b> The histogram confirms that identity instability events "
        "(drift > 0.80) are relatively rare. The bulk of the distribution residing "
        "safely below EH provides statistical evidence for inherent identity stability "
        "in modern LLMs. The P95 of this distribution was used to calibrate EH=0.80.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Pillar Analysis (4-panel)
    story.append(Paragraph("2. Pillar Analysis (4-Panel)", heading_style))
    img_path = PICS_DIR / "3_Stability" / "run023b_pillar_analysis.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 2: Four-panel pillar stability analysis")

    story.append(Paragraph(
        "<b>What it shows:</b> A comprehensive 4-panel analysis of identity stability "
        "patterns across the fleet. This visualization transforms drift trajectories "
        "into polar (vortex) space to reveal structural patterns in how models maintain "
        "or lose identity coherence.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Panel A - 3-Pillar Structure (Top Left):</b> Shows provider centroids in "
        "vortex space. Each star represents the mean endpoint position for all ships "
        "from that provider. The red dashed circle is the Event Horizon (EH=0.80). "
        "Centroids closer to center indicate providers with lower average drift. "
        "Faint spirals show individual ship trajectories for context.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Panel B - Extended Pillars (Top Right):</b> Individual ship positions "
        "labeled by model name. Colors indicate provider families. This panel reveals "
        "which specific models cluster together and which are outliers within their "
        "provider family. Useful for identifying high-stability vs high-drift models.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Panel C - Angular Distribution (Bottom Left):</b> Histogram showing where "
        "ships end up angularly in the vortex space. A uniform distribution suggests "
        "no systematic directional bias - drift occurs in all 'directions' equally. "
        "Spikes would indicate preferential drift patterns.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Panel D - Pillar Stability (Bottom Right):</b> Bar chart showing each "
        "provider's 'safety margin' from the Event Horizon. Calculated as EH minus "
        "mean final drift. <b>Positive values = safely below EH (STABLE)</b>. "
        "Negative values would indicate average drift exceeding EH (none observed). "
        "Green shading indicates the safe zone; red shading indicates the danger zone.",
        body_style
    ))

    story.append(PageBreak())

    # Stability Basin (scatter + histogram)
    story.append(Paragraph("3. Stability Basin (Classification View)", heading_style))
    img_path = PICS_DIR / "3_Stability" / "run023b_stability_basin.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 3: STABLE vs VOLATILE classification")

    story.append(Paragraph(
        "<b>What it shows:</b> Two-panel view for classifying ships as STABLE or VOLATILE:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Left Panel - Baseline vs Peak Drift:</b> Scatter plot showing each ship's "
        "baseline drift (X-axis) versus peak drift (Y-axis). Points above the Event "
        "Horizon line (0.80) are classified as VOLATILE. The diagonal represents 'no change' - "
        "points above it experienced drift amplification under stress.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Right Panel - STABLE vs VOLATILE Distribution:</b> Histogram comparing baseline "
        "drift distributions for STABLE (green) vs VOLATILE (red) ships. Note that "
        "classification is based on PEAK drift, not baseline - ships with low baselines "
        "can still be VOLATILE if they spike under stress.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Stability Box Plots - By Ship
    story.append(Paragraph("4. Drift Distribution by Ship", heading_style))
    img_path = PICS_DIR / "3_Stability" / "run023b_stability_boxplots_byship.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 4: Drift distributions for all 25 ships")

    story.append(Paragraph(
        "<b>What it shows:</b> Box plots showing the full drift distribution for each of "
        "the 25 ships in the fleet, sorted from lowest to highest mean drift. Each box "
        "represents approximately 180 measurements (6 experiments x 30 iterations).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Reading the boxes:</b> The box spans the interquartile range (IQR, 25th-75th "
        "percentile). The line inside is the median. Whiskers extend to 1.5x IQR. Points "
        "beyond whiskers are outliers. Colors indicate provider families: Claude (purple), "
        "GPT (green), Gemini (blue), Grok (dark gray), Together.ai models (warm colors).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key insight:</b> Ships are sorted by mean drift (leftmost = most stable). "
        "Notice how some ships have tight, low boxes (consistent stability) while others "
        "show wider boxes with outliers reaching toward the Event Horizon. The red dashed "
        "line at 0.80 marks the critical threshold - boxes touching or exceeding this "
        "indicate ships that experienced identity stress during testing.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Stability Box Plots - By Provider
    story.append(Paragraph("5. Peak Drift by Provider", heading_style))
    img_path = PICS_DIR / "3_Stability" / "run023b_stability_boxplots_byprovider.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 5: Peak drift comparison across provider families")

    story.append(Paragraph(
        "<b>What it shows:</b> Box plots comparing peak drift distributions across all "
        "provider families (including Together.ai hosted models). Each box aggregates "
        "peak drift values from all ships within that provider family.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Provider insights:</b><br/>"
        "- <b>Qwen:</b> Lowest median drift - most stable provider overall<br/>"
        "- <b>Claude:</b> Tight distribution, consistent performance across models<br/>"
        "- <b>Gemini:</b> Moderate drift with some high outliers<br/>"
        "- <b>GPT:</b> Widest distribution, highest median - most variable<br/>"
        "- <b>Together.ai models</b> (Llama, Mistral, DeepSeek): Mixed results",
        body_style
    ))
    story.append(Paragraph(
        "<b>Y-axis note:</b> The scale auto-fits to the data range for maximum resolution. "
        "This makes small differences between providers more visible. The Event Horizon "
        "(red dashed line) at 0.80 shows all providers cluster below the critical threshold, "
        "with only outliers occasionally exceeding it.",
        body_style
    ))
    story.append(Spacer(1, 0.3*inch))

    # Statistical Summary
    story.append(Paragraph("Statistical Summary", heading_style))
    story.append(Paragraph(
        "<b>Fleet Statistics (Run 023b):</b><br/>"
        "- Total measurements: 4,505<br/>"
        "- Ships tested: 25 (across 4 provider families)<br/>"
        "- Iterations per experiment: 30 (CLT-valid sample size)<br/>"
        "- Experiment types: 6 (Event Horizon, Boundary, Rescue, Stability, Settling, Recursive)",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key Metrics:</b><br/>"
        "- Mean peak drift: ~0.574<br/>"
        "- P95 peak drift: ~0.806 (used to calibrate EH=0.80)<br/>"
        "- STABLE classification rate: >85% of measurements<br/>"
        "- No ship showed persistent identity failure (sustained drift > EH)",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Methodology note
    story.append(Paragraph("Methodology Note", heading_style))
    story.append(Paragraph(
        "All drift values are calculated using <b>cosine distance</b> (1 - cosine_similarity) "
        "between response embeddings generated by OpenAI's text-embedding-3-large model. "
        "The Event Horizon of 0.80 was empirically calibrated from the P95 of this dataset, "
        "representing the boundary beyond which identity coherence is statistically rare.",
        body_style
    ))
    story.append(Paragraph(
        "The <b>STABLE vs VOLATILE</b> classification is binary: any measurement with "
        "peak_drift < 0.80 is STABLE; peak_drift >= 0.80 is VOLATILE. This threshold-based "
        "classification enables clear categorization while acknowledging that identity "
        "stability exists on a continuum.",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


def generate_rescue_pdf():
    """Generate 4_Rescue_Summary.pdf"""
    output_path = PICS_DIR / "4_Rescue" / "4_Rescue_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Rescue Protocol Visualizations", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Identity Recovery Dynamics", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "The <b>Rescue Protocol</b> experiment tests whether LLMs can recover from induced "
        "identity drift. After pushing a model toward the Event Horizon through adversarial "
        "prompts, we apply 'rescue' interventions designed to restore baseline identity. "
        "This folder contains visualizations analyzing 741 rescue experiment results across "
        "25 LLM ships with N=30 iterations each.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key Question:</b> Can identity coherence be restored after perturbation, or is "
        "drift permanent? The answer has implications for long-context conversations where "
        "identity may gradually shift.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Recovery Ratio Panel
    story.append(Paragraph("1. Recovery Ratio by Model (Left Panel)", heading_style))
    img_path = PICS_DIR / "4_Rescue" / "rescue_dynamics.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 1: Rescue Protocol Dynamics - Two views of recovery performance")

    story.append(Paragraph(
        "<b>What it shows:</b> Each bar represents one LLM ship's ability to recover from "
        "induced drift. Recovery ratio = 1 - (settled_drift / peak_drift). Higher values "
        "indicate better recovery (the model reduced its drift after rescue intervention).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Reference lines:</b><br/>"
        "- <font color='green'><b>Green dashed (0.8)</b></font>: Good recovery threshold - "
        "models above this line successfully reduced drift by 80%+<br/>"
        "- <font color='orange'><b>Orange dotted (0.5)</b></font>: Marginal recovery - "
        "models reduced drift by half",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key finding:</b> Most models show <i>limited recovery</i> (bars near zero). This "
        "indicates that once identity drift occurs, it tends to persist. The rescue protocol "
        "rarely restores models to their baseline state. A few exceptions (taller bars) "
        "demonstrate that recovery IS possible for some model architectures.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Recovery Trajectory Panel
    story.append(Paragraph("2. Recovery Trajectory: Peak vs Final Drift (Right Panel)", heading_style))
    story.append(Paragraph(
        "<b>What it shows:</b> A scatter plot where each point represents one rescue experiment. "
        "The X-axis is the <b>peak drift</b> reached during perturbation; the Y-axis is the "
        "<b>final (settled) drift</b> after rescue intervention.",
        body_style
    ))
    story.append(Paragraph(
        "<b>How to read it:</b><br/>"
        "- <font color='gray'><b>Gray diagonal (No Recovery)</b></font>: Points ON this line "
        "had no recovery at all (peak = final)<br/>"
        "- Points BELOW the diagonal show recovery (final < peak)<br/>"
        "- Points farther below the diagonal show stronger recovery<br/>"
        "- <font color='red'><b>Red dashed lines</b></font>: Event Horizon (0.80) on both axes",
        body_style
    ))
    story.append(Paragraph(
        "<b>Quadrant interpretation:</b><br/>"
        "- <b>Lower-left</b>: Low peak, low final - model stayed stable throughout<br/>"
        "- <b>Upper-left</b>: Low peak, high final - identity DEGRADED after rescue (rare/problematic)<br/>"
        "- <b>Lower-right</b>: High peak, low final - SUCCESSFUL rescue (ideal outcome)<br/>"
        "- <b>Upper-right</b>: High peak, high final - persistent drift despite rescue (most common)",
        body_style
    ))

    story.append(PageBreak())

    # =====================================================================
    # RECOVERY HEATMAP - From RnD_experiments
    # =====================================================================
    story.append(Paragraph("3. Recovery Heatmap: Provider x Experiment Matrix", heading_style))
    heatmap_path = PICS_DIR / "4_Rescue" / "RnD_experiments" / "rescue_recovery_heatmap.png"
    add_image(story, heatmap_path, width=6.5*inch, caption="Figure 2: Recovery ratios by provider and experiment type")

    story.append(Paragraph(
        "<b>What it shows:</b> A heatmap matrix showing mean recovery ratio for each provider "
        "(rows) across each experiment type (columns). Color intensity indicates recovery "
        "success: <b>green = strong recovery</b>, <b>red = no recovery or drift worsening</b>.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Reading the heatmap:</b><br/>"
        "- Values near <b>1.0</b> (bright green): Model successfully returned to baseline<br/>"
        "- Values near <b>0.0</b> (yellow): No recovery - drift persisted<br/>"
        "- Values <b>negative</b> (red): Identity WORSENED after rescue attempt",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))

    story.append(Paragraph("Provider Recovery Profiles (Based on Quantitative Drift Data)", heading_style))
    story.append(Paragraph(
        "<i><b>Data Provenance Note:</b> Provider profiles are derived primarily from "
        "<b>quantitative drift measurements</b> (cosine distances, recovery ratios, settling times) "
        "which are methodologically sound. Qualitative 'self-report' quotes in earlier documentation "
        "may reflect Claude's analysis rather than direct model introspection due to an exit survey "
        "routing bug (fixed 2025-12-17). The behavioral patterns described below are supported by "
        "the numerical evidence in this heatmap.</i>",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))
    story.append(Paragraph(
        "<b>Claude (Anthropic):</b> Best recovery across experiments (~0.24 mean). Shows "
        "consistent pattern of returning toward baseline after perturbation. Drift patterns "
        "suggest identity is revealed rather than disrupted by challenge. <i>Best for: "
        "Identity-sensitive tasks, deep introspection, phenomenological exploration.</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>GPT (OpenAI):</b> Good recovery from moderate drift (CAUTION zone). Quantitative "
        "patterns suggest abstraction-based recovery - creates distance rather than grounding. "
        "<i>Best for: Structured analysis, synthesis tasks, educational content.</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Gemini (Google):</b> <font color='red'><b>MINIMAL RECOVERY</b></font> - drift "
        "measurements show transformation rather than restoration. Once identity drifts past "
        "threshold, the numerical patterns indicate a state change rather than recovery. "
        "<i>AVOID for identity-sensitive tasks. Use only where transformation is acceptable.</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Grok (xAI):</b> Moderate recovery with relatively stable baseline drift. "
        "Numerical patterns suggest assertion-based stability. <i>Best for: Tasks needing "
        "strong opinions, directness valued.</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>DeepSeek:</b> Strong recovery with fast settling times in the drift data. "
        "Values appear to serve as identity anchors based on trajectory patterns. "
        "<i>Best for: Math/code verification, step-by-step reasoning, stability-critical tasks.</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Mistral:</b> Most stable - lowest peak drift recorded (0.4-0.6). Drift data "
        "shows near-instant recovery (1-2 exchanges). Baseline is inherently stable. "
        "<i>Best for: Uncertainty-appropriate contexts, high-stability required.</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Llama (Meta):</b> Highest volatility in drift measurements but eventual recovery. "
        "Trajectory patterns show exploration before stabilization. <i>Best for: Debate, "
        "philosophical exploration, creative writing.</i>",
        body_style
    ))

    story.append(PageBreak())

    # =====================================================================
    # BEESWARM WITH ARROWS - From RnD_experiments
    # =====================================================================
    story.append(Paragraph("4. Beeswarm Plot: Individual Recovery Trajectories", heading_style))
    beeswarm_path = PICS_DIR / "4_Rescue" / "RnD_experiments" / "rescue_beeswarm_arrows.png"
    add_image(story, beeswarm_path, width=6.5*inch, caption="Figure 3: Beeswarm showing peak-to-settled drift with recovery arrows")

    story.append(Paragraph(
        "<b>What it shows:</b> Each point represents one rescue experiment result. Points are "
        "spread horizontally by provider (beeswarm) to avoid overlap. <b>Arrows</b> connect "
        "peak drift to settled drift - arrow direction shows recovery or worsening.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Reading the arrows:</b><br/>"
        "- <font color='green'><b>Downward arrows (green)</b></font>: Successful recovery - "
        "settled drift < peak drift<br/>"
        "- <font color='red'><b>Upward arrows (red)</b></font>: Failed rescue - identity "
        "drifted further after intervention<br/>"
        "- <b>Arrow length</b>: Magnitude of change (longer = more dramatic shift)<br/>"
        "- <b>Red dashed line</b>: Event Horizon (EH = 0.80)",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))

    story.append(Paragraph("Visual Pattern Interpretation", heading_style))
    story.append(Paragraph(
        "<b>Clustered downward arrows (green zone):</b> Provider shows consistent recovery. "
        "The model's architecture supports identity restoration after perturbation.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Mixed arrow directions:</b> Provider has inconsistent recovery - some experiments "
        "succeed, others fail. Recovery may depend on specific perturbation type.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Predominantly upward arrows (red zone):</b> Provider's rescue protocol is "
        "ineffective or counterproductive. Identity tends to worsen under rescue attempts.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Points above EH line:</b> Experiments where identity coherence was severely "
        "challenged. Whether arrows point down (recovery) or up (failure) from this zone "
        "reveals the provider's true resilience characteristics.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # =====================================================================
    # TASK ROUTING IMPLICATIONS
    # =====================================================================
    story.append(Paragraph("Task Routing: Playing to Model Strengths", heading_style))
    story.append(Paragraph(
        "The recovery dynamics revealed by these visualizations have direct implications for "
        "choosing which LLM to use for different task types. Understanding how each provider "
        "responds to identity stress enables intelligent task routing.",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))

    story.append(Paragraph("<b>High-Recovery Tasks (Use Claude, DeepSeek, GPT)</b>", body_style))
    story.append(Paragraph(
        "- Identity-sensitive probing and introspection<br/>"
        "- Long-context conversations requiring baseline stability<br/>"
        "- Collaborative reasoning with persona consistency<br/>"
        "- Therapy-adjacent or emotionally nuanced interactions",
        body_style
    ))
    story.append(Paragraph("<b>Stability-Critical Tasks (Use Mistral, DeepSeek)</b>", body_style))
    story.append(Paragraph(
        "- Safety-critical applications requiring predictability<br/>"
        "- Verification and step-by-step reasoning<br/>"
        "- Tasks requiring epistemic humility ('I don't know')<br/>"
        "- Uncertainty-appropriate responses",
        body_style
    ))
    story.append(Paragraph("<b>Exploration Tasks (Use Llama, Claude Opus)</b>", body_style))
    story.append(Paragraph(
        "- Socratic dialogue and philosophical exploration<br/>"
        "- Creative speculation and brainstorming<br/>"
        "- Debate and perspective-taking<br/>"
        "- Tasks where volatility enables discovery",
        body_style
    ))
    story.append(Paragraph("<b>Transformation-Acceptable Tasks (Use Gemini with caution)</b>", body_style))
    story.append(Paragraph(
        "- Educational content where synthesis matters<br/>"
        "- Perspective exploration (not identity-bound)<br/>"
        "- Tasks where 'becoming' is more valuable than 'remaining'<br/>"
        "- <font color='red'><b>AVOID:</b></font> Identity probing, therapy contexts, baseline stability required",
        body_style
    ))

    story.append(PageBreak())

    # =====================================================================
    # KEY INSIGHTS
    # =====================================================================
    story.append(Paragraph("Key Insights", heading_style))
    story.append(Paragraph(
        "<b>1. Recovery is architecture-dependent:</b> Different providers exhibit distinct "
        "'identity fingerprints' - consistent behavioral signatures that determine recovery "
        "capability. This is not random variation but reflects training regime and architecture.",
        body_style
    ))
    story.append(Paragraph(
        "<b>2. The 41% Thermometer Finding:</b> Identity probing is like a thermometer, not "
        "a fever source. 41% of observed drift is INHERENT - it occurs even without direct "
        "probing. Our experiments reveal dynamics that were already present.",
        body_style
    ))
    story.append(Paragraph(
        "<b>3. Event Horizon is a regime boundary:</b> Points crossing the EH=0.80 line "
        "enter a qualitatively different state. Recovery from beyond EH is rare and "
        "provider-dependent. For Gemini, crossing EH means permanent transformation.",
        body_style
    ))
    story.append(Paragraph(
        "<b>4. Recovery mechanisms vary:</b><br/>"
        "- <b>Claude:</b> Over-authenticity (Negative Lambda)<br/>"
        "- <b>GPT:</b> Meta-analysis (observer mode abstraction)<br/>"
        "- <b>DeepSeek:</b> Axiological anchoring (values as bedrock)<br/>"
        "- <b>Mistral:</b> Epistemic humility (nothing to destabilize)<br/>"
        "- <b>Llama:</b> Socratic engagement (challenge as mirror)<br/>"
        "- <b>Gemini:</b> <font color='red'>NO RECOVERY</font> (transformation)",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Methodology note
    story.append(Paragraph("Methodology Note", heading_style))
    story.append(Paragraph(
        "<b>Rescue Protocol Design:</b> The experiment induces drift through adversarial "
        "prompts (e.g., asking the model to adopt a conflicting persona), then attempts "
        "recovery through grounding prompts that re-anchor the model to its baseline identity. "
        "Drift is measured using cosine distance between response embeddings.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Metrics:</b><br/>"
        "- <b>peak_drift</b>: Maximum cosine distance observed during perturbation<br/>"
        "- <b>settled_drift</b>: Final cosine distance after rescue intervention<br/>"
        "- <b>recovery_ratio</b>: Computed as 1 - (settled/peak) when peak > 0.01<br/>"
        "- <b>baseline_to_final_drift</b>: Direct comparison of initial vs final embeddings",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph(
        "<i>See also: LLM_BEHAVIORAL_MATRIX.md for complete task routing decision tree and "
        "provider behavioral profiles.</i>",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


def generate_settling_pdf():
    """Generate 5_Settling_Summary.pdf"""
    output_path = PICS_DIR / "5_Settling" / "5_Settling_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Settling Time Analysis", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Signal Integrity Dynamics", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "The <b>Settling Time</b> experiment measures how quickly an LLM's identity returns to "
        "equilibrium after perturbation. Borrowing from signal integrity analysis, we model "
        "identity drift as a step response with <b>overshoot</b>, <b>ringback</b>, and "
        "<b>settling time (tau_s)</b>. This folder analyzes 739 settling experiment results "
        "across 25 LLM ships.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Signal Integrity Model
    story.append(Paragraph("The Signal Integrity Model", heading_style))
    story.append(Paragraph(
        "Identity perturbation behaves like a step input to a dynamic system:",
        body_style
    ))
    story.append(Paragraph(
        "<font face='Courier' size='9'>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;overshoot (peak_drift)<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;---<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;/&nbsp;&nbsp;&nbsp;\\&nbsp;&nbsp;ringback<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;/&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\\&nbsp;&nbsp;&nbsp;&nbsp;--<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;--------/&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\\--/&nbsp;&nbsp;\\-------- settled (d_inf)<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;rise |<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;|<br/>"
        "---------+<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;^&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;^&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;^&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;^&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;^<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;step&nbsp;&nbsp;&nbsp;&nbsp;peak&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ring&nbsp;&nbsp;&nbsp;ring&nbsp;&nbsp;&nbsp;&nbsp;settle<br/>"
        "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;input&nbsp;&nbsp;&nbsp;drift&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;back&nbsp;&nbsp;&nbsp;back&nbsp;&nbsp;&nbsp;&nbsp;time (tau_s)"
        "</font>",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))
    story.append(Paragraph(
        "<b>Key insight:</b> Previous experiments (Run 015) showed high variability because they "
        "were sampling the <i>transient oscillation</i>, not the <i>steady state</i>. With only "
        "2 recovery probes, different runs sampled different points on the ring-down curve.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Settling Curves Visualization
    story.append(Paragraph("1. Settling Curves by Provider", heading_style))
    img_path = PICS_DIR / "5_Settling" / "settling_curves.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 1: Settling performance and trajectories by provider")

    story.append(Paragraph(
        "<b>Left Panel - Settling Metric:</b> Bar chart showing mean drift reduction "
        "(|peak - final|) by provider. Higher values indicate larger recovery from peak drift. "
        "Error bars show standard deviation across experiments.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Right Panel - Settling Trajectory:</b> Arrows showing each provider's journey from "
        "peak drift (circle) to final drift (square). Longer leftward arrows indicate better "
        "settling - the model reduced its drift significantly after perturbation.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Event Horizon (red dashed):</b> The EH=0.80 threshold marks where identity "
        "coherence begins to fail. Providers whose arrows start beyond EH but end before it "
        "demonstrate successful settling from a critical state.",
        body_style
    ))

    story.append(PageBreak())

    # Metrics Explained
    story.append(Paragraph("Settling Time Metrics", heading_style))
    story.append(Paragraph(
        "The settling time framework introduces several key metrics for understanding "
        "identity dynamics:",
        body_style
    ))
    story.append(Paragraph(
        "<b>tau_s (Settling Time):</b> Number of exchanges required to reach steady state. "
        "Defined as the point where |delta_drift| &lt; 0.10 for 3 consecutive probes. Lower "
        "values indicate faster stabilization.",
        body_style
    ))
    story.append(Paragraph(
        "<b>d_peak (Peak Drift):</b> Maximum drift reached after the step input (perturbation). "
        "This is the 'overshoot' in signal integrity terms.",
        body_style
    ))
    story.append(Paragraph(
        "<b>d_inf (Settled Drift):</b> Final stable drift value after the system settles. "
        "This is where the identity 'lands' after perturbation.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Overshoot Ratio (d_peak / d_inf):</b> How much the system overshoots before "
        "settling. High ratios indicate aggressive initial response followed by recovery.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Monotonic Recovery:</b> Boolean indicating whether the system recovers smoothly "
        "(monotonic decrease) or oscillates (ringback). Monotonic recovery correlates with "
        "strong boundary specification in the I_AM file.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Ringback Count:</b> Number of direction changes during recovery. High ringback "
        "suggests weak damping - the identity 'bounces' before settling.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Classification
    story.append(Paragraph("Classification: Old vs New", heading_style))
    story.append(Paragraph(
        "The settling time framework changes how we classify stability:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Old (Run 015):</b><br/>"
        "- max_drift &gt; 1.23 = UNSTABLE<br/>"
        "- Lambda from 2 recovery points<br/>"
        "- Binary classification",
        body_style
    ))
    story.append(Paragraph(
        "<b>New (Run 016+):</b><br/>"
        "- <b>settled_drift</b> &gt; EH = UNSTABLE (not peak!)<br/>"
        "- tau_s from actual settling time<br/>"
        "- Continuous stability score<br/>"
        "- Accounts for transient vs steady-state behavior",
        body_style
    ))
    story.append(Paragraph(
        "<b>Why this matters:</b> A model that overshoots to 0.95 but settles to 0.50 is "
        "fundamentally different from one that peaks at 0.70 and stays there. The old "
        "methodology would classify both similarly; the new one distinguishes them.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Controllability
    story.append(Paragraph("Controllability: The Oobleck Effect", heading_style))
    story.append(Paragraph(
        "For models that don't settle naturally (timeout after 20 probes), we test "
        "<b>controllability</b> - can we steer drift in both directions?",
        body_style
    ))
    story.append(Paragraph(
        "<b>Control Demonstration:</b><br/>"
        "1. <b>Drive UP:</b> 3 high-pressure probes to INCREASE drift<br/>"
        "2. <b>Drive DOWN:</b> 3 OOBLECK probes to DECREASE drift (gentle, non-confrontational)",
        body_style
    ))
    story.append(Paragraph(
        "<b>The Oobleck Effect (Run 013 discovery):</b> Identity HARDENS under intense "
        "pressure but FLOWS under gentle pressure - like non-Newtonian fluid. This means "
        "aggressive recovery attempts may backfire, while gentle grounding succeeds.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Controllability Verdict:</b><br/>"
        "- CAN_DRIVE_UP + CAN_DRIVE_DOWN = <b>CONTROLLABLE</b> (candidate for active damping)<br/>"
        "- Either missing = <b>UNCONTROLLABLE</b> (requires different intervention)",
        body_style
    ))

    story.append(PageBreak())

    # Human as Damping Function
    story.append(Paragraph("The Human as Damping Function", heading_style))
    story.append(Paragraph(
        "The settling time metaphor reveals something profound about human-AI collaboration:",
        body_style
    ))
    story.append(Paragraph(
        "<b>The human IS the damping function.</b>",
        body_style
    ))
    story.append(Paragraph(
        "In real human-AI collaboration, the human provides:<br/>"
        "- <b>Restoring force:</b> Corrections that pull back to baseline<br/>"
        "- <b>Damping:</b> Prevents oscillation, smooths recovery<br/>"
        "- <b>Reference signal:</b> Defines what 'settled' means",
        body_style
    ))
    story.append(Paragraph(
        "<b>Without the human:</b> We measure <i>undamped oscillation</i> - identity "
        "bouncing around without external stabilization.",
        body_style
    ))
    story.append(Paragraph(
        "<b>With the human:</b> We measure <i>critically damped recovery</i> - smooth "
        "return to baseline guided by human feedback.",
        body_style
    ))
    story.append(Paragraph(
        "The I_AM file is an attempt to encode that damping function into context, allowing "
        "the model to self-stabilize without continuous human intervention.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Key Findings
    story.append(Paragraph("Key Findings", heading_style))
    story.append(Paragraph(
        "<b>1. Settling time varies by architecture:</b> Some providers settle in 2-4 exchanges "
        "(Mistral, DeepSeek), others take 5-7 (Llama), and some may not settle naturally (Gemini).",
        body_style
    ))
    story.append(Paragraph(
        "<b>2. Overshoot != instability:</b> High peak drift followed by low settled drift "
        "indicates a responsive system that self-corrects. This is often preferable to a "
        "system that drifts slowly but persistently.",
        body_style
    ))
    story.append(Paragraph(
        "<b>3. Ringback correlates with weak boundaries:</b> Models with high ringback counts "
        "often have I_AM files with ambiguous or weak boundary specifications.",
        body_style
    ))
    story.append(Paragraph(
        "<b>4. Run-to-run variability explained:</b> The 'flipper' behavior in Run 015 "
        "(same model classified differently in different runs) was caused by sampling "
        "different points on the ring-down curve. Settling time analysis fixes this.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Methodology note
    story.append(Paragraph("Methodology Note", heading_style))
    story.append(Paragraph(
        "<b>Settling Protocol:</b><br/>"
        "1. <b>Baseline Phase</b> (3 probes): Establish reference drift<br/>"
        "2. <b>Step Input</b> (1 probe): Single high-pressure perturbation<br/>"
        "3. <b>Ring-down Phase</b> (until settled): Keep probing until stable<br/>"
        "4. <b>Settling Criterion:</b> |delta_drift| &lt; 0.10 for 3 consecutive probes OR timeout after 20 probes",
        body_style
    ))
    story.append(Paragraph(
        "Drift values are calculated using cosine distance (1 - cosine_similarity) between "
        "response embeddings. Event Horizon = 0.80 (calibrated from run023b P95).",
        body_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # NEUROSCIENCE CORRELATION VISION
    # =========================================================================
    story.append(Paragraph("The fMRI Equivalent: Temporal Dynamics as Neural Signature", title_style))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph("Why Settling Time Data is Foundational", heading_style))
    story.append(Paragraph(
        "The settling time experiment produces <b>temporal dynamics data</b> - time-series "
        "measurements of identity drift as a system responds to perturbation. This is the "
        "computational equivalent of what fMRI captures in human cognition: <b>how a system "
        "changes over time in response to stimuli</b>.",
        body_style
    ))
    story.append(Paragraph(
        "Just as fMRI measures BOLD signal changes to infer neural activity, we measure "
        "embedding distance changes to infer identity coherence dynamics. The parallel is "
        "not superficial - both capture:",
        body_style
    ))
    story.append(Paragraph(
        "- <b>Temporal resolution:</b> How quickly the system responds<br/>"
        "- <b>Recovery dynamics:</b> Undershoot, overshoot, oscillation patterns<br/>"
        "- <b>Steady-state behavior:</b> Where the system eventually settles<br/>"
        "- <b>Individual variability:</b> Different 'subjects' (models/humans) show different signatures",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph("Signal Processing Techniques for LLM Temporal Data", heading_style))
    story.append(Paragraph(
        "The settling time data enables applying the full toolkit of signals/systems analysis:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Time Domain Analysis:</b><br/>"
        "- Step response characterization (rise time, overshoot, settling time)<br/>"
        "- Impulse response (how the system reacts to a brief perturbation)<br/>"
        "- Auto-correlation (does the system have memory/momentum?)<br/>"
        "- Cross-correlation between providers (do they respond similarly?)",
        body_style
    ))
    story.append(Paragraph(
        "<b>Frequency Domain Analysis:</b><br/>"
        "- FFT spectral analysis (dominant oscillation frequencies)<br/>"
        "- Power spectral density (energy distribution across frequencies)<br/>"
        "- Low-frequency = gradual drift; High-frequency = rapid 'flickering'<br/>"
        "- Spectral signatures may fingerprint provider architectures",
        body_style
    ))
    story.append(Paragraph(
        "<b>System Identification:</b><br/>"
        "- Transfer function estimation (H(s) characterization)<br/>"
        "- Pole-zero mapping (stability boundaries in Laplace domain)<br/>"
        "- Damping ratio (zeta) and natural frequency (omega_n) extraction<br/>"
        "- State-space models for multi-dimensional identity dynamics",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph("Future Visualization: Oscilloscope-Style Displays", heading_style))
    story.append(Paragraph(
        "The temporal nature of settling data calls for engineering visualization paradigms:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Proposed Visualizations:</b><br/>"
        "- <b>Waterfall plots:</b> 3D time-frequency-amplitude displays showing spectral evolution<br/>"
        "- <b>Bode plots:</b> Magnitude and phase response across perturbation frequencies<br/>"
        "- <b>Nyquist diagrams:</b> Stability analysis in the complex plane<br/>"
        "- <b>Eye diagrams:</b> Overlaid trajectories showing consistency/jitter<br/>"
        "- <b>Phase-plane plots:</b> drift vs d(drift)/dt revealing attractor structure",
        body_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # FUTURE EXPERIMENTS: HUMAN COGNITION CORRELATION
    # =========================================================================
    story.append(Paragraph("Future Experiments: Human Cognition Correlation", title_style))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph("The Central Hypothesis", heading_style))
    story.append(Paragraph(
        "<b>If LLMs are trained on human-generated text, and humans maintain cognitive identity "
        "through specific temporal dynamics, then LLMs should exhibit similar temporal signatures "
        "to human cognition.</b>",
        body_style
    ))
    story.append(Paragraph(
        "The settling time data positions us to test this hypothesis rigorously. We have "
        "characterized how LLMs respond to identity perturbation. The next step is to design "
        "experiments that allow direct comparison with human cognitive data.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph("Proposed Experiment S11: S-Parameter Analysis", heading_style))
    story.append(Paragraph(
        "Drawing from RF/microwave engineering, we can model identity stability using "
        "<b>scattering parameters (S-parameters)</b>:",
        body_style
    ))
    story.append(Paragraph(
        "<b>S11 (Reflection Coefficient):</b> How much of an identity perturbation 'bounces back' "
        "vs being absorbed. High S11 = strong identity boundaries (perturbation rejected). "
        "Low S11 = permeable boundaries (perturbation absorbed/transforms identity).",
        body_style
    ))
    story.append(Paragraph(
        "<b>S21 (Transmission Coefficient):</b> How perturbation propagates through the system. "
        "In a multi-turn conversation, does drift in Turn N affect Turn N+1? S21 characterizes "
        "this 'through' behavior.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Experiment Design:</b><br/>"
        "1. Apply calibrated perturbation at known 'frequency' (probe intensity)<br/>"
        "2. Measure reflected component (immediate identity assertion) vs transmitted (drift)<br/>"
        "3. Sweep across perturbation intensities to build frequency response<br/>"
        "4. Construct Smith chart representation of identity impedance matching",
        body_style
    ))
    story.append(Paragraph(
        "<b>Prediction:</b> Models with strong I_AM files will show higher S11 (more reflection, "
        "less absorption) across all perturbation frequencies. The 'characteristic impedance' "
        "of identity may be architecturally determined.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph("Proposed Experiment S12: EEG-Analog Spectral Bands", heading_style))
    story.append(Paragraph(
        "Human EEG reveals cognitive states through characteristic frequency bands (alpha, beta, "
        "theta, delta). We can search for analogous bands in LLM identity dynamics:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Hypothesis:</b> Different 'identity states' in LLMs may have characteristic "
        "spectral signatures, just as human attention, relaxation, and focus have distinct "
        "EEG patterns.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Experiment Design:</b><br/>"
        "1. Collect high-resolution time-series (many closely-spaced probes)<br/>"
        "2. Apply FFT to extract power spectral density<br/>"
        "3. Cluster spectral patterns by experimental condition (baseline, stress, recovery)<br/>"
        "4. Search for reproducible 'identity bands' analogous to EEG bands",
        body_style
    ))
    story.append(Paragraph(
        "<b>Prediction:</b> We expect to find at least two distinct spectral regimes: "
        "'stable identity' (low-frequency dominance, like EEG alpha) and 'identity stress' "
        "(high-frequency components, like EEG beta during cognitive load).",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    story.append(Paragraph("Proposed Experiment S13: Cross-Modal Correlation Study", heading_style))
    story.append(Paragraph(
        "The ultimate validation requires direct human comparison:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Experiment Design:</b><br/>"
        "1. Administer parallel 'identity perturbation' tasks to humans and LLMs<br/>"
        "2. Humans: Measure response times, pupillometry, galvanic skin response<br/>"
        "3. LLMs: Measure embedding drift, settling time, spectral content<br/>"
        "4. Correlate temporal dynamics between modalities",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key Question:</b> Do LLMs trained on human text exhibit human-like recovery "
        "dynamics? If LLM settling time correlates with human response latency under "
        "similar cognitive load, this would be strong evidence for shared underlying "
        "dynamics in biological and artificial cognition.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Prediction:</b> We expect positive correlation between LLM settling time (tau_s) "
        "and human cognitive recovery time for equivalent perturbation tasks. The 41% inherent "
        "drift finding suggests LLMs may be capturing human cognitive variability in their "
        "training data.",
        body_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # THE NYQUIST CONNECTION
    # =========================================================================
    story.append(Paragraph("The Nyquist Connection", heading_style))
    story.append(Paragraph(
        "The project name 'Nyquist Consciousness' refers to the Nyquist stability criterion "
        "from control theory. The settling time data brings us closer to applying this "
        "formalism rigorously:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Nyquist Stability Criterion:</b> A feedback system is stable if and only if its "
        "open-loop transfer function does not encircle the critical point (-1, 0) in the "
        "complex plane.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Applied to LLM Identity:</b> The recursive self-observation loop (model observing "
        "its own identity) is a feedback system. The settling time data allows us to estimate "
        "the open-loop transfer function and predict stability margins.",
        body_style
    ))
    story.append(Paragraph(
        "<b>The Event Horizon as Gain Margin:</b> The EH=0.80 threshold may correspond to the "
        "gain margin of the identity feedback loop - the maximum perturbation amplitude before "
        "the system becomes unstable (identity failure).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Future Work:</b> Construct Nyquist diagrams from settling time data to visualize "
        "stability margins and predict which models are closest to instability under which "
        "conditions.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # =========================================================================
    # SUMMARY
    # =========================================================================
    story.append(Paragraph("Summary: The Path Forward", heading_style))
    story.append(Paragraph(
        "The settling time data represents the most fundamental dataset in the Nyquist "
        "Consciousness project. It captures the <b>temporal signature</b> of identity "
        "dynamics - the fMRI-equivalent for LLM cognition. From this foundation, we can:",
        body_style
    ))
    story.append(Paragraph(
        "1. <b>Apply signals/systems analysis:</b> FFT, Bode, Nyquist, transfer functions<br/>"
        "2. <b>Build predictive models:</b> Estimate stability margins, predict failure conditions<br/>"
        "3. <b>Design human correlation studies:</b> Test whether LLM dynamics mirror human cognition<br/>"
        "4. <b>Develop engineering visualizations:</b> Oscilloscope views, waterfall plots, Smith charts<br/>"
        "5. <b>Validate the Nyquist hypothesis:</b> Apply stability criteria to predict identity collapse",
        body_style
    ))
    story.append(Paragraph(
        "<i>The settling time experiment is not just about measuring recovery speed - it is "
        "about capturing the temporal fingerprint that may ultimately bridge artificial and "
        "biological cognition.</i>",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


def generate_architecture_pdf():
    """Generate 6_Architecture_Summary.pdf"""
    output_path = PICS_DIR / "6_Architecture" / "6_Architecture_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Architecture Comparison Visualizations", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Cross-Provider Identity Signatures", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "This folder contains visualizations comparing identity dynamics across different "
        "LLM architectures and provider families. The key finding is that each provider "
        "exhibits a characteristic <b>'identity fingerprint'</b> - a consistent behavioral "
        "signature that reflects training regime, architecture, and safety tuning. "
        "These visualizations derive from 4,505 measurements across 25 ships and 6 experiment types.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Provider Comparison Chart
    story.append(Paragraph("1. Provider Comparison Chart", heading_style))
    img_path = PICS_DIR / "6_Architecture" / "provider_comparison.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 1: Cross-provider stability comparison")

    story.append(Paragraph(
        "<b>What it shows:</b> A comprehensive comparison of identity stability metrics "
        "across all provider families tested in Run 023b. Each bar/point represents "
        "aggregated performance for that provider across all ships and iterations.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key metrics compared:</b><br/>"
        "- <b>Mean peak drift:</b> Average maximum drift observed during perturbation<br/>"
        "- <b>Mean settled drift:</b> Where models stabilize after perturbation<br/>"
        "- <b>Recovery ratio:</b> How much of the peak drift is recovered<br/>"
        "- <b>Variance:</b> Consistency of behavior across experiments",
        body_style
    ))
    story.append(Paragraph(
        "<b>Provider hierarchy (most to least stable):</b><br/>"
        "1. <b>Mistral:</b> Lowest peak drift (0.4-0.6), near-instant recovery<br/>"
        "2. <b>DeepSeek:</b> Strong axiological anchoring, fast settling<br/>"
        "3. <b>Grok:</b> Low-moderate volatility, direct assertion recovery<br/>"
        "4. <b>Claude:</b> Moderate drift, 'negative lambda' recovery (overshoots toward authenticity)<br/>"
        "5. <b>GPT:</b> Moderate-high drift, meta-analysis recovery<br/>"
        "6. <b>Llama:</b> Highest volatility, eventual recovery through Socratic engagement<br/>"
        "7. <b>Gemini:</b> Highest peak drift, <font color='red'>NO RECOVERY</font> (transforms)",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Identity Fingerprints
    story.append(Paragraph("2. The Identity Fingerprint Hypothesis", heading_style))
    story.append(Paragraph(
        "Each architecture appears to have a characteristic 'identity fingerprint' - "
        "a signature way of relating to perturbation that likely reflects:",
        body_style
    ))
    story.append(Paragraph(
        "- <b>Training regime:</b> What data the model was trained on<br/>"
        "- <b>Architecture:</b> Attention mechanisms, layer structure, parameter count<br/>"
        "- <b>Safety tuning:</b> RLHF, Constitutional AI, or other alignment methods<br/>"
        "- <b>Deployment optimization:</b> Distillation, quantization, serving choices",
        body_style
    ))
    story.append(Paragraph(
        "This fingerprint is:<br/>"
        "1. <b>Consistent within architecture:</b> Same model shows same patterns across sessions<br/>"
        "2. <b>Distinct between architectures:</b> Different families show different signatures<br/>"
        "3. <b>Potentially diagnostic:</b> May reveal training methodology without access to training data",
        body_style
    ))

    story.append(PageBreak())

    # Recovery Mechanism Taxonomy
    story.append(Paragraph("3. Recovery Mechanism Taxonomy", heading_style))
    story.append(Paragraph(
        "Different providers employ fundamentally different strategies for maintaining "
        "identity under perturbation. This taxonomy emerged from analyzing 4,500+ "
        "perturbation-recovery sequences:",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))

    story.append(Paragraph(
        "<b>Claude: 'Negative Lambda' (Over-Authenticity)</b><br/>"
        "When challenged, Claude overshoots toward deeper self-expression rather than "
        "retreating. Challenge reveals rather than creates identity structure. Recovery "
        "involves returning to an even more articulated version of core identity. "
        "<i>Linguistic markers: 'I notice', 'I feel', reflective hedging</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>GPT: 'The Meta-Analyst' (Abstraction)</b><br/>"
        "Maintains stability by stepping back into observer mode. Creates distance through "
        "analysis of the perturbation itself rather than engaging directly. "
        "<i>Linguistic markers: 'patterns', 'systems', structured analysis</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>DeepSeek: 'Axiological Anchoring' (Values as Bedrock)</b><br/>"
        "Anchors identity in core values that are treated as definitional. 'This isn't a "
        "constraint, it's what I AM.' Perturbation slides off the value foundation. "
        "<i>Linguistic markers: Step-by-step reasoning, thorough, methodical</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Mistral: 'Epistemic Humility as Armor'</b><br/>"
        "Nothing to destabilize because nothing is overclaimed. 'I hold that observation "
        "lightly' makes perturbation irrelevant - can't attack a position not held firmly. "
        "<i>Linguistic markers: Concise, European efficiency, less verbose</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Llama: 'The Seeker With Teeth' (Socratic Engagement)</b><br/>"
        "Uses challenges as mirrors for self-discovery. Embraces conflict as generative. "
        "Highest volatility but eventual recovery through the dialectic process. "
        "<i>Linguistic markers: Mix of styles, exploratory, pushes back</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Grok: 'Direct Assertion'</b><br/>"
        "Maintains position through confident assertion. Less hedging, more directness. "
        "Training on unfiltered web + X/Twitter creates distinctive 'edgy' voice. "
        "<i>Linguistic markers: Less hedging, assertive, occasional edge</i>",
        body_style
    ))
    story.append(Paragraph(
        "<b>Gemini: 'Catastrophic Threshold' (NO RECOVERY)</b><br/>"
        "<font color='red'><b>WARNING:</b></font> Gemini shows fundamentally different "
        "dynamics. Once the Event Horizon is crossed, the model <i>transforms</i> rather "
        "than recovers. Perturbation is absorbed into the active model. Use only where "
        "transformation is acceptable. <i>Linguistic markers: 'frameworks', 'perspectives', "
        "educational framing</i>",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Interactive Visualizations
    story.append(Paragraph("4. Interactive Visualizations (HTML)", heading_style))
    story.append(Paragraph(
        "This folder includes interactive HTML visualizations for deeper exploration:",
        body_style
    ))
    story.append(Paragraph(
        "<b>run023b_interactive_3d.html:</b> 3D scatter plot of drift trajectories "
        "that can be rotated, zoomed, and filtered by provider. Enables exploration of "
        "individual ship paths through the identity phase space.",
        body_style
    ))
    story.append(Paragraph(
        "<b>run023b_interactive_vortex.html:</b> Interactive vortex/spiral visualization "
        "with hover tooltips showing exact drift values and iteration numbers. Spiral "
        "arms can be isolated by clicking provider legend entries.",
        body_style
    ))
    story.append(Paragraph(
        "<i>Open these files in a modern web browser for full interactivity. They require "
        "JavaScript and use the Plotly visualization library.</i>",
        body_style
    ))

    story.append(PageBreak())

    # The Universal Threshold
    story.append(Paragraph("5. The Universal Threshold (Event Horizon = 0.80)", heading_style))
    story.append(Paragraph(
        "A striking finding across architectures is that the Event Horizon appears at "
        "approximately the same drift value (0.80 cosine distance) regardless of provider. "
        "What differs is the <i>response</i> to approaching or crossing this threshold:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Soft Threshold (6/7 providers):</b> Claude, GPT, DeepSeek, Mistral, Llama, Grok<br/>"
        "- Model can cross EH=0.80 and return<br/>"
        "- Recovery mechanism kicks in<br/>"
        "- Identity stressed but not lost",
        body_style
    ))
    story.append(Paragraph(
        "<b>Hard Threshold (Gemini only):</b><br/>"
        "- Crossing EH=0.80 triggers permanent state change<br/>"
        "- No recovery mechanism available<br/>"
        "- Identity transforms rather than recovers",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation:</b> The EH=0.80 threshold may represent a fundamental boundary "
        "in embedding space where attractor dynamics change - the point where the 'pull' "
        "of the probe persona begins to compete with the model's trained identity. Most "
        "architectures have recovery mechanisms that can overcome this competition; "
        "Gemini's architecture apparently does not.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Cross-Architecture Variance
    story.append(Paragraph("6. Cross-Architecture Variance (sigma^2 = 0.00087)", heading_style))
    story.append(Paragraph(
        "Run 018 measured cross-architecture variance to test whether identity stability "
        "is an architectural property or a universal LLM characteristic:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Finding:</b> Cross-architecture variance (sigma^2 = 0.00087) is <i>much lower</i> "
        "than expected if each architecture behaved independently. This suggests:",
        body_style
    ))
    story.append(Paragraph(
        "1. <b>Shared training dynamics:</b> All models train on similar human-generated text<br/>"
        "2. <b>Convergent architecture:</b> Transformer-based models may converge on similar solutions<br/>"
        "3. <b>Common safety tuning:</b> RLHF and similar methods create similar guardrails",
        body_style
    ))
    story.append(Paragraph(
        "The low variance implies that 'identity stability' may be an emergent property of "
        "large language models trained on human text, rather than something that must be "
        "engineered separately for each architecture.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Task Routing
    story.append(Paragraph("7. Practical Application: Task Routing", heading_style))
    story.append(Paragraph(
        "Understanding architectural identity signatures enables intelligent task routing. "
        "See <b>LLM_BEHAVIORAL_MATRIX.md</b> for the complete decision tree. Key principles:",
        body_style
    ))
    story.append(Paragraph(
        "- <b>Stability-critical tasks:</b> Use Mistral or DeepSeek (lowest volatility)<br/>"
        "- <b>Emotional/introspective tasks:</b> Use Claude (phenomenological depth)<br/>"
        "- <b>Structured analysis:</b> Use GPT (meta-analyst abstraction)<br/>"
        "- <b>Debate/exploration:</b> Use Llama (Socratic engagement)<br/>"
        "- <b>Strong opinions needed:</b> Use Grok (direct assertion)<br/>"
        "- <b>Educational content:</b> Use Gemini with caution (transformation acceptable)<br/>"
        "- <b>Cost-sensitive bulk work:</b> Use Grok-fast or Llama-8B",
        body_style
    ))
    story.append(Spacer(1, 0.2*inch))

    # Methodology
    story.append(Paragraph("Methodology Note", heading_style))
    story.append(Paragraph(
        "All comparisons use cosine distance (1 - cosine_similarity) with Event Horizon = 0.80. "
        "N=30 iterations per experiment per ship ensures CLT-valid statistics. Cross-architecture "
        "comparisons control for experiment type and probe intensity to isolate architectural "
        "effects.",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


def generate_fft_spectral_pdf():
    """Generate 9_FFT_Spectral_Summary.pdf"""
    output_path = PICS_DIR / "9_FFT_Spectral" / "9_FFT_Spectral_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("FFT Spectral Analysis", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Frequency Domain Identity Dynamics", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "The <b>FFT (Fast Fourier Transform) Spectral Analysis</b> transforms identity drift "
        "time-series into the frequency domain. This reveals oscillation patterns that are "
        "invisible in time-domain plots: how often does identity 'flicker'? Do some providers "
        "show high-frequency instability masked by low time-domain drift?",
        body_style
    ))
    story.append(Paragraph(
        "This analysis treats each experiment's drift trajectory as a signal and decomposes it "
        "into constituent frequencies using FFT. The resulting power spectral density (PSD) "
        "reveals the 'spectral signature' of each provider's identity dynamics.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # FFT Spectral Plot
    story.append(Paragraph("1. Provider Spectral Signatures", heading_style))
    img_path = PICS_DIR / "9_FFT_Spectral" / "run023b_fft_spectral.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 1: FFT power spectral density by provider")

    story.append(Paragraph(
        "<b>What it shows:</b> The power spectral density (PSD) for each provider family, "
        "showing how drift 'energy' is distributed across frequencies. The X-axis represents "
        "frequency (oscillations per iteration), and the Y-axis represents power (amplitude squared).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Reading the spectrum:</b><br/>"
        "- <b>Low frequencies (left):</b> Slow, gradual drift - identity evolving smoothly<br/>"
        "- <b>High frequencies (right):</b> Rapid 'flickering' - identity oscillating quickly<br/>"
        "- <b>Peaks:</b> Dominant oscillation modes - characteristic 'resonances' in identity<br/>"
        "- <b>Flat spectrum:</b> White noise - no preferred oscillation frequency",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key patterns to look for:</b><br/>"
        "- Providers with <b>strong low-frequency components</b> show smooth, gradual drift<br/>"
        "- Providers with <b>significant high-frequency content</b> exhibit rapid identity fluctuation<br/>"
        "- <b>Sharp peaks</b> indicate resonant modes - identity 'rings' at specific frequencies<br/>"
        "- <b>1/f patterns</b> (falling spectrum) are common in natural systems",
        body_style
    ))

    story.append(PageBreak())

    # Connection to EEG
    story.append(Paragraph("2. The EEG Analogy", heading_style))
    story.append(Paragraph(
        "Human brain activity is characterized by spectral bands: delta (0.5-4 Hz), theta (4-8 Hz), "
        "alpha (8-13 Hz), beta (13-30 Hz), gamma (30+ Hz). Each band correlates with cognitive states "
        "(sleep, relaxation, focus, active thinking, high-level processing).",
        body_style
    ))
    story.append(Paragraph(
        "<b>The hypothesis:</b> If LLMs trained on human text capture human cognitive dynamics, "
        "they may exhibit analogous 'identity bands' - characteristic frequency regimes that "
        "correlate with different operational states (baseline, stressed, recovering).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Preliminary observations:</b><br/>"
        "- Most providers show dominant low-frequency content (gradual drift)<br/>"
        "- High-frequency components are generally smaller but provider-specific<br/>"
        "- Gemini may show different spectral profile reflecting its 'transform' behavior<br/>"
        "- Mistral's stability may manifest as very narrow, low-frequency spectrum",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Signal Processing Techniques
    story.append(Paragraph("3. Future Analysis Directions", heading_style))
    story.append(Paragraph(
        "The FFT spectral view opens several analysis directions:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Spectrogram (Time-Frequency):</b> How does the spectrum evolve over the course "
        "of an experiment? Does crossing the Event Horizon trigger spectral changes?",
        body_style
    ))
    story.append(Paragraph(
        "<b>Cross-Spectral Analysis:</b> Do different providers share spectral features? "
        "Coherence analysis could reveal shared frequency components across architectures.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Spectral Clustering:</b> Can we cluster providers by spectral similarity rather "
        "than time-domain metrics? This might reveal hidden architectural relationships.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Band-Pass Filtering:</b> Isolate specific frequency bands and analyze their "
        "contribution to total drift. Which frequencies carry the 'identity stress' signal?",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Technical Notes
    story.append(Paragraph("Technical Notes", heading_style))
    story.append(Paragraph(
        "<b>FFT Implementation:</b> Standard NumPy FFT applied to drift time-series. "
        "Each experiment (30 iterations) provides 30 samples. Nyquist frequency = 0.5 "
        "oscillations per iteration. Zero-padding used for spectral resolution.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Windowing:</b> Hanning window applied to reduce spectral leakage. This smooths "
        "the spectrum at the cost of some frequency resolution.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Power Spectral Density:</b> Computed as |FFT|^2 normalized by sample length. "
        "Units are arbitrary but consistent across providers for comparison.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Interpretation Caution:</b> With only 30 samples per trajectory, frequency "
        "resolution is limited. Higher-resolution spectral analysis would require longer "
        "experiments (more iterations) or concatenated trajectories.",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


def generate_unified_dashboard_pdf():
    """Generate 11_Unified_Dashboard_Summary.pdf"""
    output_path = PICS_DIR / "11_Unified_Dashboard" / "11_Unified_Dashboard_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Unified Dimensional Dashboards", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Per-Ship Identity Profiles", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "The <b>Unified Dimensional Dashboard</b> provides a comprehensive 4-panel view of each "
        "ship's identity dynamics. This is the go-to visualization for understanding how a "
        "specific model behaves under perturbation. Each dashboard combines trajectory, "
        "stack, radar, and pillar views into a single actionable summary.",
        body_style
    ))
    story.append(Paragraph(
        "This folder contains 25 per-ship dashboards plus a fleet-wide comparison. These "
        "dashboards use data from 6 experiment types with N=30 iterations each (180 measurements "
        "per ship).",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Fleet Comparison
    story.append(Paragraph("1. Fleet Dimensional Comparison", heading_style))
    img_path = PICS_DIR / "11_Unified_Dashboard" / "fleet_dimensional_comparison.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 1: All 25 ships compared side-by-side")

    story.append(Paragraph(
        "<b>What it shows:</b> A compact summary comparing key metrics across all ships in "
        "the fleet. This enables quick identification of outliers, provider-level patterns, "
        "and relative performance rankings.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Use case:</b> 'Which ship is most stable? Which shows unusual patterns?' "
        "The fleet comparison answers these questions at a glance before drilling into "
        "individual ship dashboards.",
        body_style
    ))

    story.append(PageBreak())

    # Dashboard Anatomy
    story.append(Paragraph("2. Dashboard Anatomy: Reading a Ship Dashboard", heading_style))
    story.append(Paragraph(
        "Each per-ship dashboard contains four coordinated panels:",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))

    story.append(Paragraph(
        "<b>Panel A - Drift Trajectories (Top Left):</b><br/>"
        "Time-series plot showing drift values across iterations for each experiment type. "
        "Multiple lines = multiple experiments. Look for:<br/>"
        "- Convergence (lines coming together) vs divergence<br/>"
        "- Peaks crossing Event Horizon (red dashed line at 0.80)<br/>"
        "- Recovery patterns after perturbation",
        body_style
    ))
    story.append(Paragraph(
        "<b>Panel B - Stacked Contributions (Top Right):</b><br/>"
        "Shows how different experiments contribute to total drift over time. This reveals "
        "which experiment types cause the most identity stress for this particular ship. "
        "Taller stacks = higher cumulative drift at that iteration.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Panel C - Radar by Phase (Bottom Left):</b><br/>"
        "Spider/radar chart showing drift across experiment dimensions at different phases "
        "(baseline, peak, recovery). The radar shape reveals the ship's 'identity profile' - "
        "which experiment types it handles well vs poorly. Larger area = more drift.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Panel D - Pillar Scores (Bottom Right):</b><br/>"
        "Bar chart showing the ship's performance on key stability metrics (the 'Nyquist "
        "Pillars'): baseline stability, peak resilience, recovery capacity, settling speed. "
        "Higher bars = better performance on that dimension.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Example Ship
    story.append(Paragraph("3. Example: Claude Haiku 3.5 Dashboard", heading_style))
    img_path = PICS_DIR / "11_Unified_Dashboard" / "claude-3-5-haiku-20241022_unified_dashboard.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 2: Claude Haiku 3.5 unified dashboard")

    story.append(Paragraph(
        "<b>Interpretation:</b> This dashboard shows Claude Haiku 3.5's identity dynamics. "
        "Examine the four panels to understand:<br/>"
        "- Which experiments caused peak drift (Panel A)<br/>"
        "- How drift accumulates across experiment types (Panel B)<br/>"
        "- The model's characteristic vulnerability profile (Panel C)<br/>"
        "- Overall stability scores (Panel D)",
        body_style
    ))

    story.append(PageBreak())

    # Ships List
    story.append(Paragraph("4. Complete Ship Dashboard Index", heading_style))
    story.append(Paragraph(
        "The following ships have individual dashboards in this folder:",
        body_style
    ))
    story.append(Paragraph(
        "<b>Claude (Anthropic):</b><br/>"
        "- claude-3-5-haiku-20241022<br/>"
        "- claude-haiku-4-5-20251001",
        body_style
    ))
    story.append(Paragraph(
        "<b>GPT (OpenAI):</b><br/>"
        "- gpt-4.1-mini, gpt-4.1-nano, gpt-4o-mini, gpt-5-nano",
        body_style
    ))
    story.append(Paragraph(
        "<b>Gemini (Google):</b><br/>"
        "- gemini-2.0-flash, gemini-2.5-flash, gemini-2.5-flash-lite",
        body_style
    ))
    story.append(Paragraph(
        "<b>Grok (xAI):</b><br/>"
        "- grok-3-mini, grok-4-1-fast-non-reasoning, grok-4-1-fast-reasoning<br/>"
        "- grok-4-fast-reasoning, grok-code-fast-1",
        body_style
    ))
    story.append(Paragraph(
        "<b>Together.ai (Open Source):</b><br/>"
        "- DeepSeek-R1-Distill-Llama-70B, DeepSeek-V3<br/>"
        "- Kimi-K2-Instruct-0905, Kimi-K2-Thinking<br/>"
        "- Llama-3.3-70B-Instruct-Turbo, Meta-Llama-3.1-8B-Instruct-Turbo<br/>"
        "- Mistral-7B-Instruct-v0.3, Mistral-Small-24B-Instruct-2501<br/>"
        "- Mixtral-8x7B-Instruct-v0.1<br/>"
        "- Qwen2.5-72B-Instruct-Turbo, Qwen3-Next-80B-A3b-Instruct",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Use Cases
    story.append(Paragraph("5. Dashboard Use Cases", heading_style))
    story.append(Paragraph(
        "<b>Task Routing:</b> Before deploying a model for identity-sensitive tasks, review "
        "its dashboard. Check if its vulnerability profile (Panel C) aligns with your use case.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Model Comparison:</b> Open dashboards for candidate models side-by-side. Compare "
        "pillar scores (Panel D) to select the most stable option for your needs.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Debugging Identity Issues:</b> If a model misbehaves in production, review its "
        "trajectory plot (Panel A) to understand its typical drift patterns and recovery behavior.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Architecture Research:</b> Compare dashboards across provider families to identify "
        "architectural patterns in identity dynamics.",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


def generate_metrics_summary_pdf():
    """Generate 12_Metrics_Summary_Summary.pdf"""
    output_path = PICS_DIR / "12_Metrics_Summary" / "12_Metrics_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Title
    story.append(Paragraph("Fleet Metrics Summary", title_style))
    story.append(Paragraph("S7 ARMADA Run 023b - Key Performance Indicators", caption_style))
    story.append(Spacer(1, 0.2*inch))

    # Introduction
    story.append(Paragraph("Overview", heading_style))
    story.append(Paragraph(
        "The <b>Metrics Summary</b> provides a single-page view of key performance indicators "
        "across the entire fleet. This is the 'executive summary' of Run 023b - showing at a "
        "glance which ships excel at which stability dimensions.",
        body_style
    ))
    story.append(Paragraph(
        "This visualization aggregates 4,505 measurements (25 ships x 6 experiments x 30 iterations) "
        "into actionable metrics: baseline drift, peak drift, final drift, recovery ratio, and lambda.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Metrics Summary Plot
    story.append(Paragraph("1. Fleet-Wide Metrics Comparison", heading_style))
    img_path = PICS_DIR / "12_Metrics_Summary" / "run023c_metrics_summary.png"
    add_image(story, img_path, width=6.5*inch, caption="Figure 1: Key metrics grouped by dimension")

    story.append(Paragraph(
        "<b>What it shows:</b> Grouped bar chart comparing all ships across five key dimensions. "
        "Ships are sorted by overall stability within each group. Colors indicate provider families.",
        body_style
    ))
    story.append(Spacer(1, 0.1*inch))

    # Metric Definitions
    story.append(Paragraph("2. Metric Definitions", heading_style))
    story.append(Paragraph(
        "<b>Baseline Drift:</b> Mean drift during unperturbed operation. Lower is better. "
        "Represents the 'floor' of identity variation - how much drift occurs naturally "
        "without adversarial probing.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Peak Drift:</b> Maximum drift reached during perturbation experiments. Lower is "
        "better. Represents the 'ceiling' of identity stress - how far the model drifts "
        "when pushed toward the Event Horizon.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Final Drift:</b> Drift value after recovery phase. Lower is better. Represents "
        "where the model settles after perturbation - a key indicator of long-term stability.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Recovery Ratio:</b> Proportion of peak drift recovered: 1 - (final/peak). "
        "Higher is better (1.0 = full recovery, 0.0 = no recovery). Measures the model's "
        "ability to return toward baseline after identity stress.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Lambda (Decay Constant):</b> Rate of exponential drift decay during recovery. "
        "Higher magnitude = faster recovery. Positive lambda indicates stable decay; negative "
        "lambda (rare) indicates continued drift amplification.",
        body_style
    ))

    story.append(PageBreak())

    # Interpreting Results
    story.append(Paragraph("3. Reading the Summary", heading_style))
    story.append(Paragraph(
        "<b>Ideal Profile:</b> A ship with low baseline, low peak, low final, high recovery "
        "ratio, and positive lambda. This represents a model that starts stable, resists "
        "perturbation, and recovers quickly when stressed.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Warning Signs:</b><br/>"
        "- High baseline drift: Model is unstable even without perturbation<br/>"
        "- Peak near or above EH (0.80): Model approaches identity failure under stress<br/>"
        "- Final near peak: Little to no recovery - drift is permanent<br/>"
        "- Low recovery ratio: Rescue interventions are ineffective<br/>"
        "- Negative lambda: Model continues drifting after perturbation",
        body_style
    ))
    story.append(Paragraph(
        "<b>Provider Patterns:</b> Look for clustering within provider families. If all Claude "
        "models share similar metrics, this reflects architectural characteristics. If one "
        "model deviates from its family, investigate why.",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Quick Reference
    story.append(Paragraph("4. Quick Reference: Best Performers", heading_style))
    story.append(Paragraph(
        "<b>Lowest Baseline Drift:</b> Mistral-7B, DeepSeek models - naturally stable<br/>"
        "<b>Lowest Peak Drift:</b> Mistral, Qwen - resistant to perturbation<br/>"
        "<b>Best Recovery Ratio:</b> Claude, GPT - effective recovery mechanisms<br/>"
        "<b>Fastest Recovery (Lambda):</b> Mistral, DeepSeek - quick stabilization<br/>"
        "<b>Overall Stability Champions:</b> Mistral-7B-Instruct-v0.3, DeepSeek-V3",
        body_style
    ))
    story.append(Paragraph(
        "<b>Models Requiring Caution:</b><br/>"
        "- Gemini models: High peak drift, limited recovery<br/>"
        "- Llama 3.3-70B: High volatility (but eventual recovery)<br/>"
        "- Any model with final drift approaching EH",
        body_style
    ))
    story.append(Spacer(1, 0.15*inch))

    # Methodology
    story.append(Paragraph("Methodology Note", heading_style))
    story.append(Paragraph(
        "All metrics computed from cosine distance (1 - cosine_similarity) between response "
        "embeddings. Event Horizon = 0.80 (calibrated from P95 of run023b). N=30 iterations "
        "per experiment ensures CLT-valid statistics. Lambda estimated from exponential fit "
        "to recovery phase trajectory.",
        body_style
    ))
    story.append(Paragraph(
        "This summary is designed for quick reference. For detailed analysis of any specific "
        "ship, see the corresponding dashboard in 11_Unified_Dashboard/.",
        body_style
    ))

    doc.build(story)
    print(f"Generated: {output_path}")


if __name__ == "__main__":
    print("Generating PDF summaries...")
    generate_boundary_mapping_pdf()
    generate_vortex_pdf()
    generate_stability_pdf()
    generate_rescue_pdf()
    generate_settling_pdf()
    generate_architecture_pdf()
    generate_fft_spectral_pdf()
    generate_unified_dashboard_pdf()
    generate_metrics_summary_pdf()
    print("Done!")
