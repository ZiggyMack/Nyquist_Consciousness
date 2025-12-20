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


if __name__ == "__main__":
    print("Generating PDF summaries...")
    generate_boundary_mapping_pdf()
    generate_vortex_pdf()
    generate_stability_pdf()
    generate_rescue_pdf()
    print("Done!")
