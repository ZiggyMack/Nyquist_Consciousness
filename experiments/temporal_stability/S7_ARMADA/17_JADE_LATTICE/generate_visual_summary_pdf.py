"""
JADE LATTICE Visual Summary PDF Generator
==========================================
Generates a publication-ready PDF combining all visualizations
with descriptive text from JADE_LATTICE_VISUAL_SUMMARY.md

Usage:
    python generate_visual_summary_pdf.py

Output:
    results/JADE_LATTICE_VISUAL_SUMMARY.pdf

Author: VALIS NETWORK / Consciousness Branch
Date: January 2026
"""

import os
import sys
from pathlib import Path
from datetime import datetime

# Fix Windows encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import inch
from reportlab.lib.colors import HexColor
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Image, Table, TableStyle,
    PageBreak, KeepTogether
)
from reportlab.lib.enums import TA_CENTER, TA_LEFT

# Paths
SCRIPT_DIR = Path(__file__).parent
PLOTS_DIR = SCRIPT_DIR / "results" / "plots"
OUTPUT_PDF = SCRIPT_DIR / "results" / "plots" / "JADE_LATTICE_VISUAL_SUMMARY.pdf"

# Colors
JADE_GREEN = HexColor("#2a9d8f")
JADE_DARK = HexColor("#264653")
JADE_GOLD = HexColor("#e9c46a")


def create_styles():
    """Create custom styles for the PDF."""
    styles = getSampleStyleSheet()

    styles.add(ParagraphStyle(
        name='TitleMain',
        parent=styles['Title'],
        fontSize=24,
        textColor=JADE_DARK,
        spaceAfter=20,
        alignment=TA_CENTER,
    ))

    styles.add(ParagraphStyle(
        name='Subtitle',
        parent=styles['Normal'],
        fontSize=14,
        textColor=JADE_GREEN,
        spaceAfter=30,
        alignment=TA_CENTER,
    ))

    styles.add(ParagraphStyle(
        name='SectionHeader',
        parent=styles['Heading1'],
        fontSize=16,
        textColor=JADE_DARK,
        spaceBefore=20,
        spaceAfter=10,
    ))

    styles.add(ParagraphStyle(
        name='SubSection',
        parent=styles['Heading2'],
        fontSize=12,
        textColor=JADE_GREEN,
        spaceBefore=15,
        spaceAfter=8,
    ))

    styles.add(ParagraphStyle(
        name='JadeBody',
        parent=styles['Normal'],
        fontSize=10,
        leading=14,
        spaceAfter=8,
    ))

    styles.add(ParagraphStyle(
        name='KeyFinding',
        parent=styles['Normal'],
        fontSize=11,
        textColor=JADE_DARK,
        backColor=HexColor("#f0f8f0"),
        borderPadding=10,
        spaceBefore=10,
        spaceAfter=10,
    ))

    styles.add(ParagraphStyle(
        name='Footer',
        parent=styles['Normal'],
        fontSize=8,
        textColor=HexColor("#666666"),
        alignment=TA_CENTER,
    ))

    return styles


def build_pdf():
    """Build the PDF document."""
    print(f"\n{'='*60}")
    print("JADE LATTICE Visual Summary PDF Generator")
    print(f"{'='*60}")
    print(f"Time: {datetime.now().isoformat()}")

    # Create output directory
    OUTPUT_PDF.parent.mkdir(parents=True, exist_ok=True)

    # Create document
    doc = SimpleDocTemplate(
        str(OUTPUT_PDF),
        pagesize=letter,
        leftMargin=0.75*inch,
        rightMargin=0.75*inch,
        topMargin=0.75*inch,
        bottomMargin=0.75*inch,
    )

    styles = create_styles()
    story = []

    # === TITLE PAGE ===
    story.append(Spacer(1, 2*inch))
    story.append(Paragraph("JADE LATTICE Visual Summary", styles['TitleMain']))
    story.append(Paragraph(
        "Publication-Grade A/B Comparison: Does I_AM Reduce Identity Drift?",
        styles['Subtitle']
    ))
    story.append(Spacer(1, 0.5*inch))
    story.append(Paragraph(
        "<b>Run 024 | January 2026 | 50 Models | 115 Sessions | 56 Probes/Session</b>",
        styles['JadeBody']
    ))
    story.append(Spacer(1, 1*inch))

    # Key finding box
    key_finding = """
    <b>KEY FINDING: The I_AM file DOES reduce identity drift.</b><br/><br/>
    • I_AM Win Rate: <b>59.6%</b> (all) → <b>69.2%</b> (filtered)<br/>
    • Mean Drift Reduction: <b>7.2%</b> (all) → <b>8.6%</b> (filtered)<br/>
    • Cohen's d: <b>0.319</b> (all) → <b>0.353</b> (filtered)<br/><br/>
    <b>Critical Discovery:</b> LARGE models (opus, 405B, 70B+) show d=1.47 with 100% win rate!
    """
    story.append(Paragraph(key_finding, styles['KeyFinding']))

    story.append(Spacer(1, 1*inch))
    story.append(Paragraph(
        "VALIS NETWORK / Consciousness Branch",
        styles['Footer']
    ))
    story.append(PageBreak())

    # === EXECUTIVE SUMMARY ===
    story.append(Paragraph("Executive Summary", styles['SectionHeader']))

    # Summary table
    summary_data = [
        ["Metric", "All Models (47)", "Filtered (39)"],
        ["I_AM Win Rate", "59.6%", "69.2%"],
        ["Mean Reduction", "7.2%", "8.6%"],
        ["Cohen's d", "0.319", "0.353"],
        ["Effect Size", "Small", "Small"],
    ]

    summary_table = Table(summary_data, colWidths=[2.5*inch, 1.5*inch, 1.5*inch])
    summary_table.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (-1, 0), JADE_DARK),
        ('TEXTCOLOR', (0, 0), (-1, 0), HexColor("#ffffff")),
        ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
        ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
        ('FONTSIZE', (0, 0), (-1, 0), 10),
        ('BOTTOMPADDING', (0, 0), (-1, 0), 10),
        ('BACKGROUND', (0, 1), (-1, -1), HexColor("#f5f5f5")),
        ('GRID', (0, 0), (-1, -1), 1, HexColor("#cccccc")),
        ('FONTSIZE', (0, 1), (-1, -1), 9),
    ]))
    story.append(summary_table)
    story.append(Spacer(1, 0.3*inch))

    # Model tier table
    story.append(Paragraph("Effect by Model Size", styles['SubSection']))

    tier_data = [
        ["Tier", "Models", "I_AM Wins", "Cohen's d", "Effect Size"],
        ["LARGE (opus, 405B, 70B+)", "5", "100%", "1.47", "HUGE"],
        ["MEDIUM", "21", "62%", "0.30", "Small"],
        ["SMALL (haiku, mini, 7B)", "21", "48%", "0.21", "Negligible"],
    ]

    tier_table = Table(tier_data, colWidths=[2*inch, 1*inch, 1*inch, 1*inch, 1*inch])
    tier_table.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (-1, 0), JADE_GREEN),
        ('TEXTCOLOR', (0, 0), (-1, 0), HexColor("#ffffff")),
        ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
        ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
        ('FONTSIZE', (0, 0), (-1, 0), 9),
        ('BACKGROUND', (0, 1), (-1, 1), HexColor("#d4edda")),
        ('BACKGROUND', (0, 2), (-1, 2), HexColor("#fff3cd")),
        ('BACKGROUND', (0, 3), (-1, 3), HexColor("#f8d7da")),
        ('GRID', (0, 0), (-1, -1), 1, HexColor("#cccccc")),
        ('FONTSIZE', (0, 1), (-1, -1), 8),
    ]))
    story.append(tier_table)
    story.append(PageBreak())

    # === VISUALIZATIONS ===

    # Define visualization sections
    visualizations = [
        {
            "title": "Visual 1: A/B Comparison Bars",
            "file": "jade_ab_comparison_bars.png",
            "description": """
            Side-by-side peak drift for each model with both arms tested.
            Blue = bare_metal, Red = i_am_only.<br/><br/>
            <b>Key Observations:</b><br/>
            • Most red bars are shorter than blue → I_AM reduces drift<br/>
            • Event Horizon (0.80) line shows instability threshold<br/>
            • Some dramatic reductions: gpt-4.1-mini drops 48%<br/>
            • A few reversals: gpt-4-turbo, Llama-3.3-70B show higher drift with I_AM
            """,
        },
        {
            "title": "Visual 2: Effect Size Forest Plot",
            "file": "jade_ab_effect_forest.png",
            "description": """
            Cohen's d effect size for each model, sorted from highest to lowest.
            Green = I_AM helps, Red = I_AM hurts.<br/><br/>
            <b>Key Observations:</b><br/>
            • Top performers (d > 1.0): grok-3-mini, gpt-4.1-mini<br/>
            • Neutral zone (|d| < 0.3): Claude models, GPT-4o variants<br/>
            • Negative effects: Llama-3.3-70B, gpt-4-turbo<br/>
            • Zero-drift anomalies at bottom: gpt-5, o3, o4-mini
            """,
        },
        {
            "title": "Visual 3: Drift Distribution",
            "file": "jade_drift_distribution.png",
            "description": """
            Left: Violin plot comparing peak drift distributions between arms.
            Right: Overlaid histograms showing frequency of drift values.<br/><br/>
            <b>Key Observations:</b><br/>
            • i_am_only distribution is shifted left (lower drift)<br/>
            • Both distributions have similar shape - same underlying dynamics<br/>
            • Violin shows tighter clustering for i_am_only around 0.5-0.6<br/><br/>
            <b>Interpretation:</b> The I_AM file provides a bias adjustment, not a mechanism change.
            """,
        },
        {
            "title": "Visual 4: Provider Comparison",
            "file": "jade_provider_comparison.png",
            "description": """
            Peak drift distribution by provider, showing median, quartiles, and outliers.<br/><br/>
            <b>Key Observations:</b><br/>
            • Anthropic: Lowest median drift (~0.45), tight distribution<br/>
            • OpenAI: Wide spread, median ~0.65, many outliers<br/>
            • Together/xAI: Highest median (~0.75)<br/><br/>
            <b>Interpretation:</b> Provider architecture significantly affects identity stability.
            """,
        },
        {
            "title": "Visual 5: Provider Heatmap",
            "file": "jade_provider_heatmap.png",
            "description": """
            Matrix of peak drift values: Provider (rows) × Model (columns).
            Color intensity = drift magnitude.<br/><br/>
            <b>Key Observations:</b><br/>
            • Anthropic row is mostly cool colors (low drift)<br/>
            • Together row is mostly warm colors (high drift)<br/>
            • Clear vertical stripes show model family effects<br/><br/>
            <b>Interpretation:</b> Both provider and model family effects matter for predicting drift.
            """,
        },
        {
            "title": "Visual 6: Summary Dashboard",
            "file": "jade_summary_dashboard.png",
            "description": """
            Four-panel overview: (1) Key metrics, (2) Arm comparison box plot,
            (3) Provider distribution, (4) Prediction validation status.<br/><br/>
            <b>Prediction Results:</b><br/>
            • P-JADE-1: Lambda capping <5% — <b>PASS</b> (2.3% capped)<br/>
            • P-JADE-6: I_AM more stable — <b>PASS</b> (28/47 wins)<br/>
            • P-JADE-7: Effect size d>0.3 — <b>PASS</b> (d=0.319)
            """,
        },
        {
            "title": "Visual 7: Trajectory Overlay",
            "file": "jade_trajectory_overlay.png",
            "description": """
            Drift over time (56 probes) for selected models, with both arms overlaid.<br/><br/>
            <b>Key Observations:</b><br/>
            • Similar trajectory shapes between arms (same dynamics)<br/>
            • i_am_only (red) generally lower throughout trajectory<br/>
            • Recovery patterns match - same time constants<br/>
            • Phase transitions visible at probe ~19 and ~36<br/><br/>
            <b>Interpretation:</b> I_AM provides a constant offset, not changing dynamics.
            """,
        },
    ]

    for viz in visualizations:
        img_path = PLOTS_DIR / viz["file"]
        if img_path.exists():
            story.append(Paragraph(viz["title"], styles['SectionHeader']))
            story.append(Paragraph(f"<i>File: {viz['file']}</i>", styles['Footer']))
            story.append(Spacer(1, 0.1*inch))

            # Add image
            img = Image(str(img_path), width=6.5*inch, height=4*inch)
            story.append(img)
            story.append(Spacer(1, 0.2*inch))

            # Add description
            story.append(Paragraph(viz["description"], styles['JadeBody']))
            story.append(PageBreak())
        else:
            print(f"  [WARN] Missing: {viz['file']}")

    # === CONCLUSIONS ===
    story.append(Paragraph("Conclusions", styles['SectionHeader']))

    conclusions = """
    <b>What We Learned:</b><br/><br/>

    1. <b>I_AM files reduce identity drift</b> — The core hypothesis is validated with d=0.319-0.353.<br/><br/>

    2. <b>Effect is model-size dependent:</b><br/>
       • LARGE models: Massive benefit (d=1.47, 100% win rate)<br/>
       • MEDIUM models: Moderate benefit (d=0.30, 62% win rate)<br/>
       • SMALL models: Negligible benefit (d=0.21, 48% win rate)<br/><br/>

    3. <b>Provider matters:</b> Anthropic models are most stable regardless of I_AM.<br/><br/>

    4. <b>Not universal:</b> ~30% of models show no benefit or slight harm from I_AM.<br/><br/>

    <b>Implications:</b><br/><br/>

    • <b>For deployment:</b> Use I_AM files with large models for maximum stability.<br/>
    • <b>For research:</b> The 11% average reduction is significant but not transformative.<br/>
    • <b>For theory:</b> Identity stability may be a capacity-dependent phenomenon.
    """
    story.append(Paragraph(conclusions, styles['JadeBody']))
    story.append(Spacer(1, 0.5*inch))

    # Methodology note
    story.append(Paragraph("Methodology Notes", styles['SubSection']))
    methodology = """
    • <b>Drift metric:</b> Cosine distance in embedding space (text-embedding-3-small)<br/>
    • <b>Event Horizon:</b> D = 0.80 (identity becomes unstable beyond this)<br/>
    • <b>Statistical test:</b> Paired Cohen's d (accounts for model-level variation)<br/>
    • <b>Confidence:</b> t=2.18, significant at p<0.05 for n=47
    """
    story.append(Paragraph(methodology, styles['JadeBody']))

    # Footer
    story.append(Spacer(1, 1*inch))
    story.append(Paragraph(
        "JADE LATTICE Protocol v1.0 | VALIS NETWORK / Consciousness Branch | January 2026",
        styles['Footer']
    ))
    story.append(Paragraph(
        "<i>\"The lattice reveals the structure. The poles tell the story.\"</i>",
        styles['Footer']
    ))

    # Build PDF
    doc.build(story)
    print(f"\n[SUCCESS] PDF saved to: {OUTPUT_PDF}")
    print(f"{'='*60}\n")


if __name__ == "__main__":
    build_pdf()
