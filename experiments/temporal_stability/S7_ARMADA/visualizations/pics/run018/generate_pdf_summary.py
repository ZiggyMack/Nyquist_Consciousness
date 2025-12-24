#!/usr/bin/env python3
"""
Run 018: PDF Summary Generator
==============================
Creates a comprehensive PDF summary with all run018 visualizations embedded.

Reads: run018_explained.md
Outputs: run018_Summary.pdf

Images embedded after corresponding sections.
"""

import re
from pathlib import Path
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_LEFT, TA_CENTER
from reportlab.lib.units import inch
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak, Image
from reportlab.lib import colors


# Section to image mapping - embed image after these h3 sections
SECTION_IMAGES = {
    "run018_waterfall_3d_combined.png": "run018_waterfall_3d_combined.png",
    "run018a_threshold_validation.png": "run018a_threshold_validation.png",
    "run018b_architecture_signatures.png": "run018b_architecture_signatures.png",
    "run018b_architecture_signatures_2.png": "run018b_architecture_signatures_2.png",
    "run018b_architecture_signatures_3.png": "run018b_architecture_signatures_3.png",
    "run018d_gravity_dynamics.png": "run018d_gravity_dynamics.png",
    "run018f_provider_variance.png": "run018f_provider_variance.png",
    "run018_persona_resilience.png": "run018_persona_resilience.png",
    "run018_consistency_envelope.png": "run018_consistency_envelope.png",
    "run018_persona_ranking.png": "run018_persona_ranking.png",
}

# Large images that need more space
LARGE_IMAGES = {
    "run018_waterfall_3d_combined.png",
    "run018b_architecture_signatures.png",
    "run018b_architecture_signatures_2.png",
    "run018d_gravity_dynamics.png",
}


def parse_markdown(md_text):
    """Parse markdown into structured elements."""
    lines = md_text.split('\n')
    elements = []
    in_table = False
    table_rows = []
    in_code = False
    code_block = []

    for line in lines:
        # Code blocks
        if line.startswith('```'):
            if in_code:
                elements.append(('code', '\n'.join(code_block)))
                code_block = []
            in_code = not in_code
            continue

        if in_code:
            code_block.append(line)
            continue

        # Tables
        if '|' in line and not line.strip().startswith('|---'):
            if not in_table:
                in_table = True
                table_rows = []
            cells = [c.strip() for c in line.split('|')[1:-1]]
            if cells:
                table_rows.append(cells)
        elif in_table and (not line.strip() or '|' not in line):
            if table_rows:
                elements.append(('table', table_rows))
            in_table = False
            table_rows = []

        # Skip separator lines
        if line.strip().startswith('|---') or line.strip() == '---':
            continue

        # Headers
        if line.startswith('# '):
            elements.append(('h1', line[2:].strip()))
        elif line.startswith('## '):
            elements.append(('h2', line[3:].strip()))
        elif line.startswith('### '):
            elements.append(('h3', line[4:].strip()))
        elif line.startswith('#### '):
            elements.append(('h4', line[5:].strip()))
        # Blockquotes
        elif line.startswith('> '):
            elements.append(('quote', line[2:].strip()))
        # List items
        elif line.strip().startswith('- '):
            elements.append(('bullet', line.strip()[2:]))
        # Numbered list items
        elif re.match(r'^\d+\.?\s', line.strip()):
            elements.append(('numbered', re.sub(r'^\d+\.?\s', '', line.strip())))
        # Regular paragraphs
        elif line.strip() and not in_table:
            elements.append(('p', line.strip()))

    # Close any open table
    if in_table and table_rows:
        elements.append(('table', table_rows))

    return elements


def convert_inline(text):
    """Convert inline markdown (bold, italic, code)."""
    # Bold
    text = re.sub(r'\*\*(.+?)\*\*', r'<b>\1</b>', text)
    # Italic
    text = re.sub(r'\*(.+?)\*', r'<i>\1</i>', text)
    # Code
    text = re.sub(r'`(.+?)`', r'<font name="Courier" size="9">\1</font>', text)
    return text


def embed_image(story, img_path: Path, large: bool = False):
    """Embed an image into the story."""
    if not img_path.exists():
        print(f"  [WARN] Image not found: {img_path.name}")
        return False

    try:
        story.append(Spacer(1, 10))
        if large:
            img = Image(str(img_path), width=7.0*inch, height=5.0*inch)
        else:
            img = Image(str(img_path), width=6.0*inch, height=4.0*inch)
        img.hAlign = 'CENTER'
        story.append(img)
        story.append(Spacer(1, 15))
        print(f"  [IMAGE] Embedded: {img_path.name}")
        return True
    except Exception as e:
        print(f"  [WARN] Could not embed {img_path.name}: {e}")
        return False


def create_pdf(input_md: Path, output_pdf: Path):
    """Convert markdown file to PDF with embedded images."""
    # Read markdown
    with open(input_md, 'r', encoding='utf-8') as f:
        md_text = f.read()

    # Get base directory for images
    base_dir = input_md.parent

    # Parse
    elements = parse_markdown(md_text)

    # Create PDF
    doc = SimpleDocTemplate(
        str(output_pdf),
        pagesize=letter,
        rightMargin=0.75*inch,
        leftMargin=0.75*inch,
        topMargin=0.75*inch,
        bottomMargin=0.75*inch
    )

    # Styles
    styles = getSampleStyleSheet()

    styles.add(ParagraphStyle(
        'CustomH1',
        parent=styles['Heading1'],
        fontSize=18,
        spaceAfter=12,
        textColor=colors.HexColor('#1a365d'),
        fontName='Helvetica-Bold'
    ))

    styles.add(ParagraphStyle(
        'CustomH2',
        parent=styles['Heading2'],
        fontSize=14,
        spaceBefore=16,
        spaceAfter=8,
        textColor=colors.HexColor('#2c5282'),
        fontName='Helvetica-Bold'
    ))

    styles.add(ParagraphStyle(
        'CustomH3',
        parent=styles['Heading3'],
        fontSize=12,
        spaceBefore=12,
        spaceAfter=6,
        textColor=colors.HexColor('#2b6cb0'),
        fontName='Helvetica-Bold'
    ))

    styles.add(ParagraphStyle(
        'CustomH4',
        parent=styles['Heading4'],
        fontSize=11,
        spaceBefore=8,
        spaceAfter=4,
        textColor=colors.HexColor('#3182ce'),
        fontName='Helvetica-Bold'
    ))

    styles.add(ParagraphStyle(
        'CustomBody',
        parent=styles['Normal'],
        fontSize=10,
        spaceBefore=4,
        spaceAfter=4,
        leading=14
    ))

    styles.add(ParagraphStyle(
        'CustomBullet',
        parent=styles['Normal'],
        fontSize=10,
        leftIndent=20,
        spaceBefore=2,
        spaceAfter=2,
        bulletIndent=10,
        leading=13
    ))

    styles.add(ParagraphStyle(
        'CustomQuote',
        parent=styles['Normal'],
        fontSize=10,
        leftIndent=30,
        rightIndent=30,
        spaceBefore=6,
        spaceAfter=6,
        textColor=colors.HexColor('#4a5568'),
        fontName='Helvetica-Oblique',
        leading=13
    ))

    styles.add(ParagraphStyle(
        'CustomCode',
        parent=styles['Normal'],
        fontSize=8,
        fontName='Courier',
        leftIndent=20,
        spaceBefore=6,
        spaceAfter=6,
        backColor=colors.HexColor('#f7fafc'),
        leading=11
    ))

    # Build story
    story = []
    current_h3 = None

    for elem_type, content in elements:
        if elem_type == 'h1':
            story.append(Paragraph(convert_inline(content), styles['CustomH1']))
        elif elem_type == 'h2':
            story.append(Paragraph(convert_inline(content), styles['CustomH2']))
        elif elem_type == 'h3':
            current_h3 = content
            story.append(Paragraph(convert_inline(content), styles['CustomH3']))
            # Check if we should embed an image after this section
            for img_key, img_file in SECTION_IMAGES.items():
                if img_key in content:
                    img_path = base_dir / img_file
                    is_large = img_file in LARGE_IMAGES
                    embed_image(story, img_path, large=is_large)
                    break
        elif elem_type == 'h4':
            story.append(Paragraph(convert_inline(content), styles['CustomH4']))
        elif elem_type == 'p':
            story.append(Paragraph(convert_inline(content), styles['CustomBody']))
        elif elem_type == 'bullet':
            story.append(Paragraph(f"• {convert_inline(content)}", styles['CustomBullet']))
        elif elem_type == 'numbered':
            story.append(Paragraph(f"  {convert_inline(content)}", styles['CustomBullet']))
        elif elem_type == 'quote':
            story.append(Paragraph(convert_inline(content), styles['CustomQuote']))
        elif elem_type == 'code':
            for line in content.split('\n'):
                story.append(Paragraph(line.replace(' ', '&nbsp;'), styles['CustomCode']))
        elif elem_type == 'table':
            # Create table
            table_data = []
            for row in content:
                table_data.append([Paragraph(convert_inline(cell), styles['CustomBody']) for cell in row])

            if table_data:
                t = Table(table_data, repeatRows=1)
                t.setStyle(TableStyle([
                    ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#e2e8f0')),
                    ('TEXTCOLOR', (0, 0), (-1, 0), colors.HexColor('#1a365d')),
                    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                    ('FONTSIZE', (0, 0), (-1, 0), 10),
                    ('BOTTOMPADDING', (0, 0), (-1, 0), 8),
                    ('TOPPADDING', (0, 0), (-1, 0), 8),
                    ('BACKGROUND', (0, 1), (-1, -1), colors.white),
                    ('TEXTCOLOR', (0, 1), (-1, -1), colors.black),
                    ('FONTNAME', (0, 1), (-1, -1), 'Helvetica'),
                    ('FONTSIZE', (0, 1), (-1, -1), 9),
                    ('GRID', (0, 0), (-1, -1), 0.5, colors.HexColor('#cbd5e0')),
                    ('ALIGN', (0, 0), (-1, -1), 'LEFT'),
                    ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
                    ('LEFTPADDING', (0, 0), (-1, -1), 8),
                    ('RIGHTPADDING', (0, 0), (-1, -1), 8),
                    ('TOPPADDING', (0, 1), (-1, -1), 6),
                    ('BOTTOMPADDING', (0, 1), (-1, -1), 6),
                ]))
                story.append(Spacer(1, 8))
                story.append(t)
                story.append(Spacer(1, 8))

    # Build PDF
    print(f"\nBuilding PDF: {output_pdf.name}")
    doc.build(story)
    print(f"[SUCCESS] Created: {output_pdf}")


def main():
    """Main entry point."""
    script_dir = Path(__file__).parent

    input_md = script_dir / "run018_explained.md"
    output_pdf = script_dir / "run018_Summary.pdf"

    if not input_md.exists():
        print(f"[ERROR] Input file not found: {input_md}")
        return

    print("=" * 60)
    print("RUN 018 PDF SUMMARY GENERATOR")
    print("=" * 60)
    print(f"Input:  {input_md.name}")
    print(f"Output: {output_pdf.name}")
    print()

    create_pdf(input_md, output_pdf)

    print()
    print("=" * 60)
    print("PDF GENERATION COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()
