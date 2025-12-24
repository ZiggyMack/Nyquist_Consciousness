#!/usr/bin/env python3
"""
15_Oobleck_Effect: PDF Summary Generator
=========================================
Creates a PDF summary with all Oobleck Effect visualizations embedded.

Reads: 15_oobleck_effect_explained.md
Outputs: 15_Oobleck_Effect_Summary.pdf

Images embedded in order:
1. oobleck_phase_breakdown.png - 020A phase dynamics
2. oobleck_trajectory_overlay.png - 020A trajectories
3. oobleck_control_treatment.png - 020B aggregate
4. oobleck_per_model_breakdown.png - 020B per-model (CRITICAL LIMITATION)
5. oobleck_thermometer.png - Thermometer analogy
6. oobleck_cross_platform.png - Cross-platform summary
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
    "1. oobleck_phase_breakdown.png": "oobleck_phase_breakdown.png",
    "2. oobleck_trajectory_overlay.png": "oobleck_trajectory_overlay.png",
    "3. oobleck_control_treatment.png": "oobleck_control_treatment.png",
    "4. oobleck_per_model_breakdown.png": "oobleck_per_model_breakdown.png",
    "5. oobleck_thermometer.png": "oobleck_thermometer.png",
    "6. oobleck_cross_platform.png": "oobleck_cross_platform.png",
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
    text = re.sub(r'`(.+?)`', r'<font name="Courier">\1</font>', text)
    return text


def embed_image(story, img_path: Path, large: bool = False):
    """Embed an image into the story."""
    if not img_path.exists():
        print(f"  [WARN] Image not found: {img_path.name}")
        return False

    try:
        story.append(Spacer(1, 10))
        if large:
            img = Image(str(img_path), width=6.5*inch, height=4.5*inch)
        else:
            img = Image(str(img_path), width=5.5*inch, height=3.5*inch)
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
        name='DocTitle',
        parent=styles['Heading1'],
        fontSize=18,
        spaceAfter=20,
        alignment=TA_CENTER
    ))
    styles.add(ParagraphStyle(
        name='DocH2',
        parent=styles['Heading2'],
        fontSize=14,
        spaceBefore=15,
        spaceAfter=10
    ))
    styles.add(ParagraphStyle(
        name='DocH3',
        parent=styles['Heading3'],
        fontSize=12,
        spaceBefore=12,
        spaceAfter=8
    ))
    styles.add(ParagraphStyle(
        name='DocH4',
        parent=styles['Heading4'],
        fontSize=11,
        spaceBefore=10,
        spaceAfter=6
    ))
    styles.add(ParagraphStyle(
        name='DocBody',
        parent=styles['Normal'],
        fontSize=10,
        spaceAfter=8
    ))
    styles.add(ParagraphStyle(
        name='DocBullet',
        parent=styles['Normal'],
        fontSize=10,
        spaceAfter=4,
        leftIndent=20,
        bulletIndent=10
    ))
    styles.add(ParagraphStyle(
        name='DocNumbered',
        parent=styles['Normal'],
        fontSize=10,
        spaceAfter=4,
        leftIndent=20,
    ))
    styles.add(ParagraphStyle(
        name='DocCode',
        parent=styles['Normal'],
        fontName='Courier',
        fontSize=8,
        spaceBefore=5,
        spaceAfter=5,
        leftIndent=20,
        backColor=colors.lightgrey
    ))
    styles.add(ParagraphStyle(
        name='DocQuote',
        parent=styles['Normal'],
        fontSize=10,
        leftIndent=30,
        rightIndent=30,
        fontName='Helvetica-Oblique',
        spaceAfter=10,
        backColor=colors.Color(1, 0.95, 0.8)  # Light yellow for emphasis
    ))
    styles.add(ParagraphStyle(
        name='DocWarning',
        parent=styles['Normal'],
        fontSize=11,
        leftIndent=20,
        rightIndent=20,
        fontName='Helvetica-Bold',
        spaceAfter=10,
        backColor=colors.Color(1, 0.9, 0.7),  # Orange-ish for warnings
        borderColor=colors.orange,
        borderWidth=2,
        borderPadding=5
    ))
    styles.add(ParagraphStyle(
        name='DocCriticalHeader',
        parent=styles['Heading2'],
        fontSize=16,
        spaceBefore=20,
        spaceAfter=15,
        fontName='Helvetica-Bold',
        textColor=colors.red,
        backColor=colors.Color(1, 0.95, 0.8),
        borderColor=colors.red,
        borderWidth=3,
        borderPadding=10
    ))
    styles.add(ParagraphStyle(
        name='DocCriticalBody',
        parent=styles['Normal'],
        fontSize=11,
        spaceAfter=8,
        leftIndent=15,
        rightIndent=15,
        backColor=colors.Color(1, 0.97, 0.9),
    ))

    # Build story
    story = []

    # Track current h3 section for image insertion
    current_h3 = None
    images_embedded = 0
    paragraphs_since_h3 = 0
    in_critical_section = False

    for elem_type, content in elements:
        if elem_type == 'h1':
            story.append(Paragraph(convert_inline(content), styles['DocTitle']))
        elif elem_type == 'h2':
            # Check if this is the CRITICAL DATA LIMITATION section - use special styling
            if 'CRITICAL' in content.upper() and 'LIMITATION' in content.upper():
                in_critical_section = True
                story.append(Spacer(1, 20))
                story.append(Paragraph(convert_inline(content), styles['DocCriticalHeader']))
            else:
                in_critical_section = False
                story.append(Paragraph(convert_inline(content), styles['DocH2']))
            current_h3 = None  # Reset on new h2
        elif elem_type == 'h3':
            if in_critical_section:
                story.append(Paragraph(convert_inline(content), styles['DocH3']))
            else:
                story.append(Paragraph(convert_inline(content), styles['DocH3']))
            current_h3 = content
            paragraphs_since_h3 = 0
        elif elem_type == 'h4':
            story.append(Paragraph(convert_inline(content), styles['DocH4']))

        elif elem_type == 'p':
            # Use special styling for ALL content in the critical limitation section
            if in_critical_section:
                story.append(Paragraph(convert_inline(content), styles['DocCriticalBody']))
            else:
                story.append(Paragraph(convert_inline(content), styles['DocBody']))
            paragraphs_since_h3 += 1

            # Insert images after a few paragraphs in specific sections
            if current_h3 and paragraphs_since_h3 == 2:
                for section_key, img_file in SECTION_IMAGES.items():
                    if section_key in current_h3:
                        img_path = base_dir / img_file
                        # per_model_breakdown is critical - make it large
                        is_large = 'per_model' in img_file or 'control_treatment' in img_file
                        if embed_image(story, img_path, large=is_large):
                            images_embedded += 1
                        current_h3 = None  # Prevent re-embedding
                        break

        elif elem_type == 'bullet':
            if in_critical_section:
                story.append(Paragraph(f"• {convert_inline(content)}", styles['DocCriticalBody']))
            else:
                story.append(Paragraph(f"• {convert_inline(content)}", styles['DocBullet']))
        elif elem_type == 'numbered':
            if in_critical_section:
                story.append(Paragraph(f"• {convert_inline(content)}", styles['DocCriticalBody']))
            else:
                story.append(Paragraph(f"• {convert_inline(content)}", styles['DocNumbered']))
        elif elem_type == 'quote':
            # Quotes in critical section get warning style
            if in_critical_section or '42' in content or '31' in content:
                story.append(Paragraph(convert_inline(content), styles['DocWarning']))
            else:
                story.append(Paragraph(convert_inline(content), styles['DocQuote']))
        elif elem_type == 'code':
            for line in content.split('\n'):
                story.append(Paragraph(line or ' ', styles['DocCode']))
        elif elem_type == 'table':
            # Create table
            table_data = []
            for row in content:
                table_data.append([Paragraph(convert_inline(cell), styles['DocBody']) for cell in row])

            if table_data:
                table = Table(table_data)
                table.setStyle(TableStyle([
                    ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
                    ('TEXTCOLOR', (0, 0), (-1, 0), colors.black),
                    ('ALIGN', (0, 0), (-1, -1), 'LEFT'),
                    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                    ('FONTSIZE', (0, 0), (-1, -1), 9),
                    ('BOTTOMPADDING', (0, 0), (-1, 0), 8),
                    ('BACKGROUND', (0, 1), (-1, -1), colors.white),
                    ('GRID', (0, 0), (-1, -1), 0.5, colors.grey),
                    ('VALIGN', (0, 0), (-1, -1), 'TOP'),
                ]))
                story.append(table)
                story.append(Spacer(1, 10))

    # Build PDF
    doc.build(story)
    print(f"\nCreated: {output_pdf}")
    print(f"Total images embedded: {images_embedded}")


def main():
    script_dir = Path(__file__).parent
    input_file = script_dir / '15_oobleck_effect_explained.md'
    output_file = script_dir / '15_Oobleck_Effect_Summary.pdf'

    if not input_file.exists():
        print(f"Error: {input_file} not found")
        return

    print(f"Generating PDF from: {input_file.name}")
    print(f"Output: {output_file.name}")
    print()

    create_pdf(input_file, output_file)


if __name__ == '__main__':
    main()
