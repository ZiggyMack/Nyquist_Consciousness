"""
Markdown to PDF converter using reportlab with IMAGE SUPPORT.
Converts 10_pfi_cosine_explained.md to 10_PFI_Dimensional_Summary.pdf

Features:
- Headers (h1-h4)
- Bold, italic, inline code
- Tables
- Code blocks
- Blockquotes
- **IMAGES** - embeds PNGs from subdirectories
"""

import re
from pathlib import Path
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_LEFT, TA_CENTER
from reportlab.lib.units import inch
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak, Image
from reportlab.lib import colors

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

def get_image_for_section(section_name: str, base_dir: Path) -> Path | None:
    """Map markdown section headers to image files."""
    # Map h4 headers (image names) to their file paths
    image_map = {
        # Phase 2 PCA images
        "variance_curve.png": base_dir / "phase2_pca" / "variance_curve.png",
        "pc_scatter.png": base_dir / "phase2_pca" / "pc_scatter.png",
        "provider_clusters.png": base_dir / "phase2_pca" / "provider_clusters.png",
        "event_horizon_contour.png": base_dir / "phase2_pca" / "event_horizon_contour.png",
        # Phase 3A synthetic images
        "eh_crossings.png": base_dir / "phase3a_synthetic" / "eh_crossings.png",
        "perturbation_comparison.png": base_dir / "phase3a_synthetic" / "perturbation_comparison.png",
        "ship_comparison.png": base_dir / "phase3a_synthetic" / "ship_comparison.png",
        # Phase 3B cross-model images
        "cross_model_comparison.png": base_dir / "phase3b_crossmodel" / "cross_model_comparison.png",
        "cross_model_histogram.png": base_dir / "phase3b_crossmodel" / "cross_model_histogram.png",
        "provider_matrix.png": base_dir / "phase3b_crossmodel" / "provider_matrix.png",
    }

    # Check if section_name matches any image
    for img_name, img_path in image_map.items():
        if img_name in section_name:
            if img_path.exists():
                return img_path
    return None


def create_pdf(input_md, output_pdf):
    """Convert markdown file to PDF with embedded images."""
    # Read markdown
    with open(input_md, 'r', encoding='utf-8') as f:
        md_text = f.read()

    # Get base directory for images
    base_dir = Path(input_md).parent

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
        spaceAfter=10
    ))

    # Build story
    story = []

    # Track last h4 for image insertion
    last_h4_content = None
    images_embedded = 0

    for elem_type, content in elements:
        if elem_type == 'h1':
            story.append(Paragraph(convert_inline(content), styles['DocTitle']))
        elif elem_type == 'h2':
            story.append(Paragraph(convert_inline(content), styles['DocH2']))
        elif elem_type == 'h3':
            story.append(Paragraph(convert_inline(content), styles['DocH3']))
        elif elem_type == 'h4':
            story.append(Paragraph(convert_inline(content), styles['DocH4']))
            last_h4_content = content

        elif elem_type == 'p':
            story.append(Paragraph(convert_inline(content), styles['DocBody']))

            # Insert image after "Key insight:" paragraph if we have one pending
            if last_h4_content and "Key insight:" in content:
                img_path = get_image_for_section(last_h4_content, base_dir)
                if img_path:
                    story.append(Spacer(1, 10))
                    # Calculate image size to fit page width (max 6 inches)
                    try:
                        img = Image(str(img_path), width=5.5*inch, height=4*inch)
                        img.hAlign = 'CENTER'
                        story.append(img)
                        story.append(Spacer(1, 15))
                        images_embedded += 1
                        print(f"  [IMAGE] Embedded: {img_path.name}")
                    except Exception as e:
                        print(f"  [WARN] Could not embed {img_path.name}: {e}")
                last_h4_content = None  # Reset

        elif elem_type == 'quote':
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
    print(f"Created: {output_pdf}")
    print(f"  Total images embedded: {images_embedded}")

if __name__ == '__main__':
    script_dir = Path(__file__).parent
    input_file = script_dir / '10_pfi_cosine_explained.md'
    output_file = script_dir / '10_PFI_Dimensional_Summary.pdf'  # Matches sync convention

    if not input_file.exists():
        print(f"Error: {input_file} not found")
        exit(1)

    create_pdf(input_file, output_file)
