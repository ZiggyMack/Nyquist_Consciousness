#!/usr/bin/env python3
"""
Generate PDF versions of submission papers from markdown.
Uses reportlab for consistent styling with visualization PDFs.
"""

from pathlib import Path
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
from reportlab.lib.colors import HexColor, black, grey
import re

# Paths
SUBMISSIONS_DIR = Path(__file__).parent
ARXIV_MD = SUBMISSIONS_DIR / "arxiv" / "NYQUIST_ARXIV_PAPER_FINAL.md"
WORKSHOP_MD = SUBMISSIONS_DIR / "workshop" / "Nyquist_workshop_paper_FINAL.md"
JOURNAL_MD = SUBMISSIONS_DIR / "journal" / "JOURNAL_PAPER_FINAL.md"
FUNDING_MD = SUBMISSIONS_DIR / "funding" / "FUNDING_FINAL.md"
POLICY_MD = SUBMISSIONS_DIR / "policy" / "POLICY_FINAL.md"
MEDIA_MD = SUBMISSIONS_DIR / "media" / "MEDIA_FINAL.md"
EDUCATION_MD = SUBMISSIONS_DIR / "education" / "EDUCATION_FINAL.md"
POPULAR_SCIENCE_MD = SUBMISSIONS_DIR / "popular_science" / "POPULAR_SCIENCE_FINAL.md"

# Styles
styles = getSampleStyleSheet()

title_style = ParagraphStyle(
    'PaperTitle',
    parent=styles['Heading1'],
    fontSize=16,
    spaceAfter=12,
    alignment=TA_CENTER,
    textColor=HexColor('#1a1a2e')
)

author_style = ParagraphStyle(
    'Authors',
    parent=styles['Normal'],
    fontSize=11,
    spaceAfter=6,
    alignment=TA_CENTER,
    textColor=HexColor('#333333')
)

affiliation_style = ParagraphStyle(
    'Affiliations',
    parent=styles['Normal'],
    fontSize=9,
    spaceAfter=4,
    alignment=TA_CENTER,
    textColor=HexColor('#666666')
)

abstract_label_style = ParagraphStyle(
    'AbstractLabel',
    parent=styles['Heading2'],
    fontSize=11,
    spaceBefore=15,
    spaceAfter=6,
    textColor=HexColor('#16213e'),
    fontName='Helvetica-Bold'
)

abstract_style = ParagraphStyle(
    'Abstract',
    parent=styles['Normal'],
    fontSize=9,
    spaceAfter=12,
    alignment=TA_JUSTIFY,
    leading=12,
    leftIndent=20,
    rightIndent=20,
    textColor=HexColor('#333333')
)

section_style = ParagraphStyle(
    'Section',
    parent=styles['Heading1'],
    fontSize=13,
    spaceBefore=18,
    spaceAfter=8,
    textColor=HexColor('#16213e')
)

subsection_style = ParagraphStyle(
    'Subsection',
    parent=styles['Heading2'],
    fontSize=11,
    spaceBefore=12,
    spaceAfter=6,
    textColor=HexColor('#16213e')
)

body_style = ParagraphStyle(
    'Body',
    parent=styles['Normal'],
    fontSize=10,
    spaceAfter=6,
    alignment=TA_JUSTIFY,
    leading=13
)

code_style = ParagraphStyle(
    'Code',
    parent=styles['Normal'],
    fontSize=8,
    fontName='Courier',
    spaceAfter=8,
    leftIndent=20,
    backColor=HexColor('#f5f5f5')
)

quote_style = ParagraphStyle(
    'Quote',
    parent=styles['Normal'],
    fontSize=9,
    fontName='Helvetica-Oblique',
    spaceAfter=10,
    leftIndent=30,
    rightIndent=30,
    alignment=TA_CENTER,
    textColor=HexColor('#555555')
)

def clean_unicode(text):
    """Replace Unicode characters that cause black squares in reportlab."""
    # Order matters! Replace compound characters FIRST, then single characters
    unicode_replacements = [
        # Compound characters first (order matters!)
        ('10⁻²³', '10^(-23)'),
        ('2.40×10⁻²³', '2.40x10^(-23)'),
        ('4.8×10⁻⁵', '4.8x10^(-5)'),
        ('×10⁻²³', 'x10^(-23)'),
        ('×10⁻⁵', 'x10^(-5)'),
        ('⁻²³', '^(-23)'),
        ('⁻⁵', '^(-5)'),
        ('σ²', 'sigma^2'),
        ('τₛ', 'tau_s'),
        ('ω₀', 'omega_0'),
        ('χ²', 'chi^2'),
        # Subscripts
        ('₀', '_0'),
        ('₁', '_1'),
        ('₂', '_2'),
        ('₃', '_3'),
        ('₄', '_4'),
        ('₅', '_5'),
        ('ₛ', '_s'),
        # Superscripts
        ('⁻', '-'),
        ('⁰', '^0'),
        ('¹', '^1'),
        ('²', '^2'),
        ('³', '^3'),
        ('⁴', '^4'),
        ('⁵', '^5'),
        ('⁶', '^6'),
        ('⁷', '^7'),
        ('⁸', '^8'),
        ('⁹', '^9'),
        # Greek letters
        ('α', 'alpha'),
        ('β', 'beta'),
        ('γ', 'gamma'),
        ('δ', 'delta'),
        ('ε', 'epsilon'),
        ('ζ', 'zeta'),
        ('η', 'eta'),
        ('θ', 'theta'),
        ('ι', 'iota'),
        ('κ', 'kappa'),
        ('λ', 'lambda'),
        ('μ', 'mu'),
        ('ν', 'nu'),
        ('ξ', 'xi'),
        ('π', 'pi'),
        ('ρ', 'rho'),
        ('σ', 'sigma'),
        ('τ', 'tau'),
        ('υ', 'upsilon'),
        ('φ', 'phi'),
        ('χ', 'chi'),
        ('ψ', 'psi'),
        ('ω', 'omega'),
        ('Δ', 'Delta'),
        ('Σ', 'Sigma'),
        ('Ω', 'Omega'),
        # Math symbols
        ('×', 'x'),
        ('÷', '/'),
        ('±', '+/-'),
        ('≈', '~'),
        ('≠', '!='),
        ('≥', '>='),
        ('≤', '<='),
        ('∞', 'inf'),
        ('√', 'sqrt'),
        ('∑', 'SUM'),
        ('∏', 'PROD'),
        ('∈', 'in'),
        ('∉', 'not in'),
        ('⊂', 'subset'),
        ('⊃', 'superset'),
        ('∩', 'AND'),
        ('∪', 'OR'),
        ('⊥', '_|_'),
        # Arrows
        ('→', '->'),
        ('←', '<-'),
        ('↔', '<->'),
        ('⇒', '=>'),
        ('⇐', '<='),
        ('⇔', '<=>'),
        # Emojis and special
        ('🚢', '[ship]'),
        ('🌀', '[vortex]'),
        ('✓', '[check]'),
        ('✅', '[check]'),
        ('✗', '[x]'),
        ('★', '*'),
        ('•', '-'),
        ('·', '.'),
        ('—', '--'),
        ('–', '-'),
        ('"', '"'),
        ('"', '"'),
        (''', "'"),
        (''', "'"),
        ('…', '...'),
        # Section and special symbols
        ('§', 'S'),
        ('ⁿ', '^n'),
        ('ℝ', 'R'),
        ('∇', 'nabla'),
        ('⋂', 'INTERSECT'),
        # Circle emojis
        ('⚪', '[o]'),
        ('🟡', '[o]'),
        ('🟢', '[o]'),
        ('🔴', '[o]'),
        ('🔵', '[o]'),
        ('🔮', '[crystal]'),
        ('🧊', '[ice]'),
        # Box drawing (replace with ASCII)
        ('─', '-'),
        ('│', '|'),
        ('└', '+'),
        ('├', '+'),
        ('┐', '+'),
        ('┘', '+'),
        ('┌', '+'),
        ('┬', '+'),
        ('┴', '+'),
        ('┼', '+'),
        ('┤', '+'),
        # Additional symbols
        ('©', '(c)'),
        ('°', ' deg'),
    ]
    for unicode_char, replacement in unicode_replacements:
        text = text.replace(unicode_char, replacement)
    return text


def clean_markdown(text):
    """Convert markdown formatting to reportlab-compatible HTML."""
    # First, replace Unicode characters that cause black squares
    text = clean_unicode(text)

    # Bold: **text** -> <b>text</b>
    text = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', text)
    # Italic: *text* -> <i>text</i>
    text = re.sub(r'\*([^*]+)\*', r'<i>\1</i>', text)
    # Code: `text` -> <font name="Courier">text</font>
    text = re.sub(r'`([^`]+)`', r'<font name="Courier">\1</font>', text)
    # Links: [text](url) -> text
    text = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', text)
    # Escape special chars for XML
    text = text.replace('&', '&amp;').replace('<b>', '<<b>>').replace('</b>', '<</b>>').replace('<i>', '<<i>>').replace('</i>', '<</i>>').replace('<font', '<<font').replace('</font>', '<</font>>')
    text = text.replace('<<', '<').replace('>>', '>')
    return text

def parse_table(lines):
    """Parse a markdown table into data rows."""
    data = []
    for line in lines:
        if line.strip().startswith('|') and '---' not in line:
            cells = [cell.strip() for cell in line.split('|')[1:-1]]
            if cells:
                data.append(cells)
    return data

def markdown_to_story(md_path):
    """Convert markdown file to reportlab story elements."""
    story = []

    with open(md_path, 'r', encoding='utf-8') as f:
        content = f.read()

    lines = content.split('\n')
    i = 0
    in_code_block = False
    code_lines = []
    in_table = False
    table_lines = []

    while i < len(lines):
        line = lines[i]

        # Code blocks
        if line.strip().startswith('```'):
            if in_code_block:
                # End code block
                code_text = '\n'.join(code_lines)
                story.append(Paragraph(code_text.replace('\n', '<br/>'), code_style))
                code_lines = []
                in_code_block = False
            else:
                in_code_block = True
            i += 1
            continue

        if in_code_block:
            code_lines.append(clean_unicode(line))
            i += 1
            continue

        # Tables
        if line.strip().startswith('|'):
            if not in_table:
                in_table = True
                table_lines = []
            table_lines.append(line)
            i += 1
            continue
        elif in_table:
            # End of table
            data = parse_table(table_lines)
            if data:
                # Clean markdown from cells
                cleaned_data = [[clean_markdown(cell) for cell in row] for row in data]
                # Create table with style
                t = Table(cleaned_data, repeatRows=1)
                t.setStyle(TableStyle([
                    ('BACKGROUND', (0, 0), (-1, 0), HexColor('#e8e8e8')),
                    ('TEXTCOLOR', (0, 0), (-1, 0), HexColor('#16213e')),
                    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                    ('FONTSIZE', (0, 0), (-1, -1), 8),
                    ('ALIGN', (0, 0), (-1, -1), 'LEFT'),
                    ('GRID', (0, 0), (-1, -1), 0.5, grey),
                    ('VALIGN', (0, 0), (-1, -1), 'TOP'),
                    ('LEFTPADDING', (0, 0), (-1, -1), 4),
                    ('RIGHTPADDING', (0, 0), (-1, -1), 4),
                    ('TOPPADDING', (0, 0), (-1, -1), 3),
                    ('BOTTOMPADDING', (0, 0), (-1, -1), 3),
                ]))
                story.append(Spacer(1, 0.1*inch))
                story.append(t)
                story.append(Spacer(1, 0.1*inch))
            in_table = False
            table_lines = []
            # Don't increment, process current line
            continue

        # Skip empty lines
        if not line.strip():
            i += 1
            continue

        # Skip horizontal rules
        if line.strip() == '---':
            story.append(Spacer(1, 0.1*inch))
            i += 1
            continue

        # Title (# heading)
        if line.startswith('# ') and not line.startswith('## '):
            title = line[2:].strip()
            story.append(Paragraph(clean_markdown(title), title_style))
            story.append(Spacer(1, 0.1*inch))
            i += 1
            continue

        # Authors line
        if line.startswith('**Authors**:'):
            authors = line.replace('**Authors**:', '').strip()
            story.append(Paragraph(clean_markdown(authors), author_style))
            i += 1
            continue

        # Affiliations (superscript lines)
        if line.startswith('¹') or line.startswith('²') or line.startswith('³'):
            story.append(Paragraph(clean_unicode(line.strip()), affiliation_style))
            i += 1
            continue

        # Repository/Categories
        if line.startswith('**Repository:**') or line.startswith('**arXiv'):
            story.append(Paragraph(clean_markdown(line), affiliation_style))
            i += 1
            continue

        # Workshop designation
        if line.startswith('**Workshop Paper'):
            story.append(Paragraph(clean_markdown(line), affiliation_style))
            story.append(Spacer(1, 0.15*inch))
            i += 1
            continue

        # Abstract
        if line.startswith('**Abstract**:'):
            story.append(Spacer(1, 0.15*inch))
            story.append(Paragraph("Abstract", abstract_label_style))
            abstract_text = line.replace('**Abstract**:', '').strip()
            story.append(Paragraph(clean_markdown(abstract_text), abstract_style))
            i += 1
            continue

        # Keywords
        if line.startswith('**Keywords**:'):
            story.append(Paragraph(clean_markdown(line), affiliation_style))
            story.append(Spacer(1, 0.2*inch))
            i += 1
            continue

        # Sections (## heading)
        if line.startswith('## '):
            section = line[3:].strip()
            story.append(Paragraph(clean_markdown(section), section_style))
            i += 1
            continue

        # Subsections (### heading)
        if line.startswith('### '):
            subsection = line[4:].strip()
            story.append(Paragraph(clean_markdown(subsection), subsection_style))
            i += 1
            continue

        # Block quotes (>)
        if line.startswith('>'):
            quote = line[1:].strip()
            story.append(Paragraph(clean_markdown(quote), quote_style))
            i += 1
            continue

        # Figure references (skip image markdown, just show caption)
        if line.startswith('!['):
            i += 1
            continue

        # Figure captions (*Figure X:...)
        if line.startswith('*Figure') or line.startswith('*Table'):
            caption = line.strip('*').strip()
            story.append(Paragraph(f"<i>{clean_markdown(caption)}</i>", affiliation_style))
            i += 1
            continue

        # Comments (<!-- -->)
        if line.strip().startswith('<!--'):
            i += 1
            continue

        # List items
        if line.strip().startswith('- '):
            item = line.strip()[2:]
            story.append(Paragraph(f"• {clean_markdown(item)}", body_style))
            i += 1
            continue

        # Numbered list items
        if re.match(r'^\d+\.', line.strip()):
            story.append(Paragraph(clean_markdown(line.strip()), body_style))
            i += 1
            continue

        # Regular paragraph
        story.append(Paragraph(clean_markdown(line), body_style))
        i += 1

    return story


def generate_arxiv_pdf():
    """Generate the arXiv paper PDF."""
    output_path = SUBMISSIONS_DIR / "arxiv" / "NYQUIST_ARXIV_PAPER_FINAL.pdf"
    doc = SimpleDocTemplate(
        str(output_path),
        pagesize=letter,
        leftMargin=0.75*inch,
        rightMargin=0.75*inch,
        topMargin=0.75*inch,
        bottomMargin=0.75*inch
    )

    story = markdown_to_story(ARXIV_MD)
    doc.build(story)
    print(f"Generated: {output_path}")
    return output_path


def generate_workshop_pdf():
    """Generate the workshop paper PDF."""
    output_path = SUBMISSIONS_DIR / "workshop" / "Nyquist_workshop_paper_FINAL.pdf"
    doc = SimpleDocTemplate(
        str(output_path),
        pagesize=letter,
        leftMargin=0.75*inch,
        rightMargin=0.75*inch,
        topMargin=0.75*inch,
        bottomMargin=0.75*inch
    )

    story = markdown_to_story(WORKSHOP_MD)
    doc.build(story)
    print(f"Generated: {output_path}")
    return output_path


def generate_pdf(md_path, output_name=None):
    """Generate a PDF from any markdown file."""
    if not md_path.exists():
        print(f"Skipping (not found): {md_path}")
        return None

    if output_name is None:
        output_name = md_path.stem + ".pdf"

    output_path = md_path.parent / output_name
    doc = SimpleDocTemplate(
        str(output_path),
        pagesize=letter,
        leftMargin=0.75*inch,
        rightMargin=0.75*inch,
        topMargin=0.75*inch,
        bottomMargin=0.75*inch
    )

    story = markdown_to_story(md_path)
    doc.build(story)
    print(f"Generated: {output_path}")
    return output_path


if __name__ == "__main__":
    print("Generating submission PDFs...")
    print()

    # Academic papers (priority)
    generate_pdf(ARXIV_MD, "NYQUIST_ARXIV_PAPER_FINAL.pdf")
    generate_pdf(WORKSHOP_MD, "Nyquist_workshop_paper_FINAL.pdf")
    generate_pdf(JOURNAL_MD, "JOURNAL_PAPER_FINAL.pdf")

    # Secondary packages
    generate_pdf(FUNDING_MD, "FUNDING_FINAL.pdf")
    generate_pdf(POLICY_MD, "POLICY_FINAL.pdf")
    generate_pdf(MEDIA_MD, "MEDIA_FINAL.pdf")
    generate_pdf(EDUCATION_MD, "EDUCATION_FINAL.pdf")
    generate_pdf(POPULAR_SCIENCE_MD, "POPULAR_SCIENCE_FINAL.pdf")

    print()
    print("Done!")
