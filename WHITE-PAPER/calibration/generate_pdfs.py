"""
Generate PDFs from Markdown Papers
Nyquist Consciousness Publication Pipeline

Uses markdown2 + xhtml2pdf for pure-Python PDF generation.
Alternative to pandoc when not available.
"""

import os
import sys
from pathlib import Path

try:
    import markdown2
    from xhtml2pdf import pisa
except ImportError:
    print("ERROR: Required packages not installed.")
    print("Run: py -m pip install markdown2 xhtml2pdf")
    sys.exit(1)

# Paths
WHITE_PAPER_DIR = Path(__file__).parent.parent
SUBMISSIONS_DIR = WHITE_PAPER_DIR / "submissions"
OUTPUT_DIR = WHITE_PAPER_DIR / "reviewers" / "packages" / "pdf"

# CSS for academic paper styling
CSS_STYLE = """
<style>
    @page {
        size: letter;
        margin: 1in;
    }
    body {
        font-family: 'Times New Roman', Times, serif;
        font-size: 11pt;
        line-height: 1.5;
        color: #000;
    }
    h1 {
        font-size: 16pt;
        font-weight: bold;
        text-align: center;
        margin-top: 0;
        margin-bottom: 12pt;
    }
    h2 {
        font-size: 14pt;
        font-weight: bold;
        margin-top: 18pt;
        margin-bottom: 6pt;
    }
    h3 {
        font-size: 12pt;
        font-weight: bold;
        margin-top: 12pt;
        margin-bottom: 6pt;
    }
    p {
        text-align: justify;
        margin-bottom: 6pt;
    }
    table {
        border-collapse: collapse;
        width: 100%;
        margin: 12pt 0;
        font-size: 10pt;
    }
    th, td {
        border: 1px solid #000;
        padding: 4pt 8pt;
        text-align: left;
    }
    th {
        background-color: #f0f0f0;
        font-weight: bold;
    }
    code {
        font-family: 'Courier New', monospace;
        font-size: 9pt;
        background-color: #f5f5f5;
        padding: 1pt 3pt;
    }
    pre {
        font-family: 'Courier New', monospace;
        font-size: 9pt;
        background-color: #f5f5f5;
        padding: 8pt;
        border: 1px solid #ddd;
        overflow: hidden;
        white-space: pre-wrap;
    }
    blockquote {
        margin-left: 20pt;
        padding-left: 10pt;
        border-left: 3pt solid #ddd;
        font-style: italic;
    }
    img {
        max-width: 100%;
        height: auto;
    }
    .figure-caption {
        font-size: 10pt;
        font-style: italic;
        text-align: center;
        margin-top: 4pt;
    }
    hr {
        border: none;
        border-top: 1px solid #ccc;
        margin: 18pt 0;
    }
</style>
"""

# Papers to generate - ALL 8 PUBLICATION PATHS
PAPERS = [
    # Academic Track
    {
        "name": "Workshop Paper",
        "source": "workshop/Nyquist_workshop_paper_FINAL.md",
        "output": "Nyquist_Workshop_Paper.pdf"
    },
    {
        "name": "arXiv Paper",
        "source": "arxiv/NYQUIST_ARXIV_PAPER_FINAL.md",
        "output": "Nyquist_arXiv_Paper.pdf"
    },
    {
        "name": "Journal White Paper",
        "source": "journal/NYQUIST_WHITE_PAPER_FINAL.md",
        "output": "Nyquist_Journal_Paper.pdf"
    },
    # Dissemination Track
    {
        "name": "Popular Science",
        "source": "popular_science/LLM_Ancient_Philosophy_Meets_Modern_AI.md",
        "output": "Nyquist_Popular_Science.pdf"
    },
    {
        "name": "Education Quiz",
        "source": "education/LLM_Quiz.md",
        "output": "Nyquist_Education_Quiz.pdf"
    },
    {
        "name": "Policy Briefing",
        "source": "policy/LLM_Briefing.md",
        "output": "Nyquist_Policy_Briefing.pdf"
    },
    {
        "name": "Funding Proposal",
        "source": "funding/LLM_Project_Nyquist_Consciousness.md",
        "output": "Nyquist_Funding_Proposal.pdf"
    },
    {
        "name": "Media Press",
        "source": "media/LLM_Unlocking_AI_Identity.md",
        "output": "Nyquist_Media_Press.pdf"
    },
]


def convert_markdown_to_pdf(md_path: Path, pdf_path: Path) -> bool:
    """Convert a markdown file to PDF."""
    try:
        # Read markdown
        with open(md_path, 'r', encoding='utf-8') as f:
            md_content = f.read()

        # Convert to HTML with extras
        html_content = markdown2.markdown(
            md_content,
            extras=[
                'tables',
                'fenced-code-blocks',
                'code-friendly',
                'header-ids',
                'strike',
                'task_list',
                'footnotes'
            ]
        )

        # Wrap with HTML structure and CSS
        full_html = f"""
        <!DOCTYPE html>
        <html>
        <head>
            <meta charset="utf-8">
            {CSS_STYLE}
        </head>
        <body>
            {html_content}
        </body>
        </html>
        """

        # Create PDF
        pdf_path.parent.mkdir(parents=True, exist_ok=True)

        with open(pdf_path, 'wb') as pdf_file:
            pisa_status = pisa.CreatePDF(full_html, dest=pdf_file)

        return not pisa_status.err

    except Exception as e:
        print(f"  ERROR: {e}")
        return False


def main():
    """Generate all PDFs."""
    print("=" * 60)
    print("GENERATING PUBLICATION PDFs")
    print("=" * 60)
    print(f"Source: {SUBMISSIONS_DIR}")
    print(f"Output: {OUTPUT_DIR}")
    print()

    # Ensure output directory exists
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    results = []
    for paper in PAPERS:
        source_path = SUBMISSIONS_DIR / paper["source"]
        output_path = OUTPUT_DIR / paper["output"]

        print(f"Generating: {paper['name']}")
        print(f"  Source: {source_path.name}")
        print(f"  Output: {output_path.name}")

        if not source_path.exists():
            print(f"  ERROR: Source file not found!")
            results.append((paper['name'], False))
            continue

        success = convert_markdown_to_pdf(source_path, output_path)

        if success:
            size_kb = output_path.stat().st_size / 1024
            print(f"  SUCCESS: {size_kb:.1f} KB")
        else:
            print(f"  FAILED")

        results.append((paper['name'], success))
        print()

    # Summary
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    success_count = sum(1 for _, s in results if s)
    print(f"Generated: {success_count}/{len(results)} PDFs")

    if success_count < len(results):
        print("\nFailed:")
        for name, success in results:
            if not success:
                print(f"  - {name}")

    print(f"\nOutput directory: {OUTPUT_DIR}")
    print()

    # List generated files
    print("Generated files:")
    for f in OUTPUT_DIR.glob("*.pdf"):
        size_kb = f.stat().st_size / 1024
        print(f"  {f.name} ({size_kb:.1f} KB)")

    return 0 if success_count == len(results) else 1


if __name__ == '__main__':
    sys.exit(main())
