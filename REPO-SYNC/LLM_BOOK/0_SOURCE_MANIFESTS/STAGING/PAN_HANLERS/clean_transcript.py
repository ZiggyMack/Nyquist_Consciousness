#!/usr/bin/env python3
"""Clean a raw ASR recording transcript for NotebookLM.

The circle's recording transcripts prefix every line with a garbled ASR
timestamp: <m:ss><verbose duration><text> jammed together with no spaces
(e.g. "14:0014 minutesare people..."). This normalizes each line to
"[m:ss] text" and prepends a self-contained header. Spoken text is otherwise
verbatim. No extraction protocol is applied - the output is a RAW primary
source for a later round, not a dig.

Usage:  py clean_transcript.py [raw.md] [out.md]
"""
import re
import sys
from pathlib import Path

RAW = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("_IN2/transcript.md")
OUT = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("_IN2/transcript_ziggy_tale_recursion.md")

HEADER = """# Transcript - Ziggy & Tale Recursion (recorded session)

> **Cleaned recording transcript - staged for a later PAN_HANLERS round (`_IN2/`).**
> A live recorded philosophical conversation between Ziggy and Tale Recursion
> (a Pan Handler). Raw source: `_IN2/transcript.md` (ASR). Treatment: the
> garbled ASR timestamp prefixes were normalized to `[m:ss]`; spoken text is
> otherwise verbatim. This is a RAW primary source - unmined, no extraction
> protocol applied, not promoted evidence about any person. Content boundary:
> ideas discussed, not claims about persons.
>
> Topics: self-one / self-two (executive vs. subprocess), agents and AI, the
> CEO / executive-skill metaphor, the space of possibility.

---

"""


def clean_line(line):
    m = re.match(r'^(\d+:\d\d)(.*)$', line)
    if not m:
        return line
    ts, rest = m.group(1), m.group(2)
    rest = re.sub(r'^(\d+ minutes?(?:, \d+ seconds?)?|\d+ seconds?)\s*', '', rest)
    return ("[%s] %s" % (ts, rest)).rstrip()


def main():
    raw = RAW.read_text(encoding="utf-8", errors="replace").splitlines()
    cleaned = [clean_line(l) for l in raw]
    OUT.write_text(HEADER + "\n".join(cleaned) + "\n", encoding="utf-8")
    print("raw lines : %d" % len(raw))
    print("out file  : %s" % OUT)
    print("sample:")
    for l in cleaned[:4]:
        print("  " + l[:82].encode("ascii", "ignore").decode())


if __name__ == "__main__":
    main()
