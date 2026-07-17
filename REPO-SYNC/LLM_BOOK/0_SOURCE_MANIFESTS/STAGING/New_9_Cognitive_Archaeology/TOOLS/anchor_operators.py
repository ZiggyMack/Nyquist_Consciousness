#!/usr/bin/env python3
"""
anchor_operators.py — Position anchoring for Test B (Cognitive Archaeology)

PROBLEM
-------
Test B (operator sequence statistics) currently consumes operator LISTING order.
The STANDARD extraction prompt asks for "a catalog" — it never requests deployment
order. Listing order is therefore salience/taxonomy order, and is plausibly
contaminated by the 14-item example list embedded in the prompt itself
(anchoring bias: operators resembling earlier examples get listed earlier).

FIX
---
Every operator entry carries 2-3 verbatim quotes. Quotes have positions in the
source text. Anchor each operator to the position of its FIRST quoted evidence
and derive deployment order from the SOURCE, not from the extraction.

USAGE
-----
  # Stage 1 only (no source needed): parse extractions, report coverage
  python3 anchor_operators.py parse --extractions DIR

  # Full anchoring (requires source texts)
  python3 anchor_operators.py anchor --extractions DIR --sources DIR --out results.json

  # Instrument checks on anchored results
  python3 anchor_operators.py check --results results.json

OUTPUTS (per extraction file)
-----------------------------
  operators: [{name, listing_rank, quotes, anchored_pos, anchored_rank, anchor_score}]
  listing_vs_anchored_spearman: does listing order track deployment order at all?
  anchor_coverage: fraction of quotes locatable in source (KILL CONDITION: <0.70
                   means quotes are paraphrase, tool fails, prompt redesign needed)

HOUSE RULES HONORED
-------------------
  * All Measured, All Floored: run identically on neg_G/neg_H to produce the
    null ordering distribution before any dig-site claim.
  * The tool reports its own failure condition (anchor_coverage) alongside
    every result. A mis-specified control does not fail silently.
"""

import argparse, json, os, re, sys, unicodedata
from difflib import SequenceMatcher
from itertools import combinations

# ----------------------------------------------------------------------------
# Stage 1: parse extraction files -> [(operator_name, [quotes], listing_rank)]
# Handles the observed format zoo: Claude '### N. Name', Grok '**Name**',
# numbered '1. **Name**', 'Operation N:' etc.
# ----------------------------------------------------------------------------

HEADER_PATTERNS = [
    re.compile(r'^#{2,4}\s*(?:\d+[\.\)]\s*)?(.+?)\s*$'),          # ### 1. Name / ## Name
    re.compile(r'^\*\*(?:\d+[\.\)]\s*)?([^*]+?)\*\*\s*:?\s*$'),   # **Name** on its own line
    re.compile(r'^(?:\d+)[\.\)]\s+\*\*([^*]+?)\*\*'),             # 1. **Name** ...
    re.compile(r'^(?:\d+)[\.\)]\s+([A-Z][^:.]{4,60})\s*$'),       # 1. Name
    re.compile(r'^Operation\s+\d+\s*[:\-]\s*(.+)$', re.I),
]

# Lines that look like headers but are section furniture, refusal menus, or meta.
FURNITURE = re.compile(
    r'^(catalog|summary|conclusion|overview|introduction|notes?|caveats?|'
    r'source|method|failure modes?|examples?|definition|reasoning operators?|'
    r'operators? (identified|catalog)|what (goes wrong|is absent)|'
    r'no (reasoning|operators?)|analysis|assessment|observations?)\b', re.I)

QUOTE_RE = re.compile(r'[\"\u201c]([^\"\u201c\u201d]{25,400})[\"\u201d]')

def normalize(s: str) -> str:
    s = unicodedata.normalize('NFKD', s)
    s = re.sub(r'[_\-.]', ' ', s)
    s = re.sub(r'\s+', ' ', s).strip().lower()
    s = re.sub(r'[^a-z0-9 ]', '', s)
    return s

def parse_extraction(path: str):
    """Return list of {name, listing_rank, quotes[]} in file order."""
    with open(path, encoding='utf-8', errors='replace') as f:
        lines = f.read().splitlines()
    ops, current = [], None
    for ln in lines:
        stripped = ln.strip()
        name = None
        for pat in HEADER_PATTERNS:
            m = pat.match(stripped)
            if m:
                cand = m.group(1).strip().rstrip(':').strip()
                # plausible operator names: short verb-ish phrases, not furniture
                if 3 <= len(cand) <= 90 and not FURNITURE.match(cand):
                    name = cand
                break
        if name:
            current = {'name': name, 'listing_rank': len(ops) + 1, 'quotes': []}
            ops.append(current)
        elif current is not None:
            for q in QUOTE_RE.findall(ln):
                current['quotes'].append(q.strip())
    # drop trailing header-only artifacts with no content at all? keep — quotes
    # may legitimately be absent; coverage stats will surface it.
    return ops

# ----------------------------------------------------------------------------
# Stage 2: fuzzy-anchor quotes in source text
# LLM "quotes" are often lightly paraphrased; exact find() is insufficient.
# Strategy: exact match -> normalized match -> sliding-window SequenceMatcher.
# ----------------------------------------------------------------------------

def anchor_quote(quote: str, source: str, norm_source: str, threshold: float = 0.72):
    """Return (position_fraction, score) or (None, best_score)."""
    # 1. exact
    i = source.find(quote)
    if i >= 0:
        return i / max(len(source), 1), 1.0
    # 2. normalized exact
    nq = normalize(quote)
    j = norm_source.find(nq)
    if j >= 0 and nq:
        return j / max(len(norm_source), 1), 0.95
    # 3. sliding window fuzzy (windows of quote length, stride = len/4)
    if not nq:
        return None, 0.0
    L = len(nq)
    best, best_pos = 0.0, None
    stride = max(L // 4, 20)
    for start in range(0, max(len(norm_source) - L, 1), stride):
        window = norm_source[start:start + L + 40]
        r = SequenceMatcher(None, nq, window).ratio()
        if r > best:
            best, best_pos = r, start
            if r > 0.92:
                break
    if best >= threshold and best_pos is not None:
        return best_pos / max(len(norm_source), 1), round(best, 3)
    return None, round(best, 3)

def anchor_file(ops, source_text):
    norm_source = normalize(source_text)
    n_quotes = n_anchored = 0
    for op in ops:
        positions = []
        for q in op['quotes']:
            n_quotes += 1
            pos, score = anchor_quote(q, source_text, norm_source)
            if pos is not None:
                n_anchored += 1
                positions.append((pos, score))
        if positions:
            first = min(positions, key=lambda t: t[0])
            op['anchored_pos'] = round(first[0], 4)
            op['anchor_score'] = first[1]
        else:
            op['anchored_pos'] = None
            op['anchor_score'] = None
    anchored_ops = [o for o in ops if o['anchored_pos'] is not None]
    anchored_ops.sort(key=lambda o: o['anchored_pos'])
    for rank, o in enumerate(anchored_ops, 1):
        o['anchored_rank'] = rank
    coverage = (n_anchored / n_quotes) if n_quotes else 0.0
    return ops, round(coverage, 3), n_quotes, n_anchored

# ----------------------------------------------------------------------------
# Stats
# ----------------------------------------------------------------------------

def spearman(xs, ys):
    n = len(xs)
    if n < 3:
        return None
    def ranks(v):
        order = sorted(range(n), key=lambda i: v[i])
        r = [0] * n
        for rank, i in enumerate(order):
            r[i] = rank + 1
        return r
    rx, ry = ranks(xs), ranks(ys)
    d2 = sum((a - b) ** 2 for a, b in zip(rx, ry))
    return round(1 - 6 * d2 / (n * (n * n - 1)), 3)

# ----------------------------------------------------------------------------
# Commands
# ----------------------------------------------------------------------------

def cmd_parse(args):
    files = sorted(f for f in os.listdir(args.extractions)
                   if f.startswith('extraction_') and f.endswith('.md')
                   and 'summary' not in f)
    report, tot_ops, tot_q = [], 0, 0
    for fn in files:
        ops = parse_extraction(os.path.join(args.extractions, fn))
        nq = sum(len(o['quotes']) for o in ops)
        tot_ops += len(ops); tot_q += nq
        report.append({'file': fn, 'n_operators': len(ops), 'n_quotes': nq,
                       'ops_with_quotes': sum(1 for o in ops if o['quotes'])})
    usable = sum(1 for r in report if r['ops_with_quotes'] >= 2)
    print(json.dumps({'files': len(report), 'total_operators_parsed': tot_ops,
                      'total_quotes_parsed': tot_q,
                      'files_with_2plus_quoted_ops': usable,
                      'per_file': report}, indent=1))

def cmd_anchor(args):
    src_index = {}
    for fn in os.listdir(args.sources):
        key = normalize(os.path.splitext(fn)[0])
        with open(os.path.join(args.sources, fn), encoding='utf-8', errors='replace') as f:
            src_index[key] = f.read()
    results = []
    for fn in sorted(os.listdir(args.extractions)):
        if not (fn.startswith('extraction_') and fn.endswith('.md')): continue
        if 'summary' in fn: continue
        # match extraction to source by token overlap in filename
        toks = set(normalize(fn).split())
        best_key, best_ov = None, 0
        for key in src_index:
            ov = len(toks & set(key.split()))
            if ov > best_ov:
                best_key, best_ov = key, ov
        if best_key is None: continue
        ops = parse_extraction(os.path.join(args.extractions, fn))
        ops, cov, nq, na = anchor_file(ops, src_index[best_key])
        both = [o for o in ops if o.get('anchored_rank')]
        rho = spearman([o['listing_rank'] for o in both],
                       [o['anchored_rank'] for o in both]) if len(both) >= 3 else None
        results.append({'file': fn, 'source': best_key, 'anchor_coverage': cov,
                        'quotes': nq, 'anchored': na,
                        'listing_vs_anchored_spearman': rho,
                        'operators': ops})
    with open(args.out, 'w') as f:
        json.dump(results, f, indent=1)
    covs = [r['anchor_coverage'] for r in results if r['quotes']]
    rhos = [r['listing_vs_anchored_spearman'] for r in results
            if r['listing_vs_anchored_spearman'] is not None]
    print(json.dumps({
        'files_anchored': len(results),
        'mean_anchor_coverage': round(sum(covs)/len(covs), 3) if covs else None,
        'KILL_CONDITION_coverage_below_0.70': (sum(covs)/len(covs) < 0.70) if covs else None,
        'mean_listing_vs_anchored_rho': round(sum(rhos)/len(rhos), 3) if rhos else None,
        'note': 'per-file detail in ' + args.out}, indent=1))

def cmd_check(args):
    with open(args.results) as f:
        results = json.load(f)
    # Cross-extractor anchored-order agreement scaffold:
    # group files by source; within a source, operators still need semantic
    # matching (the blinded protocol). We emit name+anchored_pos pairs per
    # extractor so the existing blinded-matching pipeline can consume them.
    by_source = {}
    for r in results:
        by_source.setdefault(r['source'], []).append(r)
    out = {}
    for src, rs in by_source.items():
        out[src] = [{'file': r['file'],
                     'sequence': [{'name': o['name'], 'pos': o['anchored_pos']}
                                  for o in r['operators'] if o.get('anchored_pos') is not None]}
                    for r in rs]
    print(json.dumps(out, indent=1))

def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p1 = sub.add_parser('parse');  p1.add_argument('--extractions', required=True)
    p2 = sub.add_parser('anchor'); p2.add_argument('--extractions', required=True)
    p2.add_argument('--sources', required=True); p2.add_argument('--out', default='anchored.json')
    p3 = sub.add_parser('check');  p3.add_argument('--results', required=True)
    args = ap.parse_args()
    {'parse': cmd_parse, 'anchor': cmd_anchor, 'check': cmd_check}[args.cmd](args)

if __name__ == '__main__':
    main()
