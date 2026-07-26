#!/usr/bin/env python3
"""
De-protocol treatment for Pan Handlers dig workbooks.

Each raw dig workbook (DIG_*.md) is ~94-97% real extracted content wrapped in
a fixed ~293-line protocol shell (repeated STAGE N PROMPT fences + HUMAN
PREFLIGHT + header instructions). NotebookLM drowns in that boilerplate if the
files are uploaded raw. This strips the wrapper and keeps the substance:

  KEEP : the H1 title, the Status + Discovered-topic lines, every
         "STAGE N OUTPUT" section, and every "FIELD-DESK REVIEW" section.
  DROP : header instruction blockquote, Packet Header table, HUMAN PREFLIGHT,
         and every fenced "STAGE N PROMPT" block.

Pure text-processing. Reads the source archive read-only; writes cleaned
copies into the batch _IN/. No re-extraction, no API.

Usage:  py deprotocol_digs.py            # runs the 16-dig philosophical-core cut
        py deprotocol_digs.py --check    # dry-run: verify only, write nothing
"""
import re
import sys
from pathlib import Path

SRC = Path(r"D:\Documents\Pan_Handlers\circle\evidence\chat_extractions")
OUT = Path(__file__).resolve().parent / "_IN"

# Ziggy's 2026-07-21 philosophical-core cut (the reusable-ingredients digs).
# (code, source filename, short slug for the clean output name)
DIGS = [
    ("AUX_02", "DIG_AUX_02_invariance_and_stable_structure_2026-07.md",                                   "invariance_stable_structure"),
    ("AUX_03", "DIG_AUX_03_prediction_ontology_and_effective_theories_2026-07.md",                        "prediction_ontology"),
    ("DIG_01", "DIG_01_classical_theism_evil_and_moral_generativity.md",                                  "classical_theism_moral_generativity"),
    ("SW02",   "DIG_COMPOUND_SWEEP_02_maps_experience_values_and_plausibility.md",                        "maps_experience_plausibility"),
    ("SW03",   "DIG_COMPOUND_SWEEP_03_foundations_justification_and_jurisdiction.md",                     "foundations_jurisdiction"),
    ("SW04",   "DIG_COMPOUND_SWEEP_04_belief_prediction_foundations_and_masters.md",                      "belief_prediction_masters"),
    ("SW05",   "DIG_COMPOUND_SWEEP_05_prediction_trust_law_and_master_frames.md",                         "prediction_trust_master_frames"),
    ("SW06",   "DIG_COMPOUND_SWEEP_06_belief_justification_observer_frames_and_scientific_jurisdiction.md","observer_frames_scientific_jurisdiction"),
    ("AUX_07", "DIG_AUX_07_axioms_prediction_logic_and_epistemic_bedrock.md",                             "axioms_epistemic_bedrock"),
    ("SW13",   "DIG_COMPOUND_SWEEP_13_faith_uncertainty_evidence_and_action.md",                          "faith_uncertainty_action"),
    ("SW17",   "DIG_COMPOUND_SWEEP_17_credence_metric_selection_doxastic_agency_and_moral_commitment.md", "credence_doxastic_agency"),
    ("SW18",   "DIG_COMPOUND_SWEEP_18_sentence_intent_entailment_attribution_and_interpretive_authority.md","intent_attribution_authority"),
    ("SW19",   "DIG_COMPOUND_SWEEP_19_lens_availability_starting_whole_unconscious_agency_and_interpretive_success.md","lens_availability_unconscious_agency"),
    ("SW20",   "DIG_COMPOUND_SWEEP_20_metaphysical_grounding_presuppositions_brute_facts_ockham_derivat.md","metaphysical_grounding_brute_facts"),
    ("SW21",   "DIG_COMPOUND_SWEEP_21_suffering_minimization_catastrophic_pursuit_normative_completeness_and_reason_regress.md","suffering_minimization_reason_regress"),
    ("SW22",   "DIG_COMPOUND_SWEEP_22_archetypal_frame_mobility_power_legitimacy_ai_governance_auditor_convergence_and_trust.md","archetypal_frame_governance_convergence"),
    # + abandonment-rule / possibility-vs-plausibility cluster (Round-1 focus; IT-050 lives in SW08)
    ("SW08",   "DIG_COMPOUND_SWEEP_08_belief_justification_action_and_belief_rescue.md",                  "belief_rescue_immunization"),
    ("SW09",   "DIG_COMPOUND_SWEEP_09_plausibility_agnostic_priors_and_miracle_claims.md",               "plausibility_priors_miracles"),
]

TITLE        = re.compile(r"^#\s+\S")
KEEP_META    = re.compile(r"^\*\*(Status|Discovered topic):\*\*")
STAGE_OUTPUT = re.compile(r"^#{2,4}.*STAGE\s+\d+\s+OUTPUT", re.I)
FIELDDESK    = re.compile(r"^#{2,4}.*FIELD-DESK REVIEW", re.I)
STAGE_PROMPT = re.compile(r"^#{2,4}.*STAGE\s+\d+\s+PROMPT", re.I)
PREFLIGHT    = re.compile(r"^#{2,4}.*HUMAN PREFLIGHT", re.I)
# residual boilerplate marker: the execution command lives only in PROMPT blocks
PROMPT_MARK  = re.compile(r"PANHANDLERS DIG EXECUTION", re.I)


def header(code, src_name, title_line):
    return (
        f"{title_line}\n\n"
        f"> **De-protocoled dig - {code}.** Cleaned copy of `{src_name}` from the\n"
        f"> Pan Handlers circle archive: the Stage 1-4 extraction OUTPUT plus Nova's\n"
        f"> FIELD-DESK REVIEW sections, with the repeated protocol prompts, preflight,\n"
        f"> and header instructions removed. Project jargon (G-DIRECT, CO-###,\n"
        f"> NON-SITE, field-desk, availability tiers, etc.) is defined in `GLOSSARY.md`.\n"
        f"> Every claim keeps the confidence label it carried in the workbook; nothing\n"
        f"> here is a promoted verdict about a real person.\n"
    )


def clean(text):
    lines = text.splitlines()
    title_line = None
    kept, emit, n_out = [], False, 0
    for i, line in enumerate(lines):
        if i == 0 and TITLE.match(line):
            title_line = line
            continue
        if KEEP_META.match(line):
            kept.append(line)
            continue
        if STAGE_OUTPUT.search(line):
            emit = True; n_out += 1; kept.append(line); continue
        if FIELDDESK.search(line):
            emit = True; kept.append(line); continue
        if STAGE_PROMPT.search(line) or PREFLIGHT.search(line):
            emit = False; continue
        if emit:
            kept.append(line)
    if title_line is None:
        title_line = "# (untitled dig)"
    body = "\n".join(kept)
    residual = len(PROMPT_MARK.findall(body))
    return title_line, body, n_out, residual


def main():
    check = "--check" in sys.argv
    if not check:
        OUT.mkdir(parents=True, exist_ok=True)
    print("=" * 74)
    print("DE-PROTOCOL TREATMENT  (philosophical-core cut, n=%d)" % len(DIGS))
    print("mode: %s" % ("CHECK / dry-run" if check else "WRITE -> %s" % OUT))
    print("=" * 74)
    total_src = total_out = 0
    warnings = 0
    for code, src_name, slug in DIGS:
        sp = SRC / src_name
        if not sp.exists():
            print("[MISS] %-7s source not found: %s" % (code, src_name))
            warnings += 1
            continue
        raw = sp.read_text(encoding="utf-8", errors="replace")
        title_line, body, n_out, residual = clean(raw)
        src_lines = raw.count("\n") + 1
        out_lines = body.count("\n") + 1
        total_src += src_lines
        total_out += out_lines
        flag = "OK"
        if residual > 0 or n_out == 0:
            flag = "WARN"; warnings += 1
        print("[%-4s] %-7s src=%5d -> out=%5d  stage_outputs=%d  residual_prompts=%d  -> %s_%s.md"
              % (flag, code, src_lines, out_lines, n_out, residual, code, slug))
        if not check:
            content = header(code, src_name, title_line) + "\n" + body + "\n"
            (OUT / f"{code}_{slug}.md").write_text(content, encoding="utf-8")
    print("-" * 74)
    saved = total_src - total_out
    pct = (100.0 * total_out / total_src) if total_src else 0.0
    print("TOTAL  src=%d lines -> out=%d lines  (kept %.0f%%, stripped %d lines of wrapper)"
          % (total_src, total_out, pct, saved))
    print("warnings: %d" % warnings)
    if warnings == 0:
        print("ALL CLEAN - no residual protocol prompts, every dig has stage outputs.")
    return 1 if warnings else 0


if __name__ == "__main__":
    sys.exit(main())
