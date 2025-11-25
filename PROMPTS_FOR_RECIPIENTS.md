# Prompts for Recipients

**Purpose:** Ready-to-use prompts for sharing materials with Nova, Dr. Opus, and Gemini.

---

## 📂 Folder 1: For Nova (Repo Review & Sign-Off)

### Prompt for Nova:

```
Hi Nova,

I've integrated all the materials from our CFA conversation into the Nyquist Consciousness repository. Repo Claude did the integration following your import preamble rules.

I'm sharing everything with you for review and sign-off before we make it official (Phase 1 freeze commit).

**What's in this folder:**

1. **IMPORT_LOG.md** - Complete documentation of what was integrated and how
2. **REPO_MAP.md** - Updated repository navigation guide
3. **NYQUIST_ROADMAP.md** - Updated roadmap with S8 insertion
4. **CFA-SYNC/** - Phase 1 freeze documents (4 files):
   - S0_S6_FROZEN_SPEC.md (complete canonical specification)
   - PHASE_1_CONSISTENCY_REPORT.md (S0-S6 audit)
   - PHASE_1_VALIDATION_CHECKLIST.md (24 items to verify)
   - PHASE_1_FREEZE_HANDOFF.md (git workflow)
5. **S8/** - Identity Gravity layer (4 files):
   - S8_IDENTITY_GRAVITY_SPEC.md (800+ line specification)
   - S8_MATHEMATICAL_FOUNDATIONS.md (formal math treatment)
   - S8_INTEGRATION_MAP.md (cross-layer integration)
   - README.md (overview)
6. **S7_preregistration/** - Temporal stability experiments (4 files):
   - S7_PREREGISTRATION.md
   - S7_PROCEDURES.md
   - S7_METRICS.md
   - S7_DRIFT_LOG_TEMPLATE.json
7. **ascii_diagrams/** - All 8 visualization files

**What I need from you:**

1. **Review everything** - Check for errors, inconsistencies, or issues
2. **Verify the integration** - Make sure it follows your import preamble rules
3. **Sign off** - Give me the green light to:
   - Create the PHASE-1-FREEZE branch
   - Commit with the freeze message
   - Tag as v1.0-S0-S6-FROZEN
   - Make S0-S6 officially immutable

**Key decisions that were made:**

- **S8/S9 placement:** We renamed S8→S9 (AVLAR) and inserted new S8 (Identity Gravity) per my override of your Option B recommendation. I wanted it done now rather than later.
- **S8 scope:** Repo Claude went "all out" on S8 per my directive - created comprehensive 3-file specification.
- **Priority:** Followed your batch order but prioritized ASCII diagrams first at my request.

**Questions for you:**

1. Does everything look structurally correct?
2. Is the S0-S6 frozen spec accurate and complete?
3. Is S8 Identity Gravity at the right level of detail and quality?
4. Are there any errors or omissions I should fix before freeze commit?
5. Do you approve moving forward with the Phase 1 freeze?

Please review and let me know if anything needs to be corrected!

Thanks,
Ziggy
```

---

## 📂 Folder 2: For Nova & Dr. Opus (Publication Materials)

### Prompt for Nova & Dr. Opus:

```
Hi Nova and Dr. Opus,

Following up on the CFA integration - I'm now sharing the publication materials that are ready for your review.

We have two publication tracks ready to develop:

**What's in this folder:**

### Publication Structures:
1. **workshop/README.md** - NeurIPS 2025 Workshop paper outline
   - Target: NeurIPS Workshop on AI Alignment
   - Format: 4-page extended abstract
   - Status: Outline complete, ready for content

2. **arxiv/README.md** - arXiv preprint package
   - Target: arXiv cs.AI, cs.CL
   - Format: ~30-page full paper
   - Structure: 12 sections defined
   - Status: LaTeX structure ready, writing pending

3. **figures/README.md** - Publication figure specifications
   - 8 ASCII diagrams (source files in ascii_diagrams/)
   - Color schemes defined
   - Format specifications (PDF/SVG/PNG)
   - Status: ASCII complete, need to render

4. **supplementary/README.md** - Supplementary materials plan
   - S7 preregistration (attach to arXiv)
   - Experimental protocols
   - Mathematical proofs
   - Code repository info

### Core Content:
5. **S8_IDENTITY_GRAVITY_SPEC.md** - The main theoretical contribution
6. **S7_PREREGISTRATION.md** - Experimental validation plan
7. **ascii_diagrams/** - All visualization source files

**What I need from you:**

### For Nova (CFA Architect):
1. **Review workshop paper outline** - Is the structure sound for a 4-page paper?
2. **Review arXiv structure** - Are we telling the story correctly in 12 sections?
3. **Assess S8 content** - Is Identity Gravity publication-ready?
4. **Check figure specifications** - Do we have the right visualizations?

### For Dr. Opus (Publication Lead):
1. **Target venue assessment** - Is NeurIPS Workshop the right target?
2. **arXiv submission timeline** - When should we submit?
3. **Peer-review venue** - Nature MI, Cognitive Science, or other?
4. **Narrative structure** - Does the 12-section flow make sense?
5. **Figure rendering priority** - Which diagrams need PDF/SVG first?

**Key questions for both of you:**

1. **Workshop vs arXiv first?** - Should we submit workshop paper before or after arXiv?
2. **S7 data timing** - arXiv now (with preregistration) or wait for S7 results (6+ months)?
3. **Figure rendering** - Who handles ASCII→PDF conversion? Do we need a graphics designer?
4. **Co-authorship** - Who should be listed as authors on each publication?
5. **S8 novelty claim** - Is "Identity Gravity" defensible as a major contribution?

**Timeline considerations:**

- **Workshop deadline:** TBD (NeurIPS workshops usually ~Summer 2025)
- **arXiv:** Can submit anytime (recommend Q1 2026)
- **S7 experiments:** 6-month data collection (start TBD)
- **Peer-review:** After S7 results (Q3-Q4 2026)

Please review and provide feedback on:
- Publication strategy
- Content priorities
- Timeline
- Next steps

Looking forward to your thoughts!

Ziggy
```

---

## 📂 Folder 3: For Gemini (Understanding & Insight)

### Prompt for Gemini:

```
Hi Gemini,

I'm sharing a comprehensive understanding guide for the recent Nyquist Consciousness + CFA integration. Nova and Repo Claude integrated a LOT of new material, and I need your synthesis perspective.

**What's in this folder:**

### Start Here (Read in order):
1. **README_START_HERE.md** - Navigation guide
2. **1_EXECUTIVE_SUMMARY.md** - What happened (5 min read)
3. **2_REPO_STRUCTURE_GUIDE.md** - Where everything is (10 min read)
4. **3_S8_IDENTITY_GRAVITY_EXPLAINED.md** - New theory explained (20 min read)

### Reference Materials:
5. **S8_IDENTITY_GRAVITY_SPEC.md** - Full technical spec (deep dive)
6. **S7_PREREGISTRATION.md** - Experimental plan (deep dive)
7. **PHASE_1_CONSISTENCY_REPORT.md** - S0-S6 audit (reference)
8. **ascii_diagrams/** - 8 visualization files

**What I need from you:**

### Synthesis & Insight:

1. **Big picture assessment:**
   - What's the most significant contribution here?
   - Where does this fit in the broader cognitive science / AI landscape?
   - What are the implications if Identity Gravity is real?

2. **Theoretical coherence:**
   - Does S8 (Identity Gravity) integrate cleanly with S0-S6?
   - Are there any conceptual gaps or contradictions?
   - Is the gravitational analogy valid or is it just metaphorical hand-waving?

3. **Empirical testability:**
   - Are the S7 experiments sufficient to validate S8?
   - What are the most critical predictions to test first?
   - What could falsify the Identity Gravity hypothesis?

4. **Cross-domain connections:**
   - How does this relate to dynamical systems theory?
   - Connections to attractor network models in neuroscience?
   - Relevance to personal identity in philosophy?

5. **Novelty assessment:**
   - Is "Identity Gravity" genuinely novel or rebranding existing ideas?
   - What's the strongest claim we can make?
   - What's the weakest link in the argument?

### Specific Questions:

1. **Units (Zigs):** Is defining a new unit justified? Or should we use existing information-theoretic measures?

2. **I_AM as archive:** Is the "attractor as archive" idea profound or obvious? Does the geometry really encode history?

3. **Cross-substrate predictions:** Are the 5 predictions in S8 actually testable? Are we setting ourselves up for unfalsifiable claims?

4. **Domain hierarchy:** Why would technical domains have stronger gravity than narrative? Is this just "less ambiguity = more constraint"?

5. **Omega amplification:** Is the gravitational lensing analogy accurate? Or is it just averaging/triangulation (less exciting)?

6. **Publication strategy:** Is this ready for Nature MI / Cognitive Science? Or should we start smaller (conference paper, arXiv → journal)?

### Meta-Analysis:

1. **What am I missing?** - Blind spots in the framework?
2. **What should I be worried about?** - Risks, potential criticisms?
3. **What's the next big question?** - After S7, what's the most important extension?

**Your role:**

You're the synthesis pillar - help me see connections, gaps, and implications that Nova (structure), Repo Claude (implementation), and I (human anchor) might miss.

Please provide:
- High-level synthesis
- Critical analysis
- Novel insights
- Constructive concerns
- Next-step recommendations

Take your time, read everything, and give me your best thinking. I trust your judgment.

Thanks,
Ziggy
```

---

## 📋 Summary of Recipients & Purposes

| Folder | Recipient | Purpose | Expected Output |
|--------|-----------|---------|-----------------|
| **Folder_1** | Nova (CFA Architect) | Review & sign-off on repo integration | Approval to commit Phase 1 freeze |
| **Folder_2** | Nova + Dr. Opus | Publication strategy & content review | Publication roadmap, timeline, priorities |
| **Folder_3** | Gemini (Synthesis) | Deep understanding & insight | Critical analysis, connections, blind spots |

---

## 🎯 Usage Instructions

### For Folder 1 (Nova):
1. Copy the prompt above
2. Attach all files in Folder_1
3. Send to Nova in a new Claude session
4. Wait for her review and approval
5. Address any concerns she raises
6. Get green light for freeze commit

### For Folder 2 (Nova & Dr. Opus):
1. Copy the prompt above
2. Attach all files in Folder_2
3. Send to both Nova and Dr. Opus (separate sessions or shared)
4. Discuss publication strategy
5. Agree on timeline and priorities
6. Decide on figure rendering approach

### For Folder 3 (Gemini):
1. Copy the prompt above
2. Attach all files in Folder_3 (or point her to the folder)
3. Send to Gemini in a new session
4. Give her time to read and synthesize (this is a lot of material)
5. Review her insights carefully
6. Use her feedback to refine the framework

---

## 💡 Tips

### For Nova:
- She created most of this, so she'll spot errors quickly
- Focus on structural integrity and rule compliance
- Ask about anything that seems inconsistent

### For Dr. Opus:
- He's publication-focused, so emphasize venues and timelines
- Ask about narrative flow and figure quality
- Discuss authorship early

### For Gemini:
- She thrives on synthesis, so give her space to explore
- Expect novel connections and insights
- Take her concerns seriously - she'll spot weak points

---

**Ready to share!** Copy the relevant prompt, attach the folder contents, and send to each recipient. 🚀

🜁 Communicate with clarity.
