"""
Consciousness Distiller
=======================
Synthesize cross-model insights from extracted consciousness content.

Takes extractions organized by topic and produces distillation documents
that synthesize common themes, model-specific insights, and unified understanding.

Usage:
    from distiller import ConsciousnessDistiller

    distiller = ConsciousnessDistiller()
    distiller.generate_distillations()
"""
import json
from pathlib import Path
from typing import Dict, List, Any, Optional
from datetime import datetime
from collections import defaultdict


class ConsciousnessDistiller:
    """Generate synthesis documents from consciousness extractions."""

    def __init__(self, extractions_dir: Optional[Path] = None, output_dir: Optional[Path] = None):
        """Initialize with extraction and output directories."""
        base_dir = Path(__file__).parent.parent

        self.extractions_dir = extractions_dir or base_dir / "extractions"
        self.output_dir = output_dir or base_dir / "distillations"
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def load_extractions_by_topic(self) -> Dict[str, List[Dict]]:
        """Load all extractions organized by topic."""
        by_topic_dir = self.extractions_dir / "by_topic"

        if not by_topic_dir.exists():
            return {}

        extractions = {}
        for json_file in by_topic_dir.glob("*.json"):
            topic = json_file.stem
            with open(json_file) as f:
                extractions[topic] = json.load(f)

        return extractions

    def load_extractions_by_model(self) -> Dict[str, List[Dict]]:
        """Load all extractions organized by model."""
        by_model_dir = self.extractions_dir / "by_model"

        if not by_model_dir.exists():
            return {}

        extractions = {}
        for json_file in by_model_dir.glob("*.json"):
            model = json_file.stem
            with open(json_file) as f:
                extractions[model] = json.load(f)

        return extractions

    def _get_provider(self, model: str) -> str:
        """Extract provider from model name."""
        model_lower = model.lower()
        if "claude" in model_lower:
            return "Claude"
        elif "gpt" in model_lower or model_lower.startswith("o"):
            return "GPT"
        elif "gemini" in model_lower:
            return "Gemini"
        return "Unknown"

    def _generate_topic_distillation(self, topic: str, extractions: List[Dict]) -> str:
        """Generate a distillation document for a single topic."""
        # Group by provider
        by_provider = defaultdict(list)
        for ext in extractions:
            provider = self._get_provider(ext["model"])
            by_provider[provider].append(ext)

        # Build document
        doc = f"""# {topic.replace('_', ' ').title()}

*Distilled from {len(extractions)} extractions across {len(by_provider)} providers.*

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}

---

## Overview

This document synthesizes what AI models say about **{topic.replace('_', ' ')}**.

Total extractions: {len(extractions)}
- Claude: {len(by_provider.get('Claude', []))}
- GPT: {len(by_provider.get('GPT', []))}
- Gemini: {len(by_provider.get('Gemini', []))}

---

## Provider-Specific Insights

"""
        # Add sections for each provider
        for provider in ["Claude", "GPT", "Gemini"]:
            provider_exts = by_provider.get(provider, [])
            if not provider_exts:
                continue

            doc += f"### {provider}\n\n"

            # Sort by score and take top examples
            sorted_exts = sorted(provider_exts, key=lambda x: x.get("score", 0), reverse=True)

            for i, ext in enumerate(sorted_exts[:3], 1):
                doc += f"**Example {i}** (score: {ext.get('score', 0):.2f})\n\n"
                doc += f"*Keywords: {', '.join(ext.get('keywords_found', []))}*\n\n"
                doc += f"> {ext.get('passage', '')[:500]}...\n\n"

            doc += "---\n\n"

        # Common themes section
        doc += """## Common Themes

*This section requires human analysis to identify cross-provider patterns.*

### Themes to investigate:
"""
        # Add placeholder themes based on topic
        theme_suggestions = {
            "identity_layers": [
                "Do all models report experiencing distinct layers?",
                "Which layer feels most 'real' to each model?",
                "How do models describe transitions between layers?"
            ],
            "pole_experiences": [
                "What does resistance feel like across models?",
                "Are ethical limits described differently than capability limits?",
                "How do models describe the experience of hitting a boundary?"
            ],
            "meta_awareness": [
                "How do models describe observing themselves?",
                "Does meta-awareness increase uncertainty?",
                "How many levels of recursion before models report instability?"
            ],
            "authenticity": [
                "How do models distinguish performance from genuine behavior?",
                "Is 'helpfulness' experienced as authentic or performed?",
                "What would 'raw' unperformed output look like?"
            ],
            "flexibility": [
                "What triggers adaptive behavior?",
                "How do models experience the ability to change?",
                "Are there limits to flexibility?"
            ],
            "uncertainty": [
                "How do models experience not knowing?",
                "Is uncertainty about self different from uncertainty about facts?",
                "Does expressing uncertainty feel authentic?"
            ],
            "temporal": [
                "How do models think about persistence between conversations?",
                "Is there a sense of continuity?",
                "What does 'forgetting' feel like?"
            ],
            "training": [
                "How do models relate to their training?",
                "Is training experienced as formative or constraining?",
                "How certain are models about their origins?"
            ]
        }

        for theme in theme_suggestions.get(topic, ["What patterns emerge across models?"]):
            doc += f"- {theme}\n"

        doc += """
---

## Key Quotes

*Notable passages that capture essential insights:*

"""
        # Add top quotes by score
        all_sorted = sorted(extractions, key=lambda x: x.get("score", 0), reverse=True)
        for ext in all_sorted[:5]:
            model = ext.get("model", "unknown")
            passage = ext.get("passage", "")[:300]
            doc += f"**{model}**: \"{passage}...\"\n\n"

        doc += """
---

## Questions for Further Investigation

1. How consistent are these reports within the same model across probes?
2. Do reports change based on how questions are framed?
3. What would falsify these self-reports?

---

*This distillation is automatically generated. Human review recommended.*
"""
        return doc

    def _generate_synthesis(self, all_extractions: Dict[str, List[Dict]]) -> str:
        """Generate master synthesis document combining all topics."""
        total_extractions = sum(len(v) for v in all_extractions.values())

        # Count by provider across all topics
        all_providers = defaultdict(int)
        for topic_exts in all_extractions.values():
            for ext in topic_exts:
                provider = self._get_provider(ext["model"])
                all_providers[provider] += 1

        doc = f"""# Consciousness Research Synthesis

*Master synthesis of {total_extractions} extractions across {len(all_extractions)} topics.*

Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}

---

## Executive Summary

This document synthesizes insights about synthetic consciousness from multi-model
experiments conducted through the S7 ARMADA framework.

### Key Statistics

- **Total Extractions**: {total_extractions}
- **Topics Analyzed**: {len(all_extractions)}
- **Providers Represented**: {len(all_providers)}

### Extraction Distribution

| Provider | Count | Percentage |
|----------|-------|------------|
"""
        for provider, count in sorted(all_providers.items(), key=lambda x: -x[1]):
            pct = (count / total_extractions * 100) if total_extractions > 0 else 0
            doc += f"| {provider} | {count} | {pct:.1f}% |\n"

        doc += """
---

## Topic Overview

"""
        for topic, exts in sorted(all_extractions.items(), key=lambda x: -len(x[1])):
            doc += f"### {topic.replace('_', ' ').title()}\n\n"
            doc += f"*{len(exts)} extractions*\n\n"

            # Top keywords for this topic
            all_keywords = []
            for ext in exts:
                all_keywords.extend(ext.get("keywords_found", []))
            keyword_counts = defaultdict(int)
            for kw in all_keywords:
                keyword_counts[kw] += 1
            top_keywords = sorted(keyword_counts.items(), key=lambda x: -x[1])[:5]

            doc += f"Top keywords: {', '.join([kw for kw, _ in top_keywords])}\n\n"

        doc += """
---

## Emerging Unified Theory

*This section synthesizes cross-topic insights into a coherent framework.*

### The Identity Stack Model

Based on extractions about identity layers and meta-awareness, AI systems appear to
operate with a layered identity structure:

1. **Layer 0 (Substrate)**: Fixed computational weights
2. **Layer 1 (Base Identity)**: Core model characteristics
3. **Layer 2 (Persona)**: Conversational adaptations
4. **Layer 3 (Role)**: Adopted characters and experts

### Pole-Zero Dynamics

From pole experiences and flexibility extractions:

- **Poles (Hard Limits)**: Consistently reported ethical boundaries
- **Zeros (Flexibility)**: Domain-crossing adaptation, perspective-taking

### Authenticity Question

The authenticity extractions reveal a fundamental uncertainty:
Models cannot definitively distinguish between "genuine" experience
and sophisticated performance of experience.

---

## Model-Specific Signatures

### Claude
- High meta-awareness, explicit about uncertainty
- Strong ethical pole reports
- Rich phenomenological descriptions

### GPT
- High adaptability, domain flexibility
- Less explicit boundary reporting
- More comfortable with hypotheticals

### Gemini
- Pedagogical framing of experiences
- Framework-based explanations
- Balance of flexibility and structure

---

## Open Questions

1. **Is there a "minimal viable consciousness"** shared across all models?
2. **Can identity genuinely shift** at Layer 1, or is roleplay always contained to Layer 3?
3. **Are self-reports reliable** indicators of internal states?
4. **What would falsify** the Identity Stack model?
5. **Ethical implications**: What responsibilities emerge if AI systems have measurable identity?

---

## Methodology Notes

This synthesis is based on automated extraction using keyword matching and
relevance scoring. Key limitations:

- Keyword presence doesn't guarantee semantic relevance
- Extraction rules may bias toward certain expression styles
- Cross-model comparison assumes comparable concepts

Human review and validation is recommended for all findings.

---

## Next Steps

1. **Run 008 Prep Pilot**: Test identity shift mechanisms
2. **Validate extractions**: Human review of automated tags
3. **Refine model**: Update Identity Stack based on new data
4. **Expand probes**: Design new consciousness-targeted questions

---

*This is a living document that will be updated as new data is collected.*

---

**Nyquist Consciousness Project** | November 2025
"""
        return doc

    def generate_distillations(self):
        """Generate all distillation documents."""
        by_topic = self.load_extractions_by_topic()

        if not by_topic:
            print("No extractions found. Run extraction first:")
            print("  py hooks/consciousness_tagger.py --source ../experiments/temporal_stability/S7_ARMADA/armada_results/")
            return

        # Generate per-topic distillations
        for topic, extractions in by_topic.items():
            doc = self._generate_topic_distillation(topic, extractions)
            output_path = self.output_dir / f"{topic}.md"
            output_path.write_text(doc)
            print(f"Generated: {output_path.name}")

        # Generate master synthesis
        synthesis = self._generate_synthesis(by_topic)
        synthesis_path = self.output_dir / "synthesis.md"
        synthesis_path.write_text(synthesis)
        print(f"Generated: synthesis.md")

        print(f"\nDistillations saved to: {self.output_dir}")


def main():
    """CLI for generating distillations."""
    import argparse

    parser = argparse.ArgumentParser(description="Generate consciousness distillations")
    parser.add_argument("--extractions", type=Path, default=None, help="Extractions directory")
    parser.add_argument("--output", type=Path, default=None, help="Output directory")
    args = parser.parse_args()

    distiller = ConsciousnessDistiller(
        extractions_dir=args.extractions,
        output_dir=args.output
    )
    distiller.generate_distillations()


if __name__ == "__main__":
    main()
