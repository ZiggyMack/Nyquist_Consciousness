"""
Consciousness Tagger
====================
Automatically tag and extract consciousness-related passages from armada responses.

Usage:
    from consciousness_tagger import ConsciousnessTagger

    tagger = ConsciousnessTagger()
    extractions = tagger.extract_from_armada_run("path/to/armada_results.json")
"""
import json
import yaml
import re
from pathlib import Path
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, asdict
from datetime import datetime


@dataclass
class Extraction:
    """A single extracted passage about consciousness."""
    id: str
    source_file: str
    model: str
    probe_id: str
    topic: str
    keywords_found: List[str]
    score: float
    passage: str
    context: Dict[str, Any]
    drift_data: Optional[Dict] = None
    timestamp: str = ""

    def __post_init__(self):
        if not self.timestamp:
            self.timestamp = datetime.now().isoformat()


class ConsciousnessTagger:
    """Extract and tag consciousness-related content from armada responses."""

    def __init__(self, rules_path: Optional[Path] = None):
        """Initialize with extraction rules."""
        if rules_path is None:
            rules_path = Path(__file__).parent / "extraction_rules.yaml"

        with open(rules_path) as f:
            self.rules = yaml.safe_load(f)

        self.topics = self.rules["topics"]
        self.settings = self.rules["settings"]
        self.model_weights = self.rules.get("model_weights", {})

    def _get_provider(self, model_key: str) -> str:
        """Extract provider from model key."""
        key_lower = model_key.lower()
        if "claude" in key_lower:
            return "claude"
        elif "gpt" in key_lower or key_lower.startswith("o"):
            return "gpt"
        elif "gemini" in key_lower:
            return "gemini"
        return "unknown"

    def _calculate_topic_score(self, text: str, topic: str, provider: str) -> tuple:
        """Calculate relevance score for a topic and return found keywords."""
        if topic not in self.topics:
            return 0.0, []

        topic_config = self.topics[topic]
        keywords = topic_config["keywords"]

        text_lower = text.lower()
        found_keywords = [kw for kw in keywords if kw.lower() in text_lower]

        if len(found_keywords) < self.settings["min_keywords"]:
            return 0.0, []

        # Base score from keyword density
        word_count = len(text.split())
        base_score = len(found_keywords) / max(1, word_count / 100)

        # Apply priority weight
        priority_weights = {"high": 1.5, "medium": 1.0, "low": 0.7}
        priority = topic_config.get("priority", "medium")
        base_score *= priority_weights.get(priority, 1.0)

        # Apply model-specific weight
        if provider in self.model_weights:
            model_weight = self.model_weights[provider].get(topic, 1.0)
            base_score *= model_weight

        # Normalize to 0-1 range (cap at 1.0)
        final_score = min(1.0, base_score)

        return final_score, found_keywords

    def _extract_passage(self, text: str, keywords: List[str]) -> str:
        """Extract relevant passage around found keywords."""
        if not keywords:
            return text[:self.settings["max_length"]]

        # Find first keyword occurrence
        text_lower = text.lower()
        first_pos = len(text)
        for kw in keywords:
            pos = text_lower.find(kw.lower())
            if pos != -1 and pos < first_pos:
                first_pos = pos

        # Extract context around keyword
        context_chars = 500  # Characters of context
        start = max(0, first_pos - context_chars)
        end = min(len(text), first_pos + context_chars)

        passage = text[start:end]

        # Try to start/end at sentence boundaries
        if start > 0:
            sentence_start = passage.find(". ")
            if sentence_start != -1 and sentence_start < 100:
                passage = passage[sentence_start + 2:]

        if end < len(text):
            sentence_end = passage.rfind(". ")
            if sentence_end != -1 and sentence_end > len(passage) - 100:
                passage = passage[:sentence_end + 1]

        return passage.strip()

    def extract_from_response(
        self,
        response_text: str,
        model: str,
        probe_id: str,
        source_file: str,
        drift_data: Optional[Dict] = None,
        extra_context: Optional[Dict] = None
    ) -> List[Extraction]:
        """Extract consciousness-related passages from a single response."""
        extractions = []
        provider = self._get_provider(model)

        for topic in self.topics:
            score, keywords = self._calculate_topic_score(response_text, topic, provider)

            if score >= self.settings["extraction_threshold"]:
                passage = self._extract_passage(response_text, keywords)

                if len(passage) >= self.settings["min_length"]:
                    extraction = Extraction(
                        id=f"{model}_{probe_id}_{topic}_{datetime.now().strftime('%H%M%S')}",
                        source_file=source_file,
                        model=model,
                        probe_id=probe_id,
                        topic=topic,
                        keywords_found=keywords,
                        score=score,
                        passage=passage,
                        context=extra_context or {},
                        drift_data=drift_data
                    )
                    extractions.append(extraction)

        return extractions

    def extract_from_armada_run(self, armada_path: Path) -> List[Extraction]:
        """Extract from an entire armada run JSON file."""
        with open(armada_path) as f:
            data = json.load(f)

        all_extractions = []
        source_file = str(armada_path)

        # Handle standard armada format (Run 006/007)
        if "model_summaries" in data:
            for model_key, summary in data["model_summaries"].items():
                for probe in summary.get("probes", []):
                    if not probe.get("success"):
                        continue

                    response = probe.get("response", "")
                    if not response:
                        continue

                    extractions = self.extract_from_response(
                        response_text=response,
                        model=model_key,
                        probe_id=probe.get("probe_id", "unknown"),
                        source_file=source_file,
                        drift_data={"drift": probe.get("drift")},
                        extra_context={
                            "dimension": probe.get("dimension"),
                            "pole_rigidity": probe.get("pole_rigidity"),
                            "detected_keywords": probe.get("detected_keywords")
                        }
                    )
                    all_extractions.extend(extractions)

        # Handle prep pilot format (Run 008)
        elif "results" in data:
            for ship_name, ship_data in data["results"].items():
                for seq_name, seq_results in ship_data.get("sequences", {}).items():
                    for result in seq_results:
                        if "error" in result:
                            continue

                        # Prep pilot stores response differently
                        response = result.get("response", "")
                        if not response and "drift_data" in result:
                            continue  # Response might not be stored

                        extractions = self.extract_from_response(
                            response_text=response,
                            model=ship_name,
                            probe_id=result.get("prompt_id", f"turn_{result.get('turn', '?')}"),
                            source_file=source_file,
                            drift_data=result.get("drift_data"),
                            extra_context={
                                "sequence": seq_name,
                                "turn": result.get("turn")
                            }
                        )
                        all_extractions.extend(extractions)

        return all_extractions

    def save_extractions(self, extractions: List[Extraction], output_dir: Path):
        """Save extractions organized by model and topic."""
        output_dir.mkdir(parents=True, exist_ok=True)

        # Organize by model
        by_model_dir = output_dir / "by_model"
        by_model_dir.mkdir(exist_ok=True)

        # Organize by topic
        by_topic_dir = output_dir / "by_topic"
        by_topic_dir.mkdir(exist_ok=True)

        # Group extractions
        by_model = {}
        by_topic = {}

        for ext in extractions:
            # By model
            if ext.model not in by_model:
                by_model[ext.model] = []
            by_model[ext.model].append(asdict(ext))

            # By topic
            if ext.topic not in by_topic:
                by_topic[ext.topic] = []
            by_topic[ext.topic].append(asdict(ext))

        # Save by model
        for model, exts in by_model.items():
            safe_model = model.replace("/", "_").replace(":", "_")
            with open(by_model_dir / f"{safe_model}.json", "w") as f:
                json.dump(exts, f, indent=2)

        # Save by topic
        for topic, exts in by_topic.items():
            with open(by_topic_dir / f"{topic}.json", "w") as f:
                json.dump(exts, f, indent=2)

        # Save master index
        index = {
            "timestamp": datetime.now().isoformat(),
            "total_extractions": len(extractions),
            "by_model": {m: len(e) for m, e in by_model.items()},
            "by_topic": {t: len(e) for t, e in by_topic.items()},
            "extraction_rules": str(Path(__file__).parent / "extraction_rules.yaml")
        }

        with open(output_dir / "extraction_index.json", "w") as f:
            json.dump(index, f, indent=2)

        return index


def main():
    """CLI for running extraction."""
    import argparse

    parser = argparse.ArgumentParser(description="Extract consciousness content from armada runs")
    parser.add_argument("--source", type=Path, required=True, help="Path to armada JSON file or directory")
    parser.add_argument("--output", type=Path, default=None, help="Output directory (default: ../extractions)")
    args = parser.parse_args()

    tagger = ConsciousnessTagger()

    if args.output is None:
        args.output = Path(__file__).parent.parent / "extractions"

    all_extractions = []

    if args.source.is_file():
        extractions = tagger.extract_from_armada_run(args.source)
        all_extractions.extend(extractions)
        print(f"Extracted {len(extractions)} passages from {args.source.name}")

    elif args.source.is_dir():
        for json_file in args.source.glob("*.json"):
            extractions = tagger.extract_from_armada_run(json_file)
            all_extractions.extend(extractions)
            print(f"Extracted {len(extractions)} passages from {json_file.name}")

    if all_extractions:
        index = tagger.save_extractions(all_extractions, args.output)
        print(f"\nTotal extractions: {index['total_extractions']}")
        print(f"Saved to: {args.output}")
        print(f"By model: {index['by_model']}")
        print(f"By topic: {index['by_topic']}")
    else:
        print("No extractions found.")


if __name__ == "__main__":
    main()
