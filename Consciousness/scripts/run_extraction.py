"""
Run Extraction Script
=====================
Extract consciousness content from armada results.

Usage:
    py run_extraction.py
    py run_extraction.py --source path/to/armada_results/
"""
import sys
from pathlib import Path

# Add hooks directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "hooks"))

from consciousness_tagger import ConsciousnessTagger


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Extract consciousness content from armada runs")
    parser.add_argument(
        "--source",
        type=Path,
        default=Path(__file__).parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA" / "armada_results",
        help="Path to armada results directory"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).parent.parent / "extractions",
        help="Output directory for extractions"
    )
    args = parser.parse_args()

    print("=" * 60)
    print("CONSCIOUSNESS EXTRACTION")
    print("=" * 60)
    print(f"Source: {args.source}")
    print(f"Output: {args.output}")
    print("=" * 60)

    tagger = ConsciousnessTagger()
    all_extractions = []

    if args.source.is_file():
        extractions = tagger.extract_from_armada_run(args.source)
        all_extractions.extend(extractions)
        print(f"\nExtracted {len(extractions)} passages from {args.source.name}")

    elif args.source.is_dir():
        json_files = list(args.source.glob("*.json"))
        print(f"\nFound {len(json_files)} JSON files")

        for json_file in json_files:
            print(f"\nProcessing: {json_file.name}")
            try:
                extractions = tagger.extract_from_armada_run(json_file)
                all_extractions.extend(extractions)
                print(f"  -> Extracted {len(extractions)} passages")
            except Exception as e:
                print(f"  -> Error: {e}")

    else:
        print(f"Error: Source not found: {args.source}")
        return

    if all_extractions:
        print("\n" + "=" * 60)
        print("SAVING EXTRACTIONS")
        print("=" * 60)

        index = tagger.save_extractions(all_extractions, args.output)

        print(f"\nTotal extractions: {index['total_extractions']}")
        print(f"\nBy model:")
        for model, count in sorted(index['by_model'].items(), key=lambda x: -x[1]):
            print(f"  {model}: {count}")

        print(f"\nBy topic:")
        for topic, count in sorted(index['by_topic'].items(), key=lambda x: -x[1]):
            print(f"  {topic}: {count}")

        print(f"\nOutput saved to: {args.output}")
    else:
        print("\nNo extractions found. Check that armada results contain responses.")

    print("\n" + "=" * 60)
    print("EXTRACTION COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()
