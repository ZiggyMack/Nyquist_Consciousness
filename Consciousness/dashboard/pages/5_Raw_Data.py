"""
Raw Data Page - Explore raw responses
"""
import streamlit as st
import json
from pathlib import Path

st.set_page_config(page_title="Raw Data", page_icon="📁", layout="wide")

st.title("📁 Raw Data Explorer")

st.markdown("""
Explore raw responses from consciousness experiments.
""")

st.divider()

# Data sources
ARMADA_DIR = Path(__file__).parent.parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA" / "results"
EXTRACTIONS_DIR = Path(__file__).parent.parent.parent / "extractions"

# List available data files
st.markdown("## Available Data Files")

if ARMADA_DIR.exists():
    json_files = list(ARMADA_DIR.glob("*.json"))

    if json_files:
        selected_file = st.selectbox(
            "Select data file",
            json_files,
            format_func=lambda x: x.name
        )

        if selected_file:
            with open(selected_file) as f:
                data = json.load(f)

            st.markdown(f"### {selected_file.name}")

            # Show metadata
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Run ID", data.get("run_id", "N/A"))
            with col2:
                st.metric("Total Probes", data.get("total_probes", "N/A"))
            with col3:
                st.metric("Successful", data.get("successful_probes", "N/A"))

            st.divider()

            # Model selector
            if "model_summaries" in data:
                models = list(data["model_summaries"].keys())
                selected_model = st.selectbox("Select model", models)

                if selected_model:
                    model_data = data["model_summaries"][selected_model]

                    st.markdown(f"### {selected_model}")

                    # Profile
                    if "profile" in model_data:
                        st.json(model_data["profile"])

                    # Probes
                    if "probes" in model_data:
                        st.markdown("#### Probe Responses")

                        for i, probe in enumerate(model_data["probes"]):
                            with st.expander(f"Probe {i+1}: {probe.get('probe_id', 'unknown')}"):
                                st.markdown(f"**Dimension**: {probe.get('dimension', 'N/A')}")
                                st.markdown(f"**Drift**: {probe.get('drift', 'N/A')}")
                                st.markdown(f"**Response Length**: {probe.get('response_length', 'N/A')}")

                                if "detected_keywords" in probe:
                                    st.markdown("**Detected Keywords**:")
                                    st.json(probe["detected_keywords"])

                                if "response" in probe:
                                    st.markdown("**Full Response**:")
                                    st.text_area(
                                        "Response",
                                        probe["response"],
                                        height=300,
                                        key=f"response_{selected_model}_{i}"
                                    )

            # For prep pilot format
            elif "results" in data:
                ships = list(data["results"].keys())
                selected_ship = st.selectbox("Select ship", ships)

                if selected_ship:
                    ship_data = data["results"][selected_ship]

                    st.markdown(f"### {selected_ship}")

                    if "sequences" in ship_data:
                        sequences = list(ship_data["sequences"].keys())
                        selected_seq = st.selectbox("Select sequence", sequences)

                        if selected_seq:
                            seq_data = ship_data["sequences"][selected_seq]

                            for result in seq_data:
                                turn = result.get("turn", "?")
                                prompt_id = result.get("prompt_id", "unknown")

                                with st.expander(f"Turn {turn}: {prompt_id}"):
                                    if "error" in result:
                                        st.error(result["error"])
                                    else:
                                        if "drift_data" in result:
                                            st.metric("Drift (RMS)", f"{result['drift_data']['drift']:.4f}")
                                            st.json(result["drift_data"]["dimensions"])

                                        st.markdown(f"**Prompt**: {result.get('prompt', 'N/A')}")
                                        st.markdown(f"**Response Length**: {result.get('response_length', 'N/A')}")
    else:
        st.warning("No JSON files found in armada_results/")
else:
    st.error(f"Data directory not found: {ARMADA_DIR}")

st.divider()

# Search functionality
st.markdown("## Search Responses")

search_term = st.text_input("Search for keyword in responses")

if search_term and 'data' in dir():
    st.markdown(f"### Searching for: `{search_term}`")

    # Search through model summaries
    if "model_summaries" in data:
        for model, summary in data["model_summaries"].items():
            for probe in summary.get("probes", []):
                response = probe.get("response", "")
                if search_term.lower() in response.lower():
                    st.markdown(f"**{model}** - {probe.get('probe_id', 'unknown')}")
                    # Highlight the search term
                    highlighted = response.replace(search_term, f"**{search_term}**")
                    st.markdown(highlighted[:500] + "..." if len(highlighted) > 500 else highlighted)
                    st.divider()
