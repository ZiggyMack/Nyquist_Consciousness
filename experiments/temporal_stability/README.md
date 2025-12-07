# TEMPORAL STABILITY EXPERIMENTS (S7)

**Testing the Identity-Locked Loop (ILL) Framework**

See [S7_ARMADA/README.md](S7_ARMADA/README.md) for complete Armada documentation.

---

## QUICK START

```bash
# Install all dependencies (from this directory)
py -m pip install -r requirements.txt

# Run S7 Armada experiments
cd S7_ARMADA
py 4_BASIN_TOPOLOGY/run008_prep_pilot.py  # Note: requires API keys in file
```

---

## REQUIREMENTS.TXT PHILOSOPHY

**This file is intentionally maintained as the single source of truth for all S7 dependencies.**

A cold-boot Claude (or any new contributor) should be able to:

1. Navigate to this directory
2. Run `py -m pip install -r requirements.txt`
3. Successfully execute ANY script in this directory or subdirectories

When adding new functionality that requires new packages:

- **Always** add the dependency to `requirements.txt`
- Include a comment explaining what it's for
- Test that a fresh install works

Current dependencies cover:

- **API clients**: anthropic, openai, google-generativeai
- **Data processing**: pyyaml, python-dotenv, numpy
- **Visualization**: matplotlib

---

## ⚠️ API KEYS WARNING - READ THIS BEFORE COMMITTING

**This is the #1 source of headaches in this project.**

### The Situation

Experiment scripts (like `4_BASIN_TOPOLOGY/run008_prep_pilot.py`) contain hardcoded API keys for Anthropic, OpenAI, and Google. These keys are:

- **REQUIRED** for running experiments
- **MUST NOT** be committed to git
- **MUST NOT** be deleted (we need them!)

### Before Any Git Commit

1. **Check `.gitignore`** - Ensure your script with keys is listed
2. **Run `git status`** - Look for any `*_with_keys.py` or similar files
3. **If you see key files staged** - STOP and add them to `.gitignore` first

Current `.gitignore` patterns for keys:

```
experiments/temporal_stability/S7_ARMADA/4_BASIN_TOPOLOGY/run008_prep_pilot.py
experiments/temporal_stability/S7_ARMADA/4_BASIN_TOPOLOGY/run008_with_keys.py
**/run*_with_keys.py
**/*API_KEY*
**/*api_key*
**/*secret*
```

### Creating New Experiment Scripts

When creating a new experiment that needs API keys:

1. Name it clearly (e.g., `run009_with_keys.py`)
2. Add it to `.gitignore` BEFORE your first commit
3. Consider using the `*_with_keys.py` naming convention (already gitignored)

### If You Accidentally Commit Keys

**Don't panic, but act quickly.** The keys are now in git history even if you delete the file.

**Option 1: If NOT pushed yet**

```bash
# Undo the last commit, keep changes staged
git reset --soft HEAD~1

# Remove the file from staging
git reset HEAD path/to/file_with_keys.py

# Add to .gitignore
echo "path/to/file_with_keys.py" >> .gitignore

# Recommit without the keys
git add .gitignore
git commit -m "Add gitignore for key file"
```

**Option 2: If already pushed (requires history rewrite)**

```bash
# Remove file from ALL history (destructive - coordinate with team!)
git filter-branch --force --index-filter \
  "git rm --cached --ignore-unmatch path/to/file_with_keys.py" \
  --prune-empty --tag-name-filter cat -- --all

# Force push (DANGEROUS - only if you're sure)
git push origin main --force
```

**Option 3: Use BFG Repo-Cleaner (easier)**

```bash
# Install BFG (faster than filter-branch)
# Then run:
bfg --delete-files file_with_keys.py
git reflog expire --expire=now --all && git gc --prune=now --aggressive
git push --force
```

**After any history rewrite:**

- Rotate/regenerate ALL exposed API keys immediately
- Notify Ziggy if keys may have been exposed

### The Golden Rule

**When in doubt, check `git status` before `git commit`.**

One extra `git status` is worth avoiding hours of git history surgery.

---

## DIRECTORY STRUCTURE

- **S7_ARMADA/** - Cross-architecture mapping (29 ships, Run 006+)
- **OUTPUT/** - Meta-loop results (Runs 001-005)
- **s7_*.py** - Core meta-loop scripts
- **s7_config.yaml** - Configuration
- **requirements.txt** - All Python dependencies for S7 work

---

## TWO PARADIGMS

**META-LOOP**: Deep single-model testing (adaptive curriculum)
**ARMADA**: Wide cross-architecture mapping (parallel 29-ship fleet)

Both feed Phase 3 Orchestrator and ILL Framework validation.
