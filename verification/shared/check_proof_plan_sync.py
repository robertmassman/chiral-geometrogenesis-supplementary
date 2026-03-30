#!/usr/bin/env python3
"""
Proof Plan & Index Sync Checker
================================
Detects staleness by comparing proof files on disk against entries in:
  1. docs/Mathematical-Proof-Plan.md
  2. docs/proofs/PROOF-INDEX.md

Reports:
  Category 1: Proof files on disk NOT in Proof Plan
  Category 2: Proof files on disk NOT in Proof Index
  Category 3: Proof Plan references to non-existent files
  Category 4: Proof Index references to non-existent files

Usage:
  python3 verification/check_proof_plan_sync.py
"""

import re
import sys
from pathlib import Path
from collections import defaultdict

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOFS_DIR = PROJECT_ROOT / "docs" / "proofs"
PROOF_PLAN = PROJECT_ROOT / "docs" / "Mathematical-Proof-Plan.md"
PROOF_INDEX = PROOFS_DIR / "PROOF-INDEX.md"

# Directories containing actual proof documents
PROOF_DIRS = [
    "foundations",
    "Phase0", "Phase1", "Phase2", "Phase3", "Phase4",
    "Phase5", "Phase6", "Phase7", "Phase8",
]

# Additional directories the Proof Plan may legitimately reference
AUXILIARY_DIRS = [
    "reference", "supporting", "verification-records",
]

ALL_KNOWN_DIRS = PROOF_DIRS + AUXILIARY_DIRS

# Files to always ignore
IGNORE_FILES = {
    "README.md", "CLAUDE.md", "PROOF-INDEX.md",
}

# Prefixes that indicate actual proof documents (vs research notes, plans, etc.)
PROOF_PREFIXES = (
    "Theorem-", "Proposition-", "Lemma-", "Definition-", "Corollary-",
    "Extension-", "Derivation-", "Prediction-", "Proof-", "Axiom-",
)

# Non-proof document patterns in foundations/ (research docs, plans, etc.)
# These are legitimate files but shouldn't be expected in the Proof Plan
NON_PROOF_PATTERNS = [
    r"^Research-",
    r"^Gap-",
    r"^Axiom-Reduction-",
    r"^CATEGORY-INDEX",
    r"^RENUMBERING-",
    r"-Plan\.md$",
    r"-Resolution-Plan\.md$",
    r"-Analysis\.md$",
]

# Companion file suffixes (part of 3-file structure)
COMPANION_SUFFIXES = ["-Derivation.md", "-Applications.md"]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def is_companion_file(filename: str) -> bool:
    """Check if a file is a Derivation or Applications companion."""
    return any(filename.endswith(suffix) for suffix in COMPANION_SUFFIXES)


def get_main_file_for_companion(filename: str) -> str:
    """Given a companion file, return the main statement file name."""
    for suffix in COMPANION_SUFFIXES:
        if filename.endswith(suffix):
            return filename.replace(suffix, ".md")
    return filename


def is_proof_document(filename: str) -> bool:
    """Check if filename looks like an actual proof document."""
    return filename.startswith(PROOF_PREFIXES)


def is_non_proof_document(filename: str) -> bool:
    """Check if filename matches a known non-proof pattern."""
    return any(re.search(pat, filename) for pat in NON_PROOF_PATTERNS)


# ---------------------------------------------------------------------------
# Scan disk for all files under proofs/
# ---------------------------------------------------------------------------

def scan_all_files() -> set[str]:
    """Scan ALL known directories and return set of relative paths."""
    all_files = set()
    for subdir in ALL_KNOWN_DIRS:
        dirpath = PROOFS_DIR / subdir
        if not dirpath.is_dir():
            continue
        for f in dirpath.iterdir():
            if f.is_file() and f.suffix == ".md" and f.name not in IGNORE_FILES:
                all_files.add(f"{subdir}/{f.name}")
    return all_files


def scan_proof_files() -> tuple[dict[str, set[str]], set[str]]:
    """
    Scan proof directories for actual proof documents.
    Returns (files_by_phase, all_proof_files).
    """
    files_by_phase = defaultdict(set)
    all_files = set()

    for subdir in PROOF_DIRS:
        dirpath = PROOFS_DIR / subdir
        if not dirpath.is_dir():
            continue
        for f in sorted(dirpath.iterdir()):
            if (f.is_file() and f.suffix == ".md"
                    and f.name not in IGNORE_FILES
                    and is_proof_document(f.name)
                    and not is_non_proof_document(f.name)):
                rel = f"{subdir}/{f.name}"
                files_by_phase[subdir].add(rel)
                all_files.add(rel)

    return files_by_phase, all_files


# ---------------------------------------------------------------------------
# Parse Proof Plan for file references
# ---------------------------------------------------------------------------

def parse_proof_plan_refs() -> tuple[set[str], set[str]]:
    """
    Extract proof file paths referenced in the Proof Plan.
    Returns (proof_refs, all_refs) where proof_refs are in PROOF_DIRS
    and all_refs includes auxiliary dirs too.
    """
    if not PROOF_PLAN.is_file():
        print(f"WARNING: Proof Plan not found at {PROOF_PLAN}")
        return set(), set()

    content = PROOF_PLAN.read_text(encoding="utf-8")
    proof_refs = set()
    all_refs = set()

    # Match markdown links: [text](proofs/subdir/filename.md)
    link_pattern = re.compile(r'\[.*?\]\(proofs/([^)]+\.md)\)')
    for m in link_pattern.finditer(content):
        path = m.group(1)
        all_refs.add(path)
        # Check if it's in a proof directory
        parts = path.split("/", 1)
        if len(parts) == 2 and parts[0] in PROOF_DIRS:
            proof_refs.add(path)

    return proof_refs, all_refs


# ---------------------------------------------------------------------------
# Parse Proof Index for file references
# ---------------------------------------------------------------------------

def parse_proof_index_refs() -> set[str]:
    """Extract proof file paths referenced in the Proof Index."""
    if not PROOF_INDEX.is_file():
        print(f"WARNING: Proof Index not found at {PROOF_INDEX}")
        return set()

    content = PROOF_INDEX.read_text(encoding="utf-8")
    refs = set()

    # Match markdown links relative to docs/proofs/
    dir_pattern = '|'.join(re.escape(d) for d in ALL_KNOWN_DIRS)
    link_pattern = re.compile(r'\[.*?\]\((' + dir_pattern + r')/([^)]+\.md)\)')
    for m in link_pattern.finditer(content):
        refs.add(f"{m.group(1)}/{m.group(2)}")

    return refs


# ---------------------------------------------------------------------------
# Analysis
# ---------------------------------------------------------------------------

def analyze():
    files_by_phase, proof_files = scan_proof_files()
    all_disk_files = scan_all_files()
    plan_proof_refs, plan_all_refs = parse_proof_plan_refs()
    index_refs = parse_proof_index_refs()

    # Separate main proof files from companions
    main_files = {f for f in proof_files if not is_companion_file(Path(f).name)}
    companion_files = {f for f in proof_files if is_companion_file(Path(f).name)}

    # Category 1: Main proof files NOT referenced in Proof Plan
    missing_from_plan = main_files - plan_proof_refs

    # Category 1b: Companion files whose main file is also not in Plan
    orphan_companions = set()
    for cf in companion_files:
        main_name = get_main_file_for_companion(Path(cf).name)
        main_path = str(Path(cf).parent / main_name)
        if main_path not in plan_proof_refs and cf not in plan_proof_refs:
            orphan_companions.add(cf)

    # Category 2: Proof files NOT referenced in Proof Index
    missing_from_index = proof_files - index_refs

    # Category 3: Proof Plan references to non-existent files
    # Check all_refs against all files on disk
    plan_broken = plan_all_refs - all_disk_files

    # Category 4: Proof Index references to non-existent files
    index_broken = index_refs - all_disk_files

    return {
        "proof_files": proof_files,
        "main_files": main_files,
        "companion_files": companion_files,
        "plan_proof_refs": plan_proof_refs,
        "plan_all_refs": plan_all_refs,
        "index_refs": index_refs,
        "missing_from_plan": missing_from_plan,
        "orphan_companions": orphan_companions,
        "missing_from_index": missing_from_index,
        "plan_broken": plan_broken,
        "index_broken": index_broken,
        "files_by_phase": files_by_phase,
    }


# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------

def print_grouped(file_set: set[str], indent: str = "    "):
    """Print files grouped by phase directory."""
    by_phase = defaultdict(list)
    for f in sorted(file_set):
        phase = f.split("/")[0]
        by_phase[phase].append(f)
    for phase in sorted(by_phase.keys()):
        print(f"\n  {phase}:")
        for f in by_phase[phase]:
            print(f"{indent}- {f}")


def print_report(results):
    total_proof = len(results["proof_files"])
    total_main = len(results["main_files"])
    total_companion = len(results["companion_files"])
    plan_refs = len(results["plan_proof_refs"])
    index_refs = len(results["index_refs"])

    print("=" * 70)
    print("PROOF PLAN & INDEX SYNC CHECK")
    print("=" * 70)
    print()
    print(f"Proof files on disk:     {total_proof} ({total_main} main + {total_companion} companion)")
    print(f"Proof Plan references:   {plan_refs} (proof dirs only)")
    print(f"Proof Index references:  {index_refs}")
    print()

    # Category 1: Missing from Plan
    missing_plan = results["missing_from_plan"]
    print("-" * 70)
    print(f"Cat 1: Main proof files NOT in Proof Plan  [{len(missing_plan)} found]")
    print("-" * 70)
    if missing_plan:
        print_grouped(missing_plan)
    else:
        print("  None — Proof Plan is fully synced!")
    print()

    # Category 1b: Orphan companions
    orphan_comp = results["orphan_companions"]
    if orphan_comp:
        print("-" * 70)
        print(f"Cat 1b: Companion files with no main entry in Plan  [{len(orphan_comp)} found]")
        print("-" * 70)
        print_grouped(orphan_comp)
        print()

    # Category 2: Missing from Index
    missing_index = results["missing_from_index"]
    print("-" * 70)
    print(f"Cat 2: Proof files NOT in Proof Index  [{len(missing_index)} found]")
    print("-" * 70)
    if missing_index:
        print_grouped(missing_index)
    else:
        print("  None — Proof Index is fully synced!")
    print()

    # Category 3: Broken Plan links
    plan_broken = results["plan_broken"]
    print("-" * 70)
    print(f"Cat 3: Broken Proof Plan references  [{len(plan_broken)} found]")
    print("-" * 70)
    if plan_broken:
        for f in sorted(plan_broken):
            print(f"    - proofs/{f}")
    else:
        print("  None — all Proof Plan links are valid!")
    print()

    # Category 4: Broken Index links
    index_broken = results["index_broken"]
    print("-" * 70)
    print(f"Cat 4: Broken Proof Index references  [{len(index_broken)} found]")
    print("-" * 70)
    if index_broken:
        for f in sorted(index_broken):
            print(f"    - {f}")
    else:
        print("  None — all Proof Index links are valid!")
    print()

    # Summary table
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print(f"  {'Category':<50} {'Count':>5}  {'Severity':<8}")
    print(f"  {'-'*50} {'-'*5}  {'-'*8}")
    print(f"  {'Main proof files missing from Proof Plan':<50} {len(missing_plan):>5}  {'High':<8}")
    if orphan_comp:
        print(f"  {'Orphan companions (no main in Plan)':<50} {len(orphan_comp):>5}  {'Medium':<8}")
    print(f"  {'Proof files missing from Proof Index':<50} {len(missing_index):>5}  {'Medium':<8}")
    print(f"  {'Broken Proof Plan references':<50} {len(plan_broken):>5}  {'High':<8}")
    print(f"  {'Broken Proof Index references':<50} {len(index_broken):>5}  {'High':<8}")
    print()

    total_issues = (len(missing_plan) + len(orphan_comp) +
                    len(missing_index) + len(plan_broken) + len(index_broken))

    if total_issues == 0:
        print("  All proof files, Proof Plan, and Proof Index are in sync!")
    else:
        print(f"  {total_issues} total sync issues found.")
    print()

    return total_issues


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    results = analyze()
    total_issues = print_report(results)
    sys.exit(0 if total_issues == 0 else 1)


if __name__ == "__main__":
    main()
