#!/usr/bin/env python3
"""
PROOF-INDEX.md Generator
=========================
Scans docs/proofs/ and generates a complete, hierarchical PROOF-INDEX.md
from the filesystem. Detects 3-file structures and groups files by phase
and document type.

Usage:
  python3 verification/generate_proof_index.py          # Preview to stdout
  python3 verification/generate_proof_index.py --write   # Write to PROOF-INDEX.md
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from collections import defaultdict
from datetime import date
from typing import Optional

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOFS_DIR = PROJECT_ROOT / "docs" / "proofs"
OUTPUT_FILE = PROOFS_DIR / "PROOF-INDEX.md"

PHASE_DIRS = [
    ("foundations", "Foundations (Phase -1)", "Minimal axioms, 0.0.x theorems"),
    ("Phase0", "Phase 0", "Pre-geometric foundations, 0.1.x-0.3.x"),
    ("Phase1", "Phase 1", "SU(3) geometry and chiral fields"),
    ("Phase2", "Phase 2", "Pressure-depression dynamics"),
    ("Phase3", "Phase 3", "Mass generation"),
    ("Phase4", "Phase 4", "Topological solitons"),
    ("Phase5", "Phase 5", "Emergent spacetime and gravity"),
    ("Phase6", "Phase 6", "Scattering theory"),
    ("Phase7", "Phase 7", "Renormalization and consistency"),
    ("Phase8", "Phase 8", "Predictions and tests"),
]

AUX_DIRS = [
    ("reference", "Reference", "Constants, techniques, protocols"),
    ("supporting", "Supporting", "Research and analysis documents"),
    ("verification-records", "Verification Records", "Multi-agent verification reports"),
]

# Document type prefixes in display order
DOC_TYPES = [
    "Definition",
    "Axiom",
    "Lemma",
    "Proposition",
    "Theorem",
    "Corollary",
    "Extension",
    "Derivation",
    "Prediction",
    "Proof",
]

# Pattern to extract type, number, and title from filenames
# e.g. "Theorem-7.6.10-Constructive-SU3-Yang-Mills-Mass-Gap-D4.md"
# Also handles placeholder numbers like "0.0.XX", "0.0.XXa", "0.0.XXc"
NUM_PART = r'(?:\d+|XX)[a-z0-9]*'
FILENAME_PATTERN = re.compile(
    r'^(' + '|'.join(DOC_TYPES) + r')-'
    r'(' + NUM_PART + r'\.' + NUM_PART + r'\.' + NUM_PART + r'(?:\.' + NUM_PART + r')*)'
    r'-(.+?)(?:-(Derivation|Applications))?\.md$'
)

# Non-proof files (research docs, plans, etc.) — handled separately
IGNORE_FILES = {"README.md", "CLAUDE.md", "PROOF-INDEX.md"}

# Companion suffixes
COMPANION_SUFFIXES = {"-Derivation.md", "-Applications.md"}

# Extra companion patterns (e.g. "Two-Loop-Calculation", "Lattice-QFT-On-Stella")
# These are files that are companions but don't follow the standard suffix pattern
EXTRA_COMPANION_PATTERN = re.compile(
    r'^(' + '|'.join(DOC_TYPES) + r')-'
    r'(\d+\.\d+\.\d+[a-z0-9]*(?:\.\d+[a-z0-9]*)*)'
    r'-(.+)\.md$'
)


# ---------------------------------------------------------------------------
# File scanning and parsing
# ---------------------------------------------------------------------------

def parse_filename(filename: str) -> dict | None:
    """Parse a proof filename into components."""
    m = FILENAME_PATTERN.match(filename)
    if not m:
        return None
    return {
        "type": m.group(1),
        "number": m.group(2),
        "title_slug": m.group(3),
        "companion": m.group(4),  # "Derivation", "Applications", or None
        "filename": filename,
    }


def is_companion(filename: str) -> bool:
    """Check if file is a known companion (Derivation/Applications)."""
    return any(filename.endswith(s) for s in COMPANION_SUFFIXES)


def title_from_slug(slug: str) -> str:
    """Convert a hyphenated slug to a readable title."""
    # Handle common abbreviations
    replacements = {
        "SU3": "SU(3)", "SU2": "SU(2)", "D4": "D=4",
        "QCD": "QCD", "EFT": "EFT", "UV": "UV", "IR": "IR",
        "FCC": "FCC", "RG": "RG", "VEV": "VEV", "GR": "GR",
        "QGP": "QGP", "EM": "EM", "CP": "CP", "GUT": "GUT",
        "OS": "OS", "FOS": "FOS", "PMNS": "PMNS", "CG": "CG",
        "LHC": "LHC", "PDG": "PDG",
    }
    words = slug.split("-")
    result = []
    for w in words:
        if w.upper() in replacements:
            result.append(replacements[w.upper()])
        elif w in replacements:
            result.append(replacements[w])
        else:
            result.append(w)
    return " ".join(result)


def sort_key_for_number(number: str):
    """Generate a sort key for theorem numbers like '7.6.10' or '0.0.17aa'."""
    parts = number.split(".")
    result = []
    for p in parts:
        # Split into numeric and alpha parts
        m = re.match(r'^(\d+)([a-z]*)(\d*)$', p)
        if m:
            result.append((int(m.group(1)), m.group(2), int(m.group(3)) if m.group(3) else 0))
        else:
            result.append((0, p, 0))
    return result


def scan_phase_dir(subdir: str) -> dict:
    """
    Scan a phase directory and return organized file data.
    Returns {doc_type: [entries]} where each entry is a main file + companions.
    """
    dirpath = PROOFS_DIR / subdir
    if not dirpath.is_dir():
        return {}, [], 0

    all_files = sorted(f.name for f in dirpath.iterdir()
                       if f.is_file() and f.suffix == ".md" and f.name not in IGNORE_FILES)
    all_files_set = set(all_files)
    total_count = len(all_files)

    # First pass: identify which files are genuine companions
    # A file ending in -Derivation.md or -Applications.md is only a companion
    # if the corresponding statement file (without that suffix) exists
    genuine_companions = set()
    for fname in all_files:
        for suffix in COMPANION_SUFFIXES:
            if fname.endswith(suffix):
                base = fname.replace(suffix, ".md")
                if base in all_files_set:
                    genuine_companions.add(fname)

    # Second pass: group files
    file_groups = defaultdict(dict)
    other_files = []

    for fname in all_files:
        if fname in genuine_companions:
            # This is a genuine companion — attach to its parent
            parsed = parse_filename(fname)
            if parsed:
                key = (parsed["type"], parsed["number"])
                file_groups[key][parsed["companion"]] = fname
            continue

        # Parse as a potential statement/standalone file
        # Re-parse without companion detection if the regex matched companion
        parsed = parse_filename(fname)
        if parsed and parsed["companion"] and fname not in genuine_companions:
            # The regex matched "Derivation"/"Applications" in the name,
            # but there's no corresponding statement file — treat as standalone
            parsed["title_slug"] = parsed["title_slug"] + "-" + parsed["companion"]
            parsed["companion"] = None

        if parsed and not parsed["companion"]:
            key = (parsed["type"], parsed["number"])
            if "Statement" in file_groups[key]:
                # Multiple files share the same (type, number) — treat extras
                file_groups[key][f"Extra:{parsed['title_slug']}"] = fname
            else:
                file_groups[key]["Statement"] = fname
                file_groups[key]["title"] = title_from_slug(parsed["title_slug"])
        elif not parsed:
            # Not a proof document — check if it's an extra for an existing entry
            m = EXTRA_COMPANION_PATTERN.match(fname)
            if m:
                doc_type = m.group(1)
                number = m.group(2)
                key = (doc_type, number)
                slug = m.group(3)
                if key in file_groups:
                    file_groups[key][f"Extra:{slug}"] = fname
                else:
                    file_groups[key]["Statement"] = fname
                    file_groups[key]["title"] = title_from_slug(slug)
            else:
                other_files.append(fname)

    # Organize by document type
    by_type = defaultdict(list)
    for (doc_type, number), group in sorted(file_groups.items(), key=lambda x: sort_key_for_number(x[0][1])):
        entry = {
            "type": doc_type,
            "number": number,
            "title": group.get("title", number),
            "statement": group.get("Statement"),
            "derivation": group.get("Derivation"),
            "applications": group.get("Applications"),
            "extras": {k: v for k, v in group.items()
                       if k.startswith("Extra:")},
        }
        by_type[doc_type].append(entry)

    return by_type, other_files, total_count


# ---------------------------------------------------------------------------
# Markdown generation
# ---------------------------------------------------------------------------

def format_entry(entry: dict, subdir: str) -> str:
    """Format a single proof entry as a table row."""
    number = entry["number"]
    title = entry["title"]
    statement = entry["statement"]
    derivation = entry["derivation"]
    applications = entry["applications"]
    extras = entry["extras"]

    has_companions = derivation or applications or extras

    if has_companions and statement:
        # 3-file structure (or more)
        parts = [f"[Statement]({subdir}/{statement})"]
        if derivation:
            parts.append(f"[Derivation]({subdir}/{derivation})")
        if applications:
            parts.append(f"[Applications]({subdir}/{applications})")
        for label, fname in sorted(extras.items()):
            nice_label = label.replace("Extra:", "").replace("-", " ")
            parts.append(f"[{nice_label}]({subdir}/{fname})")
        files_col = ", ".join(parts)
    elif statement:
        # Single file
        files_col = f"[{statement}]({subdir}/{statement})"
    else:
        # Companion only (shouldn't happen but handle gracefully)
        parts = []
        if derivation:
            parts.append(f"[Derivation]({subdir}/{derivation})")
        if applications:
            parts.append(f"[Applications]({subdir}/{applications})")
        files_col = ", ".join(parts) if parts else "*(missing statement)*"

    return f"| {number} | {title} | {files_col} |"


def generate_phase_section(subdir: str, heading: str, description: str) -> list[str]:
    """Generate the markdown section for a phase directory."""
    by_type, other_files, total_count = scan_phase_dir(subdir)
    if total_count == 0:
        return []

    lines = []
    lines.append(f"## {heading}")
    lines.append("")
    lines.append(f"**{total_count} files** — {description}")
    lines.append("")

    # Proof documents by type
    for doc_type in DOC_TYPES:
        entries = by_type.get(doc_type, [])
        if not entries:
            continue

        plural = doc_type + "s" if not doc_type.endswith("s") else doc_type
        lines.append(f"### {plural}")
        lines.append("")

        has_multi = any(e["derivation"] or e["applications"] or e["extras"] for e in entries)
        files_header = "Files" if has_multi else "File"
        lines.append(f"| Number | Title | {files_header} |")
        lines.append(f"|--------|-------|{'------|' if not has_multi else '-------|'}")

        for entry in entries:
            lines.append(format_entry(entry, subdir))

        lines.append("")

    # Non-proof documents (research docs, plans, etc.)
    if other_files:
        lines.append("### Other Documents")
        lines.append("")
        lines.append("| Title | File |")
        lines.append("|-------|------|")
        for fname in sorted(other_files):
            title = fname.replace(".md", "").replace("-", " ")
            lines.append(f"| {title} | [{fname}]({subdir}/{fname}) |")
        lines.append("")

    lines.append("---")
    lines.append("")

    return lines


def generate_aux_section(subdir: str, heading: str, description: str) -> list[str]:
    """Generate section for auxiliary directories (reference, supporting, verification-records)."""
    dirpath = PROOFS_DIR / subdir
    if not dirpath.is_dir():
        return []

    files = sorted(f.name for f in dirpath.iterdir()
                   if f.is_file() and f.suffix == ".md" and f.name not in IGNORE_FILES)

    if not files:
        return []

    lines = []
    lines.append(f"## {heading}")
    lines.append("")
    lines.append(f"**{len(files)} files** — {description}")
    lines.append("")

    if subdir == "verification-records":
        # Too many files — just show a summary
        lines.append(f"See [{subdir}/]({subdir}/) for the complete collection of:")
        lines.append("- Multi-agent verification reports")
        lines.append("- Adversarial physics verification")
        lines.append("- Mathematical verification")
        lines.append("- Literature verification")
        lines.append("- Executive summaries")
        lines.append("- Issue resolution documents")
    else:
        lines.append("| Title | File |")
        lines.append("|-------|------|")
        for fname in files:
            title = fname.replace(".md", "").replace("-", " ")
            lines.append(f"| {title} | [{fname}]({subdir}/{fname}) |")

    lines.append("")
    lines.append("---")
    lines.append("")

    return lines


def generate_statistics() -> list[str]:
    """Generate the statistics table."""
    lines = ["## Statistics", "", "| Directory | Files | Description |",
             "|-----------|-------|-------------|"]

    total = 0
    for subdir, heading, desc in PHASE_DIRS + AUX_DIRS:
        dirpath = PROOFS_DIR / subdir
        if not dirpath.is_dir():
            continue
        count = sum(1 for f in dirpath.iterdir()
                    if f.is_file() and f.suffix == ".md" and f.name not in IGNORE_FILES)
        total += count
        lines.append(f"| {subdir}/ | {count} | {desc} |")

    lines.append(f"| **TOTAL** | **{total}** | All proof files |")
    lines.append("")
    return lines


def generate_index() -> str:
    """Generate the complete PROOF-INDEX.md content."""
    today = date.today().isoformat()

    lines = []

    # Header
    lines.append("# Proof Index: Chiral Geometrogenesis")
    lines.append("")
    lines.append("> **Auto-generated hierarchical index of all proof documents**")
    lines.append(f"> Last updated: {today}")
    lines.append("")
    lines.append("This document provides an organized, hierarchical listing of all proof files in `docs/proofs/`. For theorem status, dependencies, and verification details, see [Mathematical-Proof-Plan.md](../Mathematical-Proof-Plan.md).")
    lines.append("")
    lines.append("---")
    lines.append("")

    # Table of Contents
    lines.append("## Table of Contents")
    lines.append("")
    for i, (subdir, heading, desc) in enumerate(PHASE_DIRS, 1):
        anchor = heading.lower().replace(" ", "-").replace("(", "").replace(")", "")
        lines.append(f"{i}. [{heading}](#{anchor}) — {desc}")
    offset = len(PHASE_DIRS)
    for i, (subdir, heading, desc) in enumerate(AUX_DIRS, offset + 1):
        anchor = heading.lower().replace(" ", "-")
        lines.append(f"{i}. [{heading}](#{anchor}) — {desc}")
    lines.append("")
    lines.append("---")
    lines.append("")

    # Naming Conventions
    lines.append("## Naming Conventions")
    lines.append("")
    lines.append("| Prefix | Description |")
    lines.append("|--------|-------------|")
    lines.append("| `Definition-` | Mathematical/physical definitions |")
    lines.append("| `Theorem-` | Major theorems requiring proof |")
    lines.append("| `Proposition-` | Significant propositions |")
    lines.append("| `Lemma-` | Supporting lemmas |")
    lines.append("| `Corollary-` | Consequences of theorems |")
    lines.append("| `Derivation-` | Detailed derivations |")
    lines.append("| `Prediction-` | Experimental/theoretical predictions |")
    lines.append("| `Proof-` | Additional proofs |")
    lines.append("| `Extension-` | Extensions of existing results |")
    lines.append("")
    lines.append("**3-File Structure** (for major theorems):")
    lines.append("- `[Type]-X.Y.Z.md` — Main statement")
    lines.append("- `[Type]-X.Y.Z-Derivation.md` — Full proof")
    lines.append("- `[Type]-X.Y.Z-Applications.md` — Verification & predictions")
    lines.append("")
    lines.append("---")
    lines.append("")

    # Phase sections
    for subdir, heading, desc in PHASE_DIRS:
        section = generate_phase_section(subdir, heading, desc)
        lines.extend(section)

    # Auxiliary sections
    for subdir, heading, desc in AUX_DIRS:
        section = generate_aux_section(subdir, heading, desc)
        lines.extend(section)

    # Statistics
    lines.extend(generate_statistics())

    lines.append("---")
    lines.append("")
    lines.append(f"*Generated from filesystem scan on {today}*")
    lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    content = generate_index()

    if "--write" in sys.argv:
        OUTPUT_FILE.write_text(content, encoding="utf-8")
        print(f"Wrote {OUTPUT_FILE}")

        # Quick stats
        line_count = content.count("\n")
        print(f"  {line_count} lines generated")
    else:
        print(content)
        print("\n" + "=" * 60)
        print("Preview mode. Use --write to update PROOF-INDEX.md")


if __name__ == "__main__":
    main()
