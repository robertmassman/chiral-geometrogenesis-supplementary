#!/usr/bin/env python3
"""
Check Proof Dependencies
========================
Scans all proof markdown files in docs/proofs/ and checks for broken
dependency references. Reports broken dependencies, orphan files, and
summary statistics.

Exit codes:
  0 - No broken dependencies found
  1 - Broken dependencies found

Key design decisions:
  - Many derivation files define inline theorems/definitions using their own
    internal section numbering (e.g., "Definition 1.1.1" inside Section 1.1).
    These are NOT cross-file references and must be detected and excluded.
  - We detect inline definitions by looking for bold-formatted definitions
    in the file body: **Definition X.Y.Z**, **Theorem X.Y.Z:**, etc.
  - References within a file to its own inline definitions are excluded.
  - References from OTHER files to inline definitions are checked against
    a global inline-definition index (mapped to the containing file).
"""

import os
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Optional, List, Dict, Set, Tuple

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOFS_DIR = PROJECT_ROOT / "docs" / "proofs"

# Subdirectories to scan (excluding verification-records)
SCAN_DIRS = [
    "foundations",
    "Phase0", "Phase1", "Phase2", "Phase3", "Phase4",
    "Phase5", "Phase6", "Phase7", "Phase8",
    "reference", "supporting",
]

# Proof-type keywords used in references
PROOF_TYPES = [
    "Theorem", "Proposition", "Lemma", "Definition", "Extension",
    "Corollary", "Derivation", "Prediction", "Proof", "Axiom",
]

# Abbreviated forms that map to full types
ABBREV_MAP = {
    "Prop": "Proposition",
    "Props": "Proposition",
    "Thm": "Theorem",
    "Def": "Definition",
    "Cor": "Corollary",
    "Lem": "Lemma",
}

# The framework uses phases 0-8 for the major numbering.
# Internal section numbers (like "Theorem 12.3.2" inside a file's own
# section 12) should NOT be treated as cross-file references.
# We only consider references where the first number component is 0-8.
VALID_PHASE_RANGE = range(0, 9)

# Numbering pattern: X.Y.Z or X.Y.Z followed by optional letter suffix(es)
# Examples: 0.0.3, 3.1.1, 0.0.17k, 0.0.17z2, 5.2.3b.1, 0.0.13a
# The suffix can be letters, digits, or dots for sub-numbering like 5.2.3b.1
NUMBER_PATTERN = r'(\d+)\.(\d+)\.(\d+[a-z0-9]*(?:\.\d+[a-z0-9]*)*)'

# Files that are NOT theorem/proof documents (non-proof .md files)
NON_PROOF_FILES = {
    "README.md", "CLAUDE.md", "PROOF-INDEX.md", "CATEGORY-INDEX.md",
    "RENUMBERING-PLAN.md", "Foundation-Assessment.md",
}

# Files with these prefixes are not numbered proof documents
NON_PROOF_PREFIXES = [
    "README", "CLAUDE", "PROOF-INDEX", "CATEGORY-INDEX",
    "RENUMBERING-PLAN", "Foundation-Assessment",
    "Axiom-Reduction-Action-Plan", "Gap-Analysis",
    "Research-", "Analysis-", "Gap-Resolution",
    "Open-Question", "Plan-", "Phase6-Scattering",
    "RESTRUCTURED-FILES-NOTE", "Color-Constraints",
    "Configuration-Space", "Global-Minimality",
    "Hedgehog-", "Heterotic-", "QCD-Skyrme",
    "Alpha-GUT-Derivation",
]


def is_non_proof_file(filename):
    # type: (str) -> bool
    """Check if a file is a non-proof document (README, research notes, etc.)."""
    if filename in NON_PROOF_FILES:
        return True
    for prefix in NON_PROOF_PREFIXES:
        if filename.startswith(prefix):
            return True
    return False


def collect_all_proof_files():
    # type: () -> Dict[str, Path]
    """
    Collect all .md proof files from the scan directories.
    Returns a dict mapping relative path -> absolute path.
    """
    files = {}
    for subdir in SCAN_DIRS:
        dirpath = PROOFS_DIR / subdir
        if not dirpath.exists():
            continue
        for f in sorted(dirpath.glob("*.md")):
            rel = f.relative_to(PROOFS_DIR)
            files[str(rel)] = f
    # Also include top-level proof files
    for f in sorted(PROOFS_DIR.glob("*.md")):
        rel = f.relative_to(PROOFS_DIR)
        files[str(rel)] = f
    return files


def extract_identifier_from_filename(filepath):
    # type: (Path) -> Optional[str]
    """
    Extract the proof identifier (e.g., "Theorem-0.0.3") from a filename.
    Returns None for non-proof files.
    """
    name = filepath.stem

    if is_non_proof_file(filepath.name):
        return None

    for proof_type in PROOF_TYPES:
        pattern = r'^({pt})-({np})(?:-.*)?$'.format(pt=proof_type, np=NUMBER_PATTERN)
        m = re.match(pattern, name)
        if m:
            return "{}-{}".format(m.group(1), m.group(2))

    # Also match "Proof-8.1.3b-..." style
    m = re.match(r'^(Proof)-({np})(?:-.*)?$'.format(np=NUMBER_PATTERN), name)
    if m:
        return "{}-{}".format(m.group(1), m.group(2))

    return None


def normalize_identifier(proof_type, number):
    # type: (str, str) -> str
    """
    Normalize a proof reference to a canonical form like "Theorem-0.0.3".
    """
    full_type = ABBREV_MAP.get(proof_type, proof_type)
    return "{}-{}".format(full_type, number)


def build_file_index(all_files):
    # type: (Dict[str, Path]) -> Dict[str, List[str]]
    """
    Build an index mapping normalized identifiers to file paths.
    """
    index = defaultdict(list)
    for rel_path, abs_path in all_files.items():
        ident = extract_identifier_from_filename(abs_path)
        if ident:
            index[ident].append(rel_path)
    return index


def extract_inline_definitions(content):
    # type: (str) -> Set[str]
    """
    Extract identifiers that are defined INLINE within a file's body.
    These are typically bold-formatted definitions like:
      **Definition 1.1.1:** ...
      **Theorem 3.3.1:** ...
      **Proposition 2.3.1:** ...
      ### Lemma 0.0.13a: ...

    Returns a set of normalized identifiers defined inline.
    """
    inline_defs = set()
    full_types = '|'.join(PROOF_TYPES)

    # Pattern 1: **Type X.Y.Z** or **Type X.Y.Z:** or **Type X.Y.Z (Name)** or **Type X.Y.Z.**
    pattern1 = r'\*\*({ft})\s+({np})[\s:*(\[.]'.format(ft=full_types, np=NUMBER_PATTERN)
    for m in re.finditer(pattern1, content):
        proof_type = m.group(1)
        number = m.group(2)
        first_num = int(m.group(3))
        if first_num in VALID_PHASE_RANGE:
            inline_defs.add(normalize_identifier(proof_type, number))

    # Pattern 2: ### Type X.Y.Z: or ### Type X.Y.Z (section headers defining inline)
    pattern2 = r'^##' + r'{1,3}' + r'\s+({ft})\s+({np})'.format(ft=full_types, np=NUMBER_PATTERN)
    for m in re.finditer(pattern2, content, re.MULTILINE):
        proof_type = m.group(1)
        number = m.group(2)
        first_num = int(m.group(3))
        if first_num in VALID_PHASE_RANGE:
            inline_defs.add(normalize_identifier(proof_type, number))

    return inline_defs


def is_contextual_false_positive(line):
    # type: (str) -> bool
    """
    Detect lines where a theorem/lemma reference is NOT a cross-file dependency
    but rather a contextual mention that should be excluded.

    Categories of false positives:
      1. Changelog/historical lines: "Promoted from former Lemma 1.1.3"
      2. Literature citations: "Weihrauch (2000), Theorem 4.1.16"
      3. Planned/future references: "Theorem 5.3.3 (not yet written)"
      4. Internal corollary with apostrophe numbering: "Corollary 0.1.0'.1"
    """
    stripped = line.strip()

    # 1. Changelog / historical lines
    changelog_keywords = [
        r'\bformer\b', r'\bpromoted\b', r'\brenamed\b', r'\bupgraded\b',
        r'\bpreviously\b.*\bknown\s+as\b', r'\boriginally\b',
        r'\bwas\s+(?:formerly|previously)\b',
    ]
    if stripped.startswith('*Revised:') or stripped.startswith('*Updated:'):
        return True
    if stripped.startswith('> *Revised:') or stripped.startswith('> *Updated:'):
        return True
    for kw in changelog_keywords:
        if re.search(kw, line, re.IGNORECASE):
            return True

    # 2. Literature citations: "Author (Year), Theorem X.Y.Z" or
    #    "Author (Year), §X.Y.Z" or "(Author Year, Theorem X.Y.Z)"
    #    Also: "*Reference:* Author (Year), Theorem X.Y.Z"
    if re.search(r'\b[A-Z][a-z]+(?:\s+(?:et\s+al\.?|&|and)\s+[A-Z][a-z]+)?\s*\(\d{4}\)', line):
        return True
    if stripped.startswith('*Reference:*') or stripped.startswith('**Reference:**'):
        return True

    # 3. Planned / future / not-yet-written references
    planned_keywords = [
        r'\bnot\s+yet\s+written\b', r'\bplanned\b', r'\bto\s+be\s+written\b',
        r'\bfuture\s+work\b', r'\bnot\s+yet\s+developed\b',
        r'\bwill\s+(?:use|need|require|extend|build)\b',
    ]
    for kw in planned_keywords:
        if re.search(kw, line, re.IGNORECASE):
            return True

    # 4. Internal sub-numbering with apostrophe (e.g., "Corollary 0.1.0'.1")
    if re.search(r"'\.\d+", line):
        return True

    return False


def extract_references_from_content(content, source_file, inline_defs_in_file):
    # type: (str, str, Set[str]) -> List[Tuple[str, str, str, int]]
    """
    Extract all proof references from file content that are NOT inline
    definitions within the same file and are NOT contextual false positives.
    Returns list of (proof_type, number, raw_text, line_number) tuples.
    """
    references = []
    lines = content.split('\n')

    full_types = '|'.join(PROOF_TYPES)
    full_pattern = r'\b({ft})\s+({np})\b'.format(ft=full_types, np=NUMBER_PATTERN)

    abbrevs = '|'.join(ABBREV_MAP.keys())
    abbrev_pattern = r'\b({ab})\s+({np})\b'.format(ab=abbrevs, np=NUMBER_PATTERN)

    link_file_pattern = r'\[?({ft})-({np})-[^\]]*\.md'.format(ft=full_types, np=NUMBER_PATTERN)

    for line_num, line in enumerate(lines, 1):
        # Skip lines that are contextual false positives
        if is_contextual_false_positive(line):
            continue

        # Full-name references
        for m in re.finditer(full_pattern, line):
            proof_type = m.group(1)
            number = m.group(2)
            first_num = int(m.group(3))
            if first_num not in VALID_PHASE_RANGE:
                continue
            norm = normalize_identifier(proof_type, number)
            # Skip if this is an inline definition in the same file
            if norm in inline_defs_in_file:
                continue
            references.append((proof_type, number, m.group(0), line_num))

        # Abbreviated references
        for m in re.finditer(abbrev_pattern, line):
            abbrev = m.group(1)
            number = m.group(2)
            first_num = int(m.group(3))
            if first_num not in VALID_PHASE_RANGE:
                continue
            full_type = ABBREV_MAP[abbrev]
            norm = normalize_identifier(full_type, number)
            if norm in inline_defs_in_file:
                continue
            references.append((full_type, number, m.group(0), line_num))

        # Markdown file links
        for m in re.finditer(link_file_pattern, line):
            proof_type = m.group(1)
            number = m.group(2)
            first_num = int(m.group(3))
            if first_num not in VALID_PHASE_RANGE:
                continue
            norm = normalize_identifier(proof_type, number)
            if norm in inline_defs_in_file:
                continue
            references.append((proof_type, number, m.group(0), line_num))

    return references


def get_own_identifier(filepath, content):
    # type: (Path, str) -> Optional[str]
    """
    Determine the proof identifier for a file, using filename first,
    then falling back to the first heading.
    """
    ident = extract_identifier_from_filename(filepath)
    if ident:
        return ident

    full_types = '|'.join(PROOF_TYPES)
    m = re.search(
        r'^#\s+({ft})\s+({np})'.format(ft=full_types, np=NUMBER_PATTERN),
        content, re.MULTILINE
    )
    if m:
        first_num = int(m.group(3))
        if first_num in VALID_PHASE_RANGE:
            return normalize_identifier(m.group(1), m.group(2))

    return None


def check_reference_exists(proof_type, number, file_index, global_inline_defs):
    # type: (str, str, Dict[str, List[str]], Set[str]) -> bool
    """
    Check whether a reference to a proof identifier has a corresponding file
    or is defined inline in some file.
    """
    ident = normalize_identifier(proof_type, number)

    # Direct match in file index
    if ident in file_index:
        return True

    # Match in global inline definitions (defined inside some other file)
    if ident in global_inline_defs:
        return True

    # For sub-identifiers with letter suffixes, check if parent exists
    # e.g., "Lemma 0.0.6d" -> check for Theorem-0.0.6 or Lemma-0.0.6
    base_match = re.match(r'^(\d+\.\d+\.\d+)[a-z]', number)
    if base_match:
        base_number = base_match.group(1)
        for pt in PROOF_TYPES:
            base_ident = "{}-{}".format(pt, base_number)
            if base_ident in file_index:
                return True
            if base_ident in global_inline_defs:
                return True

    # Derivation files might be stored under a different type prefix
    if proof_type == "Derivation":
        for pt in PROOF_TYPES:
            alt_ident = "{}-{}".format(pt, number)
            if alt_ident in file_index or alt_ident in global_inline_defs:
                return True

    return False


def is_xx_placeholder(number):
    # type: (str) -> bool
    """Check if a number contains XX placeholder numbering."""
    return 'XX' in number or 'xx' in number


def main():
    print("=" * 78)
    print("  PROOF DEPENDENCY CHECKER")
    print("  Scanning: docs/proofs/")
    print("=" * 78)
    print()

    # Collect all files
    all_files = collect_all_proof_files()
    print("Found {} markdown files in proof directories".format(len(all_files)))

    # Build file index
    file_index = build_file_index(all_files)
    print("Indexed {} unique proof identifiers".format(len(file_index)))

    # -----------------------------------------------------------------------
    # Phase 1: Build inline definition index from all files
    # -----------------------------------------------------------------------
    # For each file, extract inline definitions (bold-formatted definitions
    # that use section-internal numbering).
    file_inline_defs = {}    # rel_path -> set of normalized identifiers
    global_inline_defs = set()  # union of all inline defs across all files

    for rel_path, abs_path in sorted(all_files.items()):
        dirname = Path(rel_path).parts[0] if len(Path(rel_path).parts) > 1 else ""
        if dirname not in SCAN_DIRS and dirname != "":
            continue
        if is_non_proof_file(abs_path.name):
            continue
        try:
            content = abs_path.read_text(encoding='utf-8')
        except Exception:
            continue

        own_id = get_own_identifier(abs_path, content)
        inline_defs = extract_inline_definitions(content)

        # Remove the file's own identifier from inline defs (it's a file-level def)
        if own_id:
            inline_defs.discard(own_id)

        # Also remove identifiers that correspond to actual files
        # (these are real cross-references, not internal numbering)
        inline_defs_filtered = set()
        for idef in inline_defs:
            if idef not in file_index:
                inline_defs_filtered.add(idef)

        file_inline_defs[rel_path] = inline_defs_filtered
        global_inline_defs.update(inline_defs_filtered)

    print("Found {} inline definitions across all files".format(len(global_inline_defs)))
    print()

    # -----------------------------------------------------------------------
    # Phase 2: Scan files for references and check dependencies
    # -----------------------------------------------------------------------
    broken_deps = []           # (source_file, ref_type, ref_number, line_num, raw_text)
    placeholder_refs = []      # References with XX placeholder
    all_referenced_ids = set() # All identifiers that are referenced by others
    all_own_ids = {}           # file -> own identifier
    file_references = {}       # file -> set of normalized identifiers it references

    proof_files_scanned = 0
    for rel_path, abs_path in sorted(all_files.items()):
        dirname = Path(rel_path).parts[0] if len(Path(rel_path).parts) > 1 else ""
        if dirname not in SCAN_DIRS and dirname != "":
            continue
        if is_non_proof_file(abs_path.name):
            continue

        proof_files_scanned += 1

        try:
            content = abs_path.read_text(encoding='utf-8')
        except Exception as e:
            print("WARNING: Could not read {}: {}".format(rel_path, e))
            continue

        own_id = get_own_identifier(abs_path, content)
        if own_id:
            all_own_ids[rel_path] = own_id

        # Get inline defs for this file (to exclude same-file refs)
        inline_defs_this = file_inline_defs.get(rel_path, set())

        # Extract references (already filters out inline defs in same file)
        refs = extract_references_from_content(content, rel_path, inline_defs_this)

        file_refs = set()

        for proof_type, number, raw_text, line_num in refs:
            norm_id = normalize_identifier(proof_type, number)

            # Skip self-references
            if own_id and norm_id == own_id:
                continue

            # Skip XX placeholder references
            if is_xx_placeholder(number):
                placeholder_refs.append((rel_path, proof_type, number, line_num, raw_text))
                continue

            file_refs.add(norm_id)
            all_referenced_ids.add(norm_id)

            # Check if reference target exists
            if not check_reference_exists(proof_type, number, file_index, global_inline_defs):
                broken_deps.append((rel_path, proof_type, number, line_num, raw_text))

        file_references[rel_path] = file_refs

    # -----------------------------------------------------------------------
    # Deduplicate broken deps (same file + same target, keep first occurrence)
    # -----------------------------------------------------------------------
    seen = set()
    deduped_broken = []
    for entry in broken_deps:
        source, ptype, num, line, raw = entry
        key = (source, ptype, num)
        if key not in seen:
            seen.add(key)
            deduped_broken.append(entry)

    # -----------------------------------------------------------------------
    # Report: Broken Dependencies
    # -----------------------------------------------------------------------
    print("=" * 78)
    print("  BROKEN DEPENDENCIES")
    print("=" * 78)
    print()

    if deduped_broken:
        by_file = defaultdict(list)
        for source, ptype, num, line, raw in deduped_broken:
            by_file[source].append((ptype, num, line, raw))

        by_target = defaultdict(list)
        for source, ptype, num, line, raw in deduped_broken:
            target = normalize_identifier(ptype, num)
            by_target[target].append(source)

        print("Found {} broken dependency references (deduplicated) "
              "across {} files:".format(len(deduped_broken), len(by_file)))
        print()

        for source in sorted(by_file.keys()):
            refs = by_file[source]
            print("  {}".format(source))
            for ptype, num, line, raw in sorted(refs, key=lambda x: x[2]):
                print("    Line {:4d}: {} {}".format(line, ptype, num))
            print()

        print("-" * 78)
        print("  MISSING TARGETS (grouped by target)")
        print("-" * 78)
        print()
        for target in sorted(by_target.keys()):
            sources = sorted(set(by_target[target]))
            print("  {} (referenced {} time{})".format(
                target, len(sources), "s" if len(sources) != 1 else ""))
            for s in sources:
                print("    <- {}".format(s))
            print()
    else:
        print("  No broken dependencies found!")
        print()

    # -----------------------------------------------------------------------
    # Report: Placeholder References (XX numbering)
    # -----------------------------------------------------------------------
    if placeholder_refs:
        seen_ph = set()
        deduped_ph = []
        for entry in placeholder_refs:
            key = (entry[0], entry[1], entry[2])
            if key not in seen_ph:
                seen_ph.add(key)
                deduped_ph.append(entry)

        print("=" * 78)
        print("  PLACEHOLDER REFERENCES (XX numbering)")
        print("=" * 78)
        print()
        print("  Found {} references with XX placeholder numbering:".format(len(deduped_ph)))
        print()
        for source, ptype, num, line, raw in sorted(deduped_ph):
            print("  {}".format(source))
            print("    Line {:4d}: {} {}".format(line, ptype, num))
        print()

    # -----------------------------------------------------------------------
    # Report: Orphan Files
    # -----------------------------------------------------------------------
    print("=" * 78)
    print("  ORPHAN FILES (neither referenced by others nor reference others)")
    print("=" * 78)
    print()

    orphans = []
    for rel_path, own_id in sorted(all_own_ids.items()):
        is_referenced = own_id in all_referenced_ids
        refs_others = bool(file_references.get(rel_path, set()))
        if not is_referenced and not refs_others:
            orphans.append((rel_path, own_id))

    if orphans:
        print("  Found {} orphan proof files:".format(len(orphans)))
        print()
        for rel_path, own_id in orphans:
            print("    {:45s}  {}".format(own_id, rel_path))
        print()
    else:
        print("  No orphan files found!")
        print()

    # -----------------------------------------------------------------------
    # Report: Summary Statistics
    # -----------------------------------------------------------------------
    print("=" * 78)
    print("  SUMMARY STATISTICS")
    print("=" * 78)
    print()
    print("  Total markdown files found:          {}".format(len(all_files)))
    print("  Proof files scanned:                 {}".format(proof_files_scanned))
    print("  Unique proof identifiers indexed:    {}".format(len(file_index)))
    print("  Inline definitions detected:         {}".format(len(global_inline_defs)))
    print("  Unique identifiers referenced:       {}".format(len(all_referenced_ids)))
    print("  Broken dependency references:        {}".format(len(deduped_broken)))
    print("  Placeholder (XX) references:         {}".format(len(placeholder_refs)))
    print("  Orphan files:                        {}".format(len(orphans)))
    print()

    # Print the file index for reference
    print("-" * 78)
    print("  PROOF FILE INDEX ({} identifiers)".format(len(file_index)))
    print("-" * 78)
    print()
    for ident in sorted(file_index.keys()):
        files = file_index[ident]
        if len(files) == 1:
            print("  {:50s} -> {}".format(ident, files[0]))
        else:
            print("  {}".format(ident))
            for f in sorted(files):
                print("    {:48s} -> {}".format("", f))
    print()

    # Exit code
    if deduped_broken:
        print("RESULT: FAIL - {} broken dependencies found".format(len(deduped_broken)))
        return 1
    else:
        print("RESULT: PASS - No broken dependencies")
        return 0


if __name__ == "__main__":
    sys.exit(main())
