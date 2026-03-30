#!/usr/bin/env python3
"""
Proof Link Completeness Audit
===============================
Performs a bidirectional dependency audit of all proof files in docs/proofs/.

Checks for:
  1. UNDECLARED DEPENDENCIES - Body references not listed in Dependencies section
  2. MISSING BACK-LINKS - A depends on B, but B's Enables section doesn't mention A
  3. UNREFERENCED PROOFS - Completely disconnected from the dependency graph
  4. DEPENDENCY CYCLES - Circular dependencies (A->B->C->A) in declared deps
  5. BACKWARD PHASE DEPENDENCIES - Phase N proof depending on Phase M where M > N

Usage:
  python3 check_proof_link_completeness.py
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

# Subdirectories to scan (proof content only)
SCAN_DIRS = [
    "foundations",
    "Phase0", "Phase1", "Phase2", "Phase3", "Phase4",
    "Phase5", "Phase6", "Phase7", "Phase8",
]

# Proof-type keywords
PROOF_TYPES = [
    "Theorem", "Proposition", "Lemma", "Definition", "Extension",
    "Corollary", "Derivation", "Prediction", "Proof", "Axiom",
]

# Abbreviated forms
ABBREV_MAP = {
    "Prop": "Proposition",
    "Props": "Proposition",
    "Thm": "Theorem",
    "Def": "Definition",
    "Cor": "Corollary",
    "Lem": "Lemma",
}

VALID_PHASE_RANGE = range(0, 9)

# Numbering pattern: X.Y.Z with optional letter suffix(es)
NUMBER_PATTERN = r'(\d+)\.(\d+)\.(\d+[a-z0-9]*(?:\.\d+[a-z0-9]*)*)'

# Files that are NOT theorem/proof documents
NON_PROOF_FILES = {
    "README.md", "CLAUDE.md", "PROOF-INDEX.md", "CATEGORY-INDEX.md",
    "RENUMBERING-PLAN.md", "Foundation-Assessment.md",
}

NON_PROOF_PREFIXES = [
    "README", "CLAUDE", "PROOF-INDEX", "CATEGORY-INDEX",
    "RENUMBERING-PLAN", "Foundation-Assessment",
    "Axiom-Reduction-Action-Plan", "Gap-Analysis",
    "Research-", "Analysis-", "Gap-Resolution",
    "Open-Question", "Plan-", "Phase6-Scattering",
    "RESTRUCTURED-FILES-NOTE", "Color-Constraints",
    "Configuration-Space", "Global-Minimality",
    "Hedgehog-", "Heterotic-", "QCD-Skyrme",
    "Alpha-GUT-Derivation", "Research-Plan",
]

# Mathematical context patterns: references that appear in derivation steps
MATH_CONTEXT_PATTERNS = [
    r'\bby\s+{ref}',
    r'\bfrom\s+{ref}',
    r'\busing\s+{ref}',
    r'\bvia\s+{ref}',
    r'\bestablished\s+in\s+{ref}',
    r'\bproven\s+in\s+{ref}',
    r'\bderived\s+in\s+{ref}',
    r'\bshown\s+in\s+{ref}',
    r'\bper\s+{ref}',
    r'\bfollows\s+from\s+{ref}',
    r'\brequires\s+{ref}',
    r'\bapplying\s+{ref}',
    r'\baccording\s+to\s+{ref}',
    r'\bsee\s+{ref}',
    r'\bcf\.\s*{ref}',
    r'\([\s]*{ref}[\s]*\)',             # (Theorem X.Y.Z)
    r'\[[\s]*{ref}[\s]*\]',             # [Theorem X.Y.Z]
    r'✅\s+{ref}',                       # ✅ Theorem X.Y.Z
    r'\$.*{ref}.*\$',                    # inside math context
    r'→.*{ref}',                         # → Theorem X.Y.Z
    r'{ref}\s*\(',                       # Theorem X.Y.Z (description)
    r'{ref}\s*—',                        # Theorem X.Y.Z — description
    r'{ref}\s*:',                        # Theorem X.Y.Z: description
]


def is_non_proof_file(filename):
    """Check if a file is a non-proof document."""
    if filename in NON_PROOF_FILES:
        return True
    for prefix in NON_PROOF_PREFIXES:
        if filename.startswith(prefix):
            return True
    return False


def is_xx_placeholder(number):
    """Check if a number contains XX placeholder numbering."""
    return 'XX' in number or 'xx' in number


def normalize_identifier(proof_type, number):
    """Normalize to canonical form like 'Theorem-0.0.3'."""
    full_type = ABBREV_MAP.get(proof_type, proof_type)
    return "{}-{}".format(full_type, number)


def collect_all_proof_files():
    """Collect all .md proof files from scan directories."""
    files = {}
    for subdir in SCAN_DIRS:
        dirpath = PROOFS_DIR / subdir
        if not dirpath.exists():
            continue
        for f in sorted(dirpath.glob("*.md")):
            if is_non_proof_file(f.name):
                continue
            rel = f.relative_to(PROOFS_DIR)
            files[str(rel)] = f
    return files


def extract_identifier_from_filename(filepath):
    """Extract the proof identifier from a filename."""
    name = filepath.stem
    if is_non_proof_file(filepath.name):
        return None
    for proof_type in PROOF_TYPES:
        pattern = r'^({pt})-({np})(?:-.*)?$'.format(pt=proof_type, np=NUMBER_PATTERN)
        m = re.match(pattern, name)
        if m:
            return "{}-{}".format(m.group(1), m.group(2))
    m = re.match(r'^(Proof)-({np})(?:-.*)?$'.format(np=NUMBER_PATTERN), name)
    if m:
        return "{}-{}".format(m.group(1), m.group(2))
    return None


def build_file_index(all_files):
    """Build index mapping identifiers to file paths."""
    index = defaultdict(list)
    for rel_path, abs_path in all_files.items():
        ident = extract_identifier_from_filename(abs_path)
        if ident:
            index[ident].append(rel_path)
    return index


def get_own_identifier(filepath, content):
    """Determine the proof identifier for a file."""
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


def find_section_boundaries(content):
    """
    Find line ranges for key sections in the file.
    Returns dict of section_type -> list of (start_line, end_line) ranges.
    """
    lines = content.split('\n')
    sections = {
        'dependencies': [],
        'enables': [],
        'references_bib': [],
        'changelog': [],
        'related': [],
    }

    # Patterns for section headers
    dep_patterns = [
        r'^\*\*Dependencies:?\*\*',
        r'^\*\*Depends on:?\*\*',
        r'^\*\*Prerequisites:?\*\*',
    ]
    enables_patterns = [
        r'^\*\*Enables:?\*\*',
        r'^\*\*Downstream:?\*\*',
        r'^\*\*Downstream Impact:?\*\*',
        r'^\*\*Downstream Usage:?\*\*',
        r'^\*\*Downstream Uses:?\*\*',
        r'^\*\*Dependent Theorems:?\*\*',
        r'^\*\*Used By:?\*\*',
        r'^\*\*What This Definition Enables:?\*\*',
        r'^\*\*What This Theorem Enables:?\*\*',
        r'^\*\*What This Theorem Provides:?\*\*',
    ]
    ref_patterns = [
        r'^##\s+References?\b',
        r'^##\s+Bibliography\b',
        r'^\*\*References:?\*\*',
    ]
    changelog_patterns = [
        r'^\*Revised:',
        r'^>\s+\*Revised:',
        r'^\*Updated:',
        r'^\*Version history',
        r'^##\s+Changelog',
        r'^##\s+Revision History',
        r'^##\s+Version History',
    ]
    related_patterns = [
        r'^###?\s+Related Theorems',
        r'^###?\s+Related Work',
        r'^###?\s+Connections?\s+to',
        r'^\*\*Related Theorems:?\*\*',
        r'^\*\*Related:?\*\*',
        r'^\*\*Connection',
        r'^###?\s+Verification Record',
    ]

    def find_section_end(start_idx):
        """Find where a metadata section ends (next blank line, heading, or bold marker)."""
        for j in range(start_idx + 1, min(start_idx + 50, len(lines))):
            line = lines[j].strip()
            # A new section header or horizontal rule
            if line.startswith('#') or line.startswith('---'):
                return j
            # A new bold metadata marker that's NOT a continuation bullet
            if re.match(r'^\*\*[A-Z]', line) and not line.startswith('**-'):
                return j
            # Empty line followed by non-list content
            if line == '' and j + 1 < len(lines):
                next_line = lines[j + 1].strip()
                if next_line and not next_line.startswith('-') and not next_line.startswith('*'):
                    return j
        return min(start_idx + 30, len(lines))

    def find_large_section_end(start_idx):
        """Find where a large section (References, Changelog) ends."""
        for j in range(start_idx + 1, len(lines)):
            line = lines[j].strip()
            if line.startswith('# ') or line.startswith('## '):
                return j
        return len(lines)

    for i, line in enumerate(lines):
        stripped = line.strip()
        for pat in dep_patterns:
            if re.match(pat, stripped):
                end = find_section_end(i)
                sections['dependencies'].append((i, end))
                break
        for pat in enables_patterns:
            if re.match(pat, stripped):
                end = find_section_end(i)
                sections['enables'].append((i, end))
                break
        for pat in ref_patterns:
            if re.match(pat, stripped):
                end = find_large_section_end(i)
                sections['references_bib'].append((i, end))
                break
        for pat in changelog_patterns:
            if re.match(pat, stripped):
                sections['changelog'].append((i, i + 1))
                break
        for pat in related_patterns:
            if re.match(pat, stripped):
                end = find_section_end(i)
                sections['related'].append((i, end))
                break

    return sections


def extract_identifiers_from_section(content, section_ranges):
    """Extract theorem/proposition identifiers from specific line ranges."""
    lines = content.split('\n')
    identifiers = set()
    full_types = '|'.join(PROOF_TYPES)
    abbrevs = '|'.join(ABBREV_MAP.keys())

    full_pattern = r'\b({ft})\s+({np})\b'.format(ft=full_types, np=NUMBER_PATTERN)
    abbrev_pattern = r'\b({ab})\s+({np})\b'.format(ab=abbrevs, np=NUMBER_PATTERN)
    # Also match file-link patterns: [Theorem-0.0.3b-...](...)
    link_pattern = r'({ft})-({np})'.format(ft=full_types, np=NUMBER_PATTERN)

    for start, end in section_ranges:
        for i in range(start, min(end, len(lines))):
            line = lines[i]
            for m in re.finditer(full_pattern, line):
                pt, num = m.group(1), m.group(2)
                first_num = int(m.group(3))
                if first_num in VALID_PHASE_RANGE and not is_xx_placeholder(num):
                    identifiers.add(normalize_identifier(pt, num))
            for m in re.finditer(abbrev_pattern, line):
                abbrev, num = m.group(1), m.group(2)
                first_num = int(m.group(3))
                if first_num in VALID_PHASE_RANGE and not is_xx_placeholder(num):
                    identifiers.add(normalize_identifier(ABBREV_MAP[abbrev], num))
            for m in re.finditer(link_pattern, line):
                pt, num = m.group(1), m.group(2)
                first_num = int(m.group(3))
                if first_num in VALID_PHASE_RANGE and not is_xx_placeholder(num):
                    identifiers.add(normalize_identifier(pt, num))

    return identifiers


def line_in_any_range(line_num, ranges):
    """Check if a 0-based line number is in any of the given ranges."""
    for start, end in ranges:
        if start <= line_num < end:
            return True
    return False


def is_in_excluded_section(line_idx, sections):
    """Check if a line is in a dependency, enables, references, changelog, or related section."""
    for section_type in ('dependencies', 'enables', 'references_bib', 'changelog', 'related'):
        if line_in_any_range(line_idx, sections[section_type]):
            return True
    return False


def is_in_peer_review_block(lines, line_idx):
    """Check if a line is inside a blockquote peer review block (> ...) in the header."""
    if line_idx >= len(lines):
        return False
    line = lines[line_idx]
    # Blockquote lines start with >
    if line.strip().startswith('>'):
        return True
    return False


def is_mathematical_context(line, proof_type, number):
    """
    Check if a reference appears in a mathematical/derivation context
    rather than just a casual background mention.
    """
    ref_str = r'{}\s+{}'.format(re.escape(proof_type), re.escape(number))
    for pattern_template in MATH_CONTEXT_PATTERNS:
        pattern = pattern_template.format(ref=ref_str)
        if re.search(pattern, line, re.IGNORECASE):
            return True
    return False


def is_contextual_false_positive(line):
    """
    Detect lines where a theorem/lemma reference is NOT a true dependency
    but rather a contextual mention that should be excluded.

    Categories:
      1. Changelog/historical lines: "Promoted from former Lemma 1.1.3"
      2. Literature citations: "Weihrauch (2000), Theorem 4.1.16"
      3. Planned/future references: "Theorem 5.3.3 (not yet written)"
      4. Internal sub-numbering with apostrophe: "Corollary 0.1.0'.1"
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

    # 2. Literature citations: "Author (Year), Theorem X.Y.Z"
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


def extract_body_references(content, own_id, sections):
    """
    Extract all theorem references from the body of a file,
    excluding self-references, dependency/enables sections,
    references/bibliography sections, changelog lines, and
    contextual false positives (literature citations, planned refs, etc.).

    Returns list of (identifier, line_number, raw_text, is_math_context) tuples.
    """
    lines = content.split('\n')
    references = []
    seen_on_line = {}  # (identifier, line_num) -> already recorded

    full_types = '|'.join(PROOF_TYPES)
    abbrevs = '|'.join(ABBREV_MAP.keys())
    full_pattern = r'\b({ft})\s+({np})\b'.format(ft=full_types, np=NUMBER_PATTERN)
    abbrev_pattern = r'\b({ab})\s+({np})\b'.format(ab=abbrevs, np=NUMBER_PATTERN)
    link_pattern = r'({ft})-({np})-[^\])\s]*'.format(ft=full_types, np=NUMBER_PATTERN)

    for line_idx, line in enumerate(lines):
        # Skip excluded sections
        if is_in_excluded_section(line_idx, sections):
            continue
        # Skip peer review blockquote headers (first ~60 lines)
        if line_idx < 60 and is_in_peer_review_block(lines, line_idx):
            continue
        # Skip contextual false positives (changelog, literature, planned, etc.)
        if is_contextual_false_positive(line):
            continue

        matches = []

        for m in re.finditer(full_pattern, line):
            pt, num = m.group(1), m.group(2)
            first_num = int(m.group(3))
            if first_num not in VALID_PHASE_RANGE:
                continue
            if is_xx_placeholder(num):
                continue
            norm = normalize_identifier(pt, num)
            math_ctx = is_mathematical_context(line, pt, num)
            matches.append((norm, line_idx + 1, m.group(0), math_ctx, pt, num))

        for m in re.finditer(abbrev_pattern, line):
            abbrev, num = m.group(1), m.group(2)
            first_num = int(m.group(3))
            if first_num not in VALID_PHASE_RANGE:
                continue
            if is_xx_placeholder(num):
                continue
            full_type = ABBREV_MAP[abbrev]
            norm = normalize_identifier(full_type, num)
            math_ctx = is_mathematical_context(line, abbrev, num)
            matches.append((norm, line_idx + 1, m.group(0), math_ctx, full_type, num))

        for m in re.finditer(link_pattern, line):
            pt, num = m.group(1), m.group(2)
            first_num = int(m.group(3))
            if first_num not in VALID_PHASE_RANGE:
                continue
            if is_xx_placeholder(num):
                continue
            norm = normalize_identifier(pt, num)
            # File links in derivation context are always relevant
            matches.append((norm, line_idx + 1, m.group(0), True, pt, num))

        for norm, line_num, raw, math_ctx, pt, num in matches:
            # Skip self-references
            if own_id and norm == own_id:
                continue
            key = (norm, line_num)
            if key not in seen_on_line:
                seen_on_line[key] = True
                references.append((norm, line_num, raw, math_ctx))

    return references


def extract_inline_definitions(content):
    """Extract identifiers defined inline within a file body."""
    inline_defs = set()
    full_types = '|'.join(PROOF_TYPES)
    pattern1 = r'\*\*({ft})\s+({np})[\s:*(\[.]'.format(ft=full_types, np=NUMBER_PATTERN)
    for m in re.finditer(pattern1, content):
        pt, num = m.group(1), m.group(2)
        first_num = int(m.group(3))
        if first_num in VALID_PHASE_RANGE:
            inline_defs.add(normalize_identifier(pt, num))
    pattern2 = r'^#{{2,4}}\s+({ft})\s+({np})'.format(ft=full_types, np=NUMBER_PATTERN)
    for m in re.finditer(pattern2, content, re.MULTILINE):
        pt, num = m.group(1), m.group(2)
        first_num = int(m.group(3))
        if first_num in VALID_PHASE_RANGE:
            inline_defs.add(normalize_identifier(pt, num))
    return inline_defs


def identifier_exists_in_index(ident, file_index):
    """Check if an identifier or a parent form exists in the file index."""
    if ident in file_index:
        return True
    # Check parent: Theorem-0.0.6d -> Theorem-0.0.6
    parts = ident.split('-', 1)
    if len(parts) == 2:
        ptype, num = parts
        base_match = re.match(r'^(\d+\.\d+\.\d+)[a-z]', num)
        if base_match:
            base_num = base_match.group(1)
            for pt in PROOF_TYPES:
                base_ident = "{}-{}".format(pt, base_num)
                if base_ident in file_index:
                    return True
    return False


def extract_phase_from_identifier(ident):
    """
    Extract phase number from a proof identifier.

    Mapping:
      0.0.x        -> -1 (foundations)
      0.1.x-0.3.x  -> 0
      N.x.x (1-8)  -> N

    Returns phase as int, or None if unparseable.
    """
    parts = ident.split('-', 1)
    if len(parts) != 2:
        return None
    num = parts[1]
    # Strip trailing letter suffixes: "0.0.17k" -> "0.0.17"
    num_clean = re.sub(r'[a-z]+$', '', num)
    segs = num_clean.split('.')
    if len(segs) < 2:
        return None
    try:
        first = int(segs[0])
        second = int(segs[1])
    except ValueError:
        return None
    if first == 0 and second == 0:
        return -1  # foundations
    if first == 0:
        return 0   # Phase 0
    if 1 <= first <= 8:
        return first
    return None


def detect_dependency_cycles(file_data, id_to_files):
    """
    Detect cycles in the declared dependency graph using DFS three-coloring.

    Returns list of cycles, each cycle is a list of identifiers forming the loop.
    """
    # Build adjacency: own_id -> set of dependency ids
    adj = defaultdict(set)
    all_ids = set()
    for rel_path, data in file_data.items():
        own_id = data['own_id']
        all_ids.add(own_id)
        for dep in data['declared_deps']:
            adj[own_id].add(dep)
            all_ids.add(dep)

    WHITE, GRAY, BLACK = 0, 1, 2
    color = {node: WHITE for node in all_ids}
    parent = {}
    cycles = []

    def dfs(u):
        color[u] = GRAY
        for v in adj.get(u, set()):
            if v not in color:
                continue
            if color[v] == GRAY:
                # Back-edge found — extract cycle
                cycle = [v, u]
                cur = u
                while cur in parent and parent[cur] != v:
                    cur = parent[cur]
                    cycle.append(cur)
                cycle.reverse()
                cycles.append(cycle)
            elif color[v] == WHITE:
                parent[v] = u
                dfs(v)
        color[u] = BLACK

    for node in sorted(all_ids):
        if color[node] == WHITE:
            dfs(node)

    return cycles


def check_backward_phase_dependencies(file_data):
    """
    Check for backward phase dependencies: a proof in Phase N depending on Phase M where M > N.

    Returns list of (rel_path, own_id, own_phase, dep_id, dep_phase) tuples.
    """
    findings = []
    for rel_path, data in sorted(file_data.items()):
        own_id = data['own_id']
        own_phase = extract_phase_from_identifier(own_id)
        if own_phase is None:
            continue
        for dep_id in sorted(data['declared_deps']):
            dep_phase = extract_phase_from_identifier(dep_id)
            if dep_phase is None:
                continue
            if dep_phase > own_phase:
                findings.append((rel_path, own_id, own_phase, dep_id, dep_phase))
    return findings


def main():
    print("=" * 80)
    print("  PROOF LINK COMPLETENESS AUDIT")
    print("  Scanning: docs/proofs/ (foundations + Phase0-Phase8)")
    print("=" * 80)
    print()

    # -----------------------------------------------------------------------
    # Collect files and build index
    # -----------------------------------------------------------------------
    all_files = collect_all_proof_files()
    file_index = build_file_index(all_files)
    print("Files scanned:                  {}".format(len(all_files)))
    print("Unique proof identifiers:       {}".format(len(file_index)))
    print()

    # -----------------------------------------------------------------------
    # Phase 1-4: Parse each file
    # -----------------------------------------------------------------------
    file_data = {}  # rel_path -> parsed data dict

    for rel_path, abs_path in sorted(all_files.items()):
        try:
            content = abs_path.read_text(encoding='utf-8')
        except Exception:
            continue

        own_id = get_own_identifier(abs_path, content)
        if not own_id:
            continue

        sections = find_section_boundaries(content)
        inline_defs = extract_inline_definitions(content)

        # Extract declared dependencies
        declared_deps = extract_identifiers_from_section(content, sections['dependencies'])
        # Remove self
        declared_deps.discard(own_id)

        # Extract declared enables/downstream
        declared_enables = extract_identifiers_from_section(content, sections['enables'])
        declared_enables.discard(own_id)
        has_enables_section = len(sections['enables']) > 0

        # Extract body references
        body_refs = extract_body_references(content, own_id, sections)

        # Remove inline defs from body refs (references to inline theorems in same file)
        body_refs_filtered = []
        for norm, line_num, raw, math_ctx in body_refs:
            if norm not in inline_defs:
                body_refs_filtered.append((norm, line_num, raw, math_ctx))

        file_data[rel_path] = {
            'own_id': own_id,
            'declared_deps': declared_deps,
            'declared_enables': declared_enables,
            'has_enables_section': has_enables_section,
            'body_refs': body_refs_filtered,
            'body_ref_ids': set(r[0] for r in body_refs_filtered),
            'math_context_refs': set(r[0] for r in body_refs_filtered if r[3]),
        }

    print("Proof files with identifiers:   {}".format(len(file_data)))
    print()

    # Build reverse lookup: identifier -> rel_path(s)
    id_to_files = defaultdict(list)
    for rel_path, data in file_data.items():
        id_to_files[data['own_id']].append(rel_path)

    # -----------------------------------------------------------------------
    # 3-File Structure Inheritance
    # -----------------------------------------------------------------------
    # For -Derivation.md and -Applications.md files, inherit the parent
    # statement file's declared deps (since the parent holds the canonical
    # Dependencies section for the 3-file structure).
    for rel_path, data in file_data.items():
        filename = Path(rel_path).name
        if '-Derivation' in filename or '-Applications' in filename:
            # Find the parent statement file with the same identifier
            own_id = data['own_id']
            parent_files = id_to_files.get(own_id, [])
            for pf in parent_files:
                if pf == rel_path:
                    continue
                pf_name = Path(pf).name
                # The parent is the file that is NOT -Derivation or -Applications
                if '-Derivation' not in pf_name and '-Applications' not in pf_name:
                    parent_data = file_data.get(pf)
                    if parent_data and parent_data['declared_deps']:
                        data['declared_deps'] = data['declared_deps'] | parent_data['declared_deps']

    # -----------------------------------------------------------------------
    # Category 1: UNDECLARED DEPENDENCIES
    # -----------------------------------------------------------------------
    # Body references in mathematical context that are NOT in declared deps
    cat1_findings = defaultdict(list)  # rel_path -> list of (identifier, line_num, raw)
    total_declared_deps = 0
    total_body_refs = 0

    for rel_path, data in sorted(file_data.items()):
        total_declared_deps += len(data['declared_deps'])
        total_body_refs += len(data['body_refs'])

        for norm, line_num, raw, math_ctx in data['body_refs']:
            # Only flag if in mathematical context
            if not math_ctx:
                continue
            # Skip if already declared as dependency
            if norm in data['declared_deps']:
                continue
            # Skip if already declared as enables (these are downstream, not upstream)
            if norm in data['declared_enables']:
                continue
            # Skip if the identifier doesn't exist in the file index
            # (already caught by check_proof_dependencies.py)
            if not identifier_exists_in_index(norm, file_index):
                continue
            # Skip references to the same base identifier (e.g., Derivation files
            # referencing their parent theorem)
            own_base = data['own_id'].split('-', 1)[1] if '-' in data['own_id'] else ''
            ref_base = norm.split('-', 1)[1] if '-' in norm else ''
            # Same number, different type (e.g., Theorem-3.0.2 refs from Derivation-3.0.2)
            if own_base and ref_base and own_base == ref_base:
                continue
            # Check if same base number (e.g., 3.0.2 for both)
            own_num = re.match(r'.*?-(\d+\.\d+\.\d+)', data['own_id'])
            ref_num = re.match(r'.*?-(\d+\.\d+\.\d+)', norm)
            if own_num and ref_num and own_num.group(1) == ref_num.group(1):
                continue

            cat1_findings[rel_path].append((norm, line_num, raw))

    # Deduplicate: same file + same identifier, keep first occurrence
    for rel_path in cat1_findings:
        seen = set()
        deduped = []
        for norm, line_num, raw in cat1_findings[rel_path]:
            if norm not in seen:
                seen.add(norm)
                deduped.append((norm, line_num, raw))
        cat1_findings[rel_path] = deduped

    # -----------------------------------------------------------------------
    # Category 2: MISSING BACK-LINKS
    # -----------------------------------------------------------------------
    # B declares "Depends on: A", but A has Enables section without B
    cat2_findings = defaultdict(list)  # upstream_file -> list of (upstream_id, downstream_id, downstream_file)

    for rel_path, data in sorted(file_data.items()):
        downstream_id = data['own_id']
        filename = Path(rel_path).name
        # Skip -Derivation and -Applications files for back-link checking;
        # their inherited deps shouldn't require separate back-links
        if '-Derivation' in filename or '-Applications' in filename:
            continue
        for dep_id in data['declared_deps']:
            # Find the upstream file(s)
            upstream_files = id_to_files.get(dep_id, [])
            for up_file in upstream_files:
                up_data = file_data.get(up_file)
                if not up_data:
                    continue
                # Only flag if upstream HAS an enables section
                if not up_data['has_enables_section']:
                    continue
                # Check if downstream_id is mentioned in upstream's enables
                if downstream_id not in up_data['declared_enables']:
                    # Also check if a parent/variant of downstream_id is mentioned
                    # e.g., enables mentions "Theorem 0.2.1" and downstream is "Theorem-0.2.1"
                    found = False
                    for en_id in up_data['declared_enables']:
                        # Check if they share the same base number
                        en_num = re.match(r'.*?-(\d+\.\d+\.\d+)', en_id)
                        dn_num = re.match(r'.*?-(\d+\.\d+\.\d+)', downstream_id)
                        if en_num and dn_num and en_num.group(1) == dn_num.group(1):
                            found = True
                            break
                    if not found:
                        cat2_findings[up_file].append((dep_id, downstream_id, rel_path))

    # Deduplicate
    for up_file in cat2_findings:
        seen = set()
        deduped = []
        for upstream_id, downstream_id, downstream_file in cat2_findings[up_file]:
            key = (upstream_id, downstream_id)
            if key not in seen:
                seen.add(key)
                deduped.append((upstream_id, downstream_id, downstream_file))
        cat2_findings[up_file] = deduped

    # -----------------------------------------------------------------------
    # Category 3: UNREFERENCED PROOFS
    # -----------------------------------------------------------------------
    # Proofs never referenced by any other proof AND don't reference anything
    all_referenced_ids = set()
    for rel_path, data in file_data.items():
        all_referenced_ids.update(data['body_ref_ids'])
        all_referenced_ids.update(data['declared_deps'])
        all_referenced_ids.update(data['declared_enables'])

    cat3_findings = []
    for rel_path, data in sorted(file_data.items()):
        own_id = data['own_id']
        # Skip Phase8 (terminal prediction files)
        if rel_path.startswith('Phase8/'):
            continue
        # Skip Research documents (already excluded by prefix filter, but just in case)
        if 'Research' in rel_path:
            continue
        # Check: is this proof referenced by anything?
        is_referenced = own_id in all_referenced_ids
        # Check: does this proof reference or depend on anything?
        has_connections = bool(data['declared_deps']) or bool(data['body_ref_ids'])
        if not is_referenced and not has_connections:
            cat3_findings.append((rel_path, own_id))

    # -----------------------------------------------------------------------
    # Category 4: DEPENDENCY CYCLES
    # -----------------------------------------------------------------------
    cat4_findings = detect_dependency_cycles(file_data, id_to_files)

    # -----------------------------------------------------------------------
    # Category 5: BACKWARD PHASE DEPENDENCIES
    # -----------------------------------------------------------------------
    cat5_findings = check_backward_phase_dependencies(file_data)

    # -----------------------------------------------------------------------
    # Print Report
    # -----------------------------------------------------------------------
    print("=" * 80)
    print("  SUMMARY STATISTICS")
    print("=" * 80)
    print()
    print("  Total proof files scanned:           {}".format(len(all_files)))
    print("  Files with proof identifiers:        {}".format(len(file_data)))
    print("  Unique proof identifiers indexed:    {}".format(len(file_index)))
    print("  Total declared dependencies:         {}".format(total_declared_deps))
    print("  Total body references:               {}".format(total_body_refs))
    print()

    cat1_count = sum(len(v) for v in cat1_findings.values())
    cat2_count = sum(len(v) for v in cat2_findings.values())
    cat3_count = len(cat3_findings)
    cat4_count = len(cat4_findings)
    cat5_count = len(cat5_findings)

    print("  Category 1 (Undeclared Dependencies):  {} findings in {} files".format(
        cat1_count, len(cat1_findings)))
    print("  Category 2 (Missing Back-Links):       {} findings in {} files".format(
        cat2_count, len(cat2_findings)))
    print("  Category 3 (Unreferenced Proofs):      {} findings".format(cat3_count))
    print("  Category 4 (Dependency Cycles):        {} cycles found".format(cat4_count))
    print("  Category 5 (Backward Phase Deps):      {} findings".format(cat5_count))
    print()

    # -------------------------------------------------------------------
    # Category 1: UNDECLARED DEPENDENCIES
    # -------------------------------------------------------------------
    print("=" * 80)
    print("  CATEGORY 1: UNDECLARED DEPENDENCIES")
    print("  (Body references in math context not listed in Dependencies section)")
    print("=" * 80)
    print()

    if cat1_findings:
        for rel_path in sorted(cat1_findings.keys()):
            findings = cat1_findings[rel_path]
            own_id = file_data[rel_path]['own_id']
            declared = file_data[rel_path]['declared_deps']
            print("  {} [{}]".format(rel_path, own_id))
            if declared:
                print("    Declared deps: {}".format(', '.join(sorted(declared))))
            else:
                print("    Declared deps: (none)")
            for norm, line_num, raw in sorted(findings, key=lambda x: x[1]):
                print("    Line {:4d}: {} (undeclared)".format(line_num, norm))
            print()
    else:
        print("  No undeclared dependencies found.")
        print()

    # -------------------------------------------------------------------
    # Category 2: MISSING BACK-LINKS
    # -------------------------------------------------------------------
    print("=" * 80)
    print("  CATEGORY 2: MISSING BACK-LINKS")
    print("  (B depends on A, but A's Enables section doesn't mention B)")
    print("=" * 80)
    print()

    if cat2_findings:
        for up_file in sorted(cat2_findings.keys()):
            findings = cat2_findings[up_file]
            up_id = file_data[up_file]['own_id']
            up_enables = file_data[up_file]['declared_enables']
            print("  {} [{}]".format(up_file, up_id))
            print("    Current Enables: {}".format(
                ', '.join(sorted(up_enables)) if up_enables else '(empty section)'))
            for upstream_id, downstream_id, downstream_file in sorted(findings, key=lambda x: x[1]):
                print("    MISSING: {} ({})".format(downstream_id, downstream_file))
            print()
    else:
        print("  No missing back-links found.")
        print()

    # -------------------------------------------------------------------
    # Category 3: UNREFERENCED PROOFS
    # -------------------------------------------------------------------
    print("=" * 80)
    print("  CATEGORY 3: UNREFERENCED PROOFS")
    print("  (Disconnected from dependency graph; Phase8 excluded)")
    print("=" * 80)
    print()

    if cat3_findings:
        for rel_path, own_id in cat3_findings:
            print("  {:55s}  {}".format(own_id, rel_path))
        print()
    else:
        print("  No unreferenced proofs found.")
        print()

    # -------------------------------------------------------------------
    # Category 4: DEPENDENCY CYCLES
    # -------------------------------------------------------------------
    print("=" * 80)
    print("  CATEGORY 4: DEPENDENCY CYCLES")
    print("  (Circular dependencies in the declared dependency graph)")
    print("=" * 80)
    print()

    if cat4_findings:
        for i, cycle in enumerate(cat4_findings, 1):
            cycle_str = ' -> '.join(cycle) + ' -> ' + cycle[0]
            print("  Cycle {}: {}".format(i, cycle_str))
            # Show which files are involved
            for ident in cycle:
                files = id_to_files.get(ident, [])
                for f in files:
                    print("    {} -> {}".format(ident, f))
        print()
    else:
        print("  No dependency cycles found.")
        print()

    # -------------------------------------------------------------------
    # Category 5: BACKWARD PHASE DEPENDENCIES
    # -------------------------------------------------------------------
    print("=" * 80)
    print("  CATEGORY 5: BACKWARD PHASE DEPENDENCIES")
    print("  (Phase N proof depends on Phase M where M > N)")
    print("=" * 80)
    print()

    if cat5_findings:
        # Group by file for readability
        current_file = None
        for rel_path, own_id, own_phase, dep_id, dep_phase in cat5_findings:
            if rel_path != current_file:
                if current_file is not None:
                    print()
                current_file = rel_path
                phase_label = "foundations" if own_phase == -1 else "Phase {}".format(own_phase)
                print("  {} [{}] ({})".format(rel_path, own_id, phase_label))
            dep_phase_label = "foundations" if dep_phase == -1 else "Phase {}".format(dep_phase)
            print("    BACKWARD: depends on {} ({})".format(dep_id, dep_phase_label))
        print()
    else:
        print("  No backward phase dependencies found.")
        print()

    # -------------------------------------------------------------------
    # INFORMATIONAL: MOST RELIED-ON PROOFS
    # -------------------------------------------------------------------
    # Count how many distinct proof identifiers declare each identifier
    # as a dependency (deduplicated per proof ID, so 3-file structures
    # with the same own_id count as one dependent).
    dep_count = defaultdict(set)  # target_id -> set of dependent own_ids
    for rel_path, data in file_data.items():
        own_id = data['own_id']
        for dep_id in data['declared_deps']:
            dep_count[dep_id].add(own_id)

    ranked = sorted(dep_count.items(), key=lambda x: len(x[1]), reverse=True)

    print("=" * 80)
    print("  INFORMATIONAL: MOST RELIED-ON PROOFS")
    print("  (Ranked by number of distinct proofs that declare them as dependencies)")
    print("=" * 80)
    print()
    print("  {:4s}  {:5s}  {:45s}  {}".format("Rank", "Deps", "Identifier", "Phase"))
    print("  {}  {}  {}  {}".format("-" * 4, "-" * 5, "-" * 45, "-" * 12))
    for rank, (ident, dependents) in enumerate(ranked[:30], 1):
        phase = extract_phase_from_identifier(ident)
        if phase is None:
            phase_label = "unknown"
        elif phase == -1:
            phase_label = "foundations"
        else:
            phase_label = "Phase {}".format(phase)
        print("  {:4d}  {:5d}  {:45s}  {}".format(rank, len(dependents), ident, phase_label))
    print()

    # -------------------------------------------------------------------
    # Final result
    # -------------------------------------------------------------------
    total_issues = cat1_count + cat2_count + cat3_count + cat4_count + cat5_count
    print("=" * 80)
    if total_issues > 0:
        print("  RESULT: {} total discrepancies found".format(total_issues))
    else:
        print("  RESULT: No discrepancies found - all links are complete")
    print("=" * 80)
    print()

    return 0


if __name__ == "__main__":
    sys.exit(main())
