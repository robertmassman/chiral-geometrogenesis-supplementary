#!/usr/bin/env python3
"""
Audit verification files against references in docs/proofs/.

This script:
1. Scans docs/proofs/ for all file references (.py, .png, .pdf, .svg, .json)
2. Scans verification/ for all actual files
3. Identifies unreferenced files for moving to legacy/
4. Generates a manifest and moves files
"""

import os
import re
import shutil
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# Project root
PROJECT_ROOT = Path(__file__).parent.parent
VERIFICATION_DIR = PROJECT_ROOT / "verification"
DOCS_PROOFS_DIR = PROJECT_ROOT / "docs" / "proofs"
LEGACY_DIR = VERIFICATION_DIR / "legacy"

# File extensions to audit
AUDIT_EXTENSIONS = {'.py', '.png', '.pdf', '.svg', '.json', '.md'}

# Files to always exclude from moving (config files)
EXCLUDE_FILES = {
    'CLAUDE.md', 'README.md', 'requirements.txt',
    'audit_verification_files.py',  # This script
    'LEGACY-MANIFEST.md'  # The manifest we generate
}

# Directories to skip entirely
SKIP_DIRS = {'legacy', '__pycache__', '.git'}


def extract_references_from_proofs():
    """Extract all file references from docs/proofs/ markdown files."""
    references = set()

    # Patterns to match file references
    patterns = [
        # Full path: verification/Phase5/theorem_5_2_1.py or verification/shared/Report.md
        r'verification/[^\s\)\"\'`\]]+\.(?:py|png|pdf|svg|json|md)',
        # Bare filename: theorem_5_2_1.py or theorem_5_2_1_verification.png
        r'[a-z0-9_]+\.(?:py|png|pdf|svg|json)',
        # Markdown report filenames (with hyphens and mixed case): Theorem-0.0.1-Report.md
        r'[A-Za-z0-9_.-]+-(?:Verification|Report|Summary|Resolution)[A-Za-z0-9_.-]*\.md',
        # Markdown image syntax: ![...](path.png)
        r'!\[[^\]]*\]\(([^)]+\.(?:png|pdf|svg))\)',
        # Code blocks or backticks: `filename.py` or `Report.md`
        r'`([^`]+\.(?:py|png|pdf|svg|json|md))`',
    ]

    for md_file in DOCS_PROOFS_DIR.rglob('*.md'):
        try:
            content = md_file.read_text(encoding='utf-8')

            for pattern in patterns:
                matches = re.findall(pattern, content, re.IGNORECASE)
                for match in matches:
                    # Handle tuple matches from grouped patterns
                    if isinstance(match, tuple):
                        match = match[0] if match[0] else match[1] if len(match) > 1 else ''
                    if match:
                        # Extract just the filename if it's a full path
                        filename = Path(match).name
                        references.add(filename)
                        # Also add the full relative path if it exists
                        if 'verification/' in match:
                            references.add(match)
        except Exception as e:
            print(f"Warning: Could not read {md_file}: {e}")

    return references


def scan_verification_files():
    """Scan verification/ directory for all auditable files."""
    all_files = []

    for root, dirs, files in os.walk(VERIFICATION_DIR):
        # Skip excluded directories
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]

        rel_root = Path(root).relative_to(VERIFICATION_DIR)

        for filename in files:
            if filename in EXCLUDE_FILES:
                continue

            ext = Path(filename).suffix.lower()
            if ext in AUDIT_EXTENSIONS:
                full_path = Path(root) / filename
                rel_path = rel_root / filename if str(rel_root) != '.' else Path(filename)
                all_files.append({
                    'filename': filename,
                    'rel_path': str(rel_path),
                    'full_path': full_path,
                    'extension': ext
                })

    return all_files


def categorize_files(all_files, references):
    """Categorize files as KEEP or LEGACY based on references."""
    keep_files = []
    legacy_files = []

    for file_info in all_files:
        filename = file_info['filename']
        rel_path = file_info['rel_path']
        full_ref_path = f"verification/{rel_path}"

        # Check if referenced by filename or full path
        is_referenced = (
            filename in references or
            rel_path in references or
            full_ref_path in references
        )

        if is_referenced:
            keep_files.append(file_info)
        else:
            legacy_files.append(file_info)

    return keep_files, legacy_files


def create_legacy_structure(legacy_files):
    """Create legacy folder structure based on files to move."""
    subdirs_needed = set()

    for file_info in legacy_files:
        rel_path = Path(file_info['rel_path'])
        if len(rel_path.parts) > 1:
            # Has subdirectory
            subdir = rel_path.parent
            subdirs_needed.add(subdir)

    # Create legacy directory and subdirectories
    LEGACY_DIR.mkdir(exist_ok=True)
    for subdir in subdirs_needed:
        (LEGACY_DIR / subdir).mkdir(parents=True, exist_ok=True)

    return subdirs_needed


def move_files_to_legacy(legacy_files, dry_run=True):
    """Move legacy files to legacy folder."""
    moved = []
    errors = []

    for file_info in legacy_files:
        src = file_info['full_path']
        rel_path = Path(file_info['rel_path'])
        dst = LEGACY_DIR / rel_path

        if dry_run:
            moved.append((src, dst))
        else:
            try:
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(src), str(dst))
                moved.append((src, dst))
            except Exception as e:
                errors.append((src, str(e)))

    return moved, errors


def generate_manifest(legacy_files, moved_count):
    """Generate LEGACY-MANIFEST.md."""
    manifest_lines = [
        "# Legacy Verification Files Manifest",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "",
        "## Overview",
        "",
        "These files were moved to legacy because they are not referenced in any",
        "proof document in `docs/proofs/`. They may include:",
        "",
        "- Intermediate/debugging versions of scripts",
        "- Superseded issue resolution scripts",
        "- Duplicate analyses from iterative development",
        "- Files for theorems that were renumbered",
        "",
        "## Statistics",
        "",
        f"- **Total files moved:** {moved_count}",
        "",
        "## Files by Directory",
        "",
    ]

    # Group by directory
    by_dir = defaultdict(list)
    for file_info in legacy_files:
        rel_path = Path(file_info['rel_path'])
        parent = str(rel_path.parent) if len(rel_path.parts) > 1 else "(root)"
        by_dir[parent].append(file_info['filename'])

    for dirname in sorted(by_dir.keys()):
        manifest_lines.append(f"### {dirname}")
        manifest_lines.append("")
        for filename in sorted(by_dir[dirname]):
            manifest_lines.append(f"- `{filename}`")
        manifest_lines.append("")

    return "\n".join(manifest_lines)


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Audit verification files")
    parser.add_argument('--dry-run', action='store_true', default=True,
                       help="Show what would be moved without moving (default)")
    parser.add_argument('--execute', action='store_true',
                       help="Actually move files to legacy/")
    parser.add_argument('--report-only', action='store_true',
                       help="Only generate report, don't move anything")
    args = parser.parse_args()

    dry_run = not args.execute

    print("=" * 60)
    print("Verification Files Audit")
    print("=" * 60)
    print()

    # Step 1: Extract references
    print("Step 1: Extracting references from docs/proofs/...")
    references = extract_references_from_proofs()
    print(f"  Found {len(references)} unique file references")

    # Step 2: Scan verification files
    print("\nStep 2: Scanning verification/ directory...")
    all_files = scan_verification_files()
    print(f"  Found {len(all_files)} auditable files")

    # Break down by extension
    by_ext = defaultdict(int)
    for f in all_files:
        by_ext[f['extension']] += 1
    for ext, count in sorted(by_ext.items()):
        print(f"    {ext}: {count}")

    # Step 3: Categorize
    print("\nStep 3: Categorizing files...")
    keep_files, legacy_files = categorize_files(all_files, references)
    print(f"  KEEP: {len(keep_files)} files (referenced)")
    print(f"  LEGACY: {len(legacy_files)} files (unreferenced)")

    if args.report_only:
        print("\n" + "=" * 60)
        print("REPORT ONLY MODE - No files will be moved")
        print("=" * 60)

        print("\nLegacy candidates by directory:")
        by_dir = defaultdict(list)
        for f in legacy_files:
            rel_path = Path(f['rel_path'])
            parent = str(rel_path.parent) if len(rel_path.parts) > 1 else "(root)"
            by_dir[parent].append(f['filename'])

        for dirname in sorted(by_dir.keys()):
            print(f"\n  {dirname}/ ({len(by_dir[dirname])} files)")
            for fname in sorted(by_dir[dirname])[:5]:
                print(f"    - {fname}")
            if len(by_dir[dirname]) > 5:
                print(f"    ... and {len(by_dir[dirname]) - 5} more")

        return

    # Step 4: Create structure and move
    print("\nStep 4: Preparing legacy folder structure...")
    create_legacy_structure(legacy_files)

    if dry_run:
        print("\n" + "=" * 60)
        print("DRY RUN - No files will be moved")
        print("Run with --execute to actually move files")
        print("=" * 60)
    else:
        print("\nStep 5: Moving files to legacy/...")

    moved, errors = move_files_to_legacy(legacy_files, dry_run=dry_run)

    if dry_run:
        print(f"\nWould move {len(moved)} files to verification/legacy/")
    else:
        print(f"\nMoved {len(moved)} files")
        if errors:
            print(f"Errors: {len(errors)}")
            for src, err in errors:
                print(f"  {src}: {err}")

    # Step 5: Generate manifest
    if not dry_run:
        print("\nStep 6: Generating manifest...")
        manifest = generate_manifest(legacy_files, len(moved))
        manifest_path = LEGACY_DIR / "LEGACY-MANIFEST.md"
        manifest_path.write_text(manifest)
        print(f"  Written to {manifest_path}")
    else:
        print("\nManifest preview (first 50 lines):")
        manifest = generate_manifest(legacy_files, len(legacy_files))
        for line in manifest.split('\n')[:50]:
            print(f"  {line}")
        print("  ...")

    print("\n" + "=" * 60)
    print("Audit complete!")
    if dry_run:
        print("Run with --execute to move files")
    print("=" * 60)


if __name__ == "__main__":
    main()
