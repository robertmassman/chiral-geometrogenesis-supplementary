#!/usr/bin/env python3
"""
AutoVerifier-CG: Autonomous Three-Layer Group Audit
=====================================================

Automates the three-layer audit protocol from THEMATIC-GROUPS.md Appendix E:
  Layer 1 — Coherence: Do the files agree with each other?
  Layer 2 — Validity: Are the files correct?
  Layer 3 — Adversarial: Can the files be broken?

This tool is READ-ONLY. It never modifies proof documents — only produces
audit reports in docs/proofs/reviews/<group>/.

Usage:
  python3 verification/autoverifier/autoverify_cg.py --group G2
  python3 verification/autoverifier/autoverify_cg.py --group G2 --layer 1
  python3 verification/autoverifier/autoverify_cg.py --group G2 --layer 2 --module V1
  python3 verification/autoverifier/autoverify_cg.py --group all
  python3 verification/autoverifier/autoverify_cg.py --list-groups
  python3 verification/autoverifier/autoverify_cg.py --dry-run --group G3
"""

import argparse
import concurrent.futures
import json
import logging
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from pathlib import Path
from typing import Optional

# ── Paths ─────────────────────────────────────────────────────
ROOT = Path(__file__).resolve().parent.parent.parent
AUTOVERIFIER_DIR = Path(__file__).resolve().parent
CONFIG_PATH = AUTOVERIFIER_DIR / "config.json"
PROGRAM_PATH = AUTOVERIFIER_DIR / "program.md"
RESULTS_PATH = AUTOVERIFIER_DIR / "results.tsv"
LOG_PATH = AUTOVERIFIER_DIR / "campaign.log"
THEMATIC_GROUPS_PATH = ROOT / "docs" / "proofs" / "THEMATIC-GROUPS.md"
REVIEWS_DIR = ROOT / "docs" / "proofs" / "reviews"


# ── Data Types ────────────────────────────────────────────────

# Group metadata extracted from THEMATIC-GROUPS.md
GROUP_METADATA = {
    "G1":  {"name": "Geometric Foundation",        "short": "Geometric-Foundation"},
    "G2":  {"name": "Gauge Theory & Confinement",  "short": "Gauge-Confinement"},
    "G3":  {"name": "Time & Entropy",              "short": "Time-Entropy"},
    "G4":  {"name": "Chirality & CP Violation",    "short": "Chirality-CP"},
    "G5":  {"name": "Mass Generation",             "short": "Mass-Generation"},
    "G6":  {"name": "QCD Scale Derivation",        "short": "QCD-Scale"},
    "G7":  {"name": "Quantum Foundations",          "short": "Quantum-Foundations"},
    "G8":  {"name": "Emergent Gravity",            "short": "Emergent-Gravity"},
    "G9":  {"name": "Electroweak Sector",          "short": "Electroweak-Sector"},
    "G10": {"name": "Renormalization & Yang-Mills", "short": "Renorm-YM"},
    "G11": {"name": "Bootstrap & Uniqueness",      "short": "Bootstrap-Uniqueness"},
    "G12": {"name": "Predictions & Falsifiability", "short": "Predictions-Falsifiability"},
}

# Module descriptions for prompting
COHERENCE_MODULES = {
    "M1":  "Geometric/Structural Identity — Core objects have consistent properties across all files",
    "M2":  "Primary Derivation Paths — Multiple paths to key results agree",
    "M3":  "External vs Internal Consistency — External inputs match internal re-derivations",
    "M4":  "Key Correspondence Structures — Claimed isomorphisms/mappings are consistent",
    "M5":  "Spatial/Extension Structures — Extended objects (lattices, manifolds) are consistent",
    "M6":  "Phase 0 / Foundational Objects — Base-layer definitions are consistent with their use",
    "M7":  "Notation and Convention Consistency — Symbols, markers, and conventions are uniform",
    "M8":  "Dependency Chain Verification — Theorem DAG is acyclic; all prereqs satisfied",
    "M9":  "Claims vs Evidence — Status markers match actual proof content",
    "M10": "Numerical Values — All shared numerical values are consistent across files",
}

VALIDITY_MODULES = {
    "V1": "Assumption Inventory — Identify and classify every assumption as (E)stablished, (F)ramework, or (H)ypothesis",
    "V2": "Derivation Step Verification — Check each load-bearing step against cited theorem's actual hypotheses",
    "V3": "Semantic Circularity Detection — Different proofs assuming the same thing under different names",
    "V4": "Alternative Explanations — Loopholes in uniqueness/necessity claims",
    "V5": "Domain-of-Validity Verification — Established results applied within their proven domain",
    "V6": "Selection vs Derivation Honesty — True logical character matches presentation",
    "V7": "Falsifiability & Empirical Contact — Which claims are predictions vs retrodictions",
    "V8": "Known Counterarguments & Literature — Published criticisms and alternative approaches addressed",
}

ADVERSARIAL_MODULES = {
    "A1": "Counterexample Construction — Build concrete counterexamples to key claims (EXISTENTIAL threat)",
    "A2": "Alternative Framework Construction — Build alternative theories satisfying same constraints (EXISTENTIAL)",
    "A3": "Independent Rederivation — Rederive key results from scratch to find hidden assumptions (STRUCTURAL)",
    "A4": "Assumption Removal Cascade — Remove each input one-at-a-time and map damage (STRUCTURAL)",
    "A5": "Boundary Stress-Testing — Perturb parameters, boundary conditions, limits (STRUCTURAL)",
    "A6": "Numerical Stress-Test — Verify numerical chains are identities, not coincidences (COSMETIC)",
}

# Group-specific adversarial focus from THEMATIC-GROUPS.md
GROUP_ADVERSARIAL_FOCUS = {
    "G2":  "A1: Build SU(2) gauge theory with same structure; A2: alternative gauge structures",
    "G3":  "A1: alternative time emergence mechanisms; A5: time parameter sensitivity",
    "G4":  "A1: alternative chirality selection; A2: different CP violation mechanisms",
    "G5":  "A1: build Nambu-Jona-Lasinio comparison; A6: fermion mass numerical chains",
    "G6":  "A6: dominant — all QCD parameters independently recomputed; A5: 10% R_stella variation",
    "G7":  "A1: alternative Born rule derivations; A4: which quantum principles are independent",
    "G8":  "A1: alternative gravity emergence (thermodynamic vs geometric); A2: compare with Verlinde/Jacobson",
    "G9":  "A1: alternative EW symmetry breaking; A6: Higgs mass, W/Z mass predictions",
    "G10": "A3: independent beta-function rederivation; A5: UV completion sensitivity",
    "G11": "A2: dominant — alternative bootstrap constructions; A4: self-consistency loop fragility",
    "G12": "A6: dominant — all numerical predictions stress-tested; A1: alternative explanations",
}


class ModuleResult(Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    NOTE = "NOTE"
    PENDING = "PENDING"
    ERROR = "ERROR"


@dataclass
class ModuleOutcome:
    """Result of running a single audit module."""
    group: str
    layer: int
    module_id: str
    result: ModuleResult
    checks_total: int = 0
    checks_passed: int = 0
    checks_failed: int = 0
    checks_noted: int = 0
    findings_summary: str = ""
    duration_seconds: float = 0
    report_file: str = ""


# ── Config & Logging ──────────────────────────────────────────

def load_config() -> dict:
    with open(CONFIG_PATH) as f:
        return json.load(f)


def load_program() -> str:
    with open(PROGRAM_PATH) as f:
        return f.read()


def setup_logging(config: dict) -> logging.Logger:
    logger = logging.getLogger("autoverify-cg")
    logger.setLevel(getattr(logging, config["logging"]["level"].upper()))

    fh = logging.FileHandler(LOG_PATH)
    fh.setLevel(logging.DEBUG)
    fh.setFormatter(logging.Formatter(
        "%(asctime)s [%(levelname)s] %(message)s", datefmt="%Y-%m-%d %H:%M:%S"
    ))
    logger.addHandler(fh)

    ch = logging.StreamHandler()
    ch.setLevel(logging.INFO)
    ch.setFormatter(logging.Formatter(
        "\033[90m%(asctime)s\033[0m %(message)s", datefmt="%H:%M:%S"
    ))
    logger.addHandler(ch)

    return logger


# ── Group Parsing ─────────────────────────────────────────────

def extract_group_section(group_id: str) -> str:
    """Extract the full section for a group from THEMATIC-GROUPS.md."""
    with open(THEMATIC_GROUPS_PATH) as f:
        content = f.read()

    meta = GROUP_METADATA.get(group_id)
    if not meta:
        return ""

    # Find the group header (## G1: Geometric Foundation)
    pattern = rf'^## {group_id}: .+$'
    match = re.search(pattern, content, re.MULTILINE)
    if not match:
        return ""

    start = match.start()

    # Find the next group header or end of file
    next_pattern = r'^## G\d+:'
    next_match = re.search(next_pattern, content[match.end():], re.MULTILINE)
    if next_match:
        end = match.end() + next_match.start()
    else:
        # Could be last group or hit appendix
        appendix = re.search(r'^## Appendix', content[match.end():], re.MULTILINE)
        end = match.end() + appendix.start() if appendix else len(content)

    return content[start:end].strip()


def extract_proof_files(group_section: str) -> list[dict]:
    """Extract proof file paths from a group section's table."""
    files = []
    # Match table rows with file links: | # | Phase | Number | Title | [path](link) |
    for match in re.finditer(
        r'\|\s*\d+\w?\s*\|\s*[\-\d]+\s*\|\s*(\S+\s+[\d.]+\S*)\s*\|\s*(.+?)\s*\|\s*\[.*?\]\((.*?)\)',
        group_section
    ):
        number = match.group(1).strip()
        title = match.group(2).strip()
        path = match.group(3).strip()
        # Clean relative path
        if path.startswith("foundations/") or path.startswith("Phase"):
            path = f"docs/proofs/{path}"
        # Remove anchor fragments
        path = path.split(")")[0]
        if not path.endswith(".md"):
            path += ".md"
        files.append({"number": number, "title": title, "path": path})
    return files


def extract_coherence_checklist(group_section: str) -> list[str]:
    """Extract the coherence checklist items from a group section."""
    items = []
    in_checklist = False
    for line in group_section.split('\n'):
        if 'Coherence checklist' in line:
            in_checklist = True
            continue
        if in_checklist:
            if line.strip().startswith('- ['):
                # Extract the check text
                check = re.sub(r'^- \[.\]\s*', '', line.strip())
                items.append(check)
            elif line.strip().startswith('---') or line.strip().startswith('##'):
                break
    return items


# ── Agent Invocation ──────────────────────────────────────────

def invoke_agent(prompt: str, config: dict, logger: logging.Logger,
                 timeout_minutes: float) -> tuple[str, bool]:
    """Invoke Claude Code CLI. Returns (output, success)."""
    cmd = [config["agent"]["command"]]
    if config["agent"].get("model"):
        cmd.extend(["--model", config["agent"]["model"]])
    for flag in config["agent"].get("flags", []):
        cmd.append(flag)
    cmd.extend(["--max-turns", str(config["agent"].get("max_turns", 75))])
    cmd.extend(["-p", prompt])

    timeout_seconds = int(timeout_minutes * 60)
    logger.debug(f"Invoking agent with timeout={timeout_minutes}min")

    try:
        result = subprocess.run(
            cmd, cwd=ROOT, capture_output=True, text=True,
            timeout=timeout_seconds
        )
        output = result.stdout + result.stderr
        return output, result.returncode == 0
    except subprocess.TimeoutExpired:
        logger.warning(f"Agent timed out after {timeout_minutes} minutes")
        return "TIMEOUT", False
    except FileNotFoundError:
        logger.error("Claude CLI not found")
        return "ERROR: claude CLI not found", False


def extract_json_from_output(output: str) -> Optional[dict]:
    """Extract the last JSON block from agent output."""
    json_blocks = re.findall(r'```json\s*\n(.*?)\n\s*```', output, re.DOTALL)
    if json_blocks:
        try:
            return json.loads(json_blocks[-1])
        except json.JSONDecodeError:
            pass
    # Try raw JSON at end
    lines = output.strip().split('\n')
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()
        if line.startswith('{'):
            depth = 0
            candidate = '\n'.join(lines[i:])
            for j, ch in enumerate(candidate):
                if ch == '{':
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0:
                        try:
                            return json.loads(candidate[:j + 1])
                        except json.JSONDecodeError:
                            break
            break
    return None


# ── Report File Naming ────────────────────────────────────────

def group_reviews_dir(group_id: str) -> Path:
    """Get the reviews subdirectory for a group, creating it if needed."""
    d = REVIEWS_DIR / group_id
    d.mkdir(parents=True, exist_ok=True)
    return d


def report_filename(group_id: str, layer: int, module_id: Optional[str] = None) -> str:
    """Generate report filename following established conventions."""
    meta = GROUP_METADATA[group_id]
    short = meta["short"]

    if layer == 1:
        if module_id:
            return f"{group_id}-{short}-Coherence-{module_id}-Findings.md"
        return f"{group_id}-{short}-Coherence-Audit.md"
    elif layer == 2:
        if module_id:
            return f"{group_id}-Validity-Audit-Module-{module_id}-Findings.md"
        return f"{group_id}-{short}-Validity-Audit.md"
    elif layer == 3:
        if module_id:
            return f"{group_id}-Adversarial-{module_id}-Findings.md"
        return f"{group_id}-Adversarial-Stress-Test-Findings.md"
    return f"{group_id}-{short}-Audit.md"


def report_path(group_id: str, layer: int, module_id: Optional[str] = None) -> str:
    """Full relative path for a report file (e.g., docs/proofs/reviews/G2/...)."""
    return f"docs/proofs/reviews/{group_id}/{report_filename(group_id, layer, module_id)}"


# ── Prompt Building ───────────────────────────────────────────

def build_coherence_prompt(group_id: str, module_id: str,
                           group_section: str, proof_files: list[dict],
                           checklist: list[str], program: str) -> str:
    """Build prompt for a coherence audit module."""
    meta = GROUP_METADATA[group_id]
    module_desc = COHERENCE_MODULES[module_id]

    files_table = "\n".join(
        f"  [{i+1}] {f['number']}: {f['title']} → {f['path']}"
        for i, f in enumerate(proof_files)
    )

    checklist_str = "\n".join(f"  - {c}" for c in checklist) if checklist else "  (none defined)"

    report_file = report_filename(group_id, 1, module_id)

    return f"""You are an autonomous audit agent performing a COHERENCE AUDIT on the Chiral Geometrogenesis framework.

## Audit Direction
{program}

## Task: Layer 1 (Coherence) — Module {module_id}
**Group:** {group_id} — {meta['name']}
**Module:** {module_id} — {module_desc}
**Posture:** DEFENSIVE — verify internal consistency

### Proof files in this group:
{files_table}

### Coherence checklist for {group_id}:
{checklist_str}

### Group context from THEMATIC-GROUPS.md:
{group_section[:3000]}

### Instructions:
1. Read EVERY proof file listed above (or at minimum, the ones relevant to {module_id})
2. For module {module_id}, systematically check the relevant consistency dimension
3. For each check, record PASS / FAIL / NOTE with specific evidence
4. Reference the G1 coherence audit as a template: docs/proofs/reviews/G1/G1-Geometric-Foundation-Coherence-Audit.md

### Output format:
Write your findings as a complete Markdown audit report. At the end, also output a JSON summary:

```json
{{
  "group": "{group_id}",
  "layer": 1,
  "module": "{module_id}",
  "checks_total": 0,
  "checks_passed": 0,
  "checks_failed": 0,
  "checks_noted": 0,
  "findings": [
    {{
      "check_id": "{module_id}.1",
      "result": "PASS|FAIL|NOTE",
      "description": "what was checked",
      "evidence": "specific file/section reference",
      "severity": "if FAIL: CRITICAL|MAJOR|MODERATE|MINOR"
    }}
  ],
  "overall_result": "PASS|FAIL"
}}
```

IMPORTANT:
- Write the full report to: {report_path(group_id, 1, module_id)}
- Be SPECIFIC — cite exact files, sections, values
- Do NOT modify any proof documents
- A FAIL means real inconsistency, not just a style preference"""


def build_validity_prompt(group_id: str, module_id: str,
                          group_section: str, proof_files: list[dict],
                          program: str) -> str:
    """Build prompt for a validity audit module."""
    meta = GROUP_METADATA[group_id]
    module_desc = VALIDITY_MODULES[module_id]

    files_table = "\n".join(
        f"  [{i+1}] {f['number']}: {f['title']} → {f['path']}"
        for i, f in enumerate(proof_files)
    )

    report_file = report_filename(group_id, 2, module_id)

    # Module-specific instructions
    module_instructions = {
        "V1": """For EACH proof file, inventory every assumption used. Classify each as:
- (E) Established: textbook physics, peer-reviewed, widely accepted
- (F) Framework-specific: a choice this framework makes that others might not
- (H) Physical hypothesis: a physical claim that could be tested/falsified
Flag any SMUGGLED assumptions (entering the proof without being declared).
Use V1.1-Assumption-Inventory-F01-Definition-0.0.0.md as a format template.""",

        "V2": """For each load-bearing derivation step in the group's proofs:
- Verify the step follows logically from its premises
- Check that cited theorems are used within their proven domain
- Verify dimensional consistency
- Flag any "it can be shown that..." gaps
Classify each step as SOUND / QUALIFIED / WEAK / INVALID.""",

        "V3": """Hunt for semantic circularity:
- Different proofs assuming the same thing under different names
- Concept X defined in proof A used as if independently derived in proof B
- "Different explanations" that are actually the same argument wearing different notation
This is the subtlest and most dangerous failure mode. Be thorough.""",

        "V4": """For each uniqueness or necessity claim:
- Attempt to construct an alternative that satisfies the same constraints
- Identify loopholes: could a different choice work?
- Distinguish true derivations from selections-presented-as-derivations""",

        "V5": """For each invocation of an established result:
- Verify the result is applied within its proven domain of validity
- Check that required conditions (convergence, smoothness, etc.) are met
- Flag any extrapolations beyond proven bounds""",

        "V6": """For each major result, determine its true logical character:
- DERIVATION: follows necessarily from premises (strongest)
- SELECTION: chosen from multiple viable options (honest if stated)
- CONSISTENCY CHECK: shown compatible but not derived (weakest)
Flag any result whose presentation overstates its logical character.""",

        "V7": """Assess falsifiability and empirical contact:
- Which claims are genuine predictions vs retrodictions?
- What experimental result would falsify this group's conclusions?
- Are there concrete, measurable signatures?""",

        "V8": """Survey known counterarguments and alternatives:
- Are published criticisms of similar approaches addressed?
- Are alternative frameworks (that claim similar results) compared?
- Are known difficulties honestly acknowledged?""",
    }

    specific = module_instructions.get(module_id, "Execute this module per the standard protocol.")

    return f"""You are an autonomous audit agent performing a VALIDITY AUDIT on the Chiral Geometrogenesis framework.

## Audit Direction
{program}

## Task: Layer 2 (Validity) — Module {module_id}
**Group:** {group_id} — {meta['name']}
**Module:** {module_id} — {module_desc}
**Posture:** DEFENSIVE — verify external correctness

### Proof files in this group:
{files_table}

### Module-specific instructions:
{specific}

### Reference templates:
- G1 validity findings: docs/proofs/reviews/G1/G1-Validity-Audit-Module-V1-Findings.md
- G1 validity audit plan: docs/proofs/reviews/G1/G1-Geometric-Foundation-Validity-Audit.md

### Output format:
Write your findings as a complete Markdown audit report following the G1 template format.
At the end, output a JSON summary:

```json
{{
  "group": "{group_id}",
  "layer": 2,
  "module": "{module_id}",
  "checks_total": 0,
  "sound": 0,
  "qualified": 0,
  "weak": 0,
  "invalid": 0,
  "smuggled": 0,
  "findings": [
    {{
      "check_id": "{module_id}.1",
      "result": "SOUND|QUALIFIED|WEAK|INVALID|SMUGGLED",
      "description": "what was checked",
      "evidence": "specific file/section reference",
      "severity": "CRITICAL|MAJOR|MODERATE|MINOR|NOTE"
    }}
  ],
  "overall_verdict": "summary"
}}
```

IMPORTANT:
- Write the full report to: {report_path(group_id, 2, module_id)}
- Classify EVERY finding — no unclassified results
- SMUGGLED means an undeclared assumption — this is a specific finding category
- Do NOT modify any proof documents"""


def build_adversarial_prompt(group_id: str, module_id: str,
                             group_section: str, proof_files: list[dict],
                             program: str) -> str:
    """Build prompt for an adversarial audit module."""
    meta = GROUP_METADATA[group_id]
    module_desc = ADVERSARIAL_MODULES[module_id]
    group_focus = GROUP_ADVERSARIAL_FOCUS.get(group_id, "No specific focus guidance.")

    files_table = "\n".join(
        f"  [{i+1}] {f['number']}: {f['title']} → {f['path']}"
        for i, f in enumerate(proof_files)
    )

    report_file = report_filename(group_id, 3, module_id)

    module_instructions = {
        "A1": """COUNTEREXAMPLE CONSTRUCTION (EXISTENTIAL threat)
For each key claim or uniqueness assertion:
- Attempt to build a concrete counterexample
- If the claim is "X is the only Y satisfying Z", construct an alternative Y' satisfying Z
- If no counterexample exists, explain why (this strengthens the claim)
- Document each attempt with: Claim → Attack → Outcome""",

        "A2": """ALTERNATIVE FRAMEWORK CONSTRUCTION (EXISTENTIAL threat)
Build an alternative theory that:
- Satisfies the same physical requirements as this group
- Uses different mathematical structures
- Produces comparable (or better) results
If you CANNOT build a viable alternative, explain what prevents it.
If you CAN, assess whether it's truly competitive or has fatal flaws.""",

        "A3": """INDEPENDENT REDERIVATION (STRUCTURAL)
Choose the 3 most important results in this group and:
- Rederive each from scratch without looking at the existing proof
- Compare your derivation to the original
- Any discrepancy reveals a hidden assumption or error
- Flag any step where your rederivation required an assumption the original omitted""",

        "A4": """ASSUMPTION REMOVAL CASCADE (STRUCTURAL)
For each independent input/assumption in this group:
- Remove it and trace the damage cascade
- Map: DIRECT DAMAGE → TRANSITIVE DAMAGE → SURVIVORS
- Assess REPAIRABILITY (can the assumption be replaced?)
- Compute DEPENDENCY DEPTH (how far does the damage reach?)
Use the G1 format: docs/proofs/reviews/G1/G1-Adversarial-Stress-Test-Findings.md""",

        "A5": """BOUNDARY STRESS-TESTING (STRUCTURAL)
Perturb key parameters by ±10% and check:
- Do conclusions change qualitatively?
- Are there phase transitions or discontinuities?
- Is the framework fine-tuned (small perturbation → large effect)?
Also test boundary/limiting cases — what happens at extreme values?""",

        "A6": """NUMERICAL STRESS-TEST (COSMETIC)
For every numerical chain in this group:
- Recompute each number independently from stated inputs
- Verify that agreements are genuine identities, not numerical coincidences
- Check: if you vary the input by 1σ, does the output stay within bounds?
- Flag any suspicious numerical near-agreements that lack theoretical explanation""",
    }

    specific = module_instructions.get(module_id, "Execute this module per the adversarial protocol.")

    return f"""You are an autonomous ADVERSARIAL audit agent stress-testing the Chiral Geometrogenesis framework.

## Audit Direction
{program}

## Task: Layer 3 (Adversarial) — Module {module_id}
**Group:** {group_id} — {meta['name']}
**Module:** {module_id} — {module_desc}
**Posture:** OFFENSIVE — try to BREAK the framework's conclusions

### Group-specific adversarial focus:
{group_focus}

### Proof files in this group:
{files_table}

### Module-specific instructions:
{specific}

### Reference template:
- G1 adversarial findings: docs/proofs/reviews/G1/G1-Adversarial-Stress-Test-Findings.md

### Output format:
Write your findings as a complete Markdown report. At the end, output JSON:

```json
{{
  "group": "{group_id}",
  "layer": 3,
  "module": "{module_id}",
  "attacks_total": 0,
  "survived": 0,
  "dented": 0,
  "cracked": 0,
  "broken": 0,
  "findings": [
    {{
      "attack_id": "{module_id}.1",
      "target": "what was attacked",
      "attack": "how it was attacked",
      "result": "SURVIVED|DENTED|CRACKED|BROKEN",
      "evidence": "specific details",
      "repairability": "HIGH|MODERATE|LOW|NONE"
    }}
  ],
  "resilience_score": 0.0
}}
```

IMPORTANT:
- Write the full report to: {report_path(group_id, 3, module_id)}
- Be GENUINELY adversarial — your job is to find weaknesses
- SURVIVED means the attack genuinely failed, not that you gave up
- BROKEN means the conclusion is compromised — use this carefully but honestly
- Do NOT modify any proof documents"""


# ── Layer Execution ───────────────────────────────────────────

def run_module(group_id: str, layer: int, module_id: str,
               group_section: str, proof_files: list[dict],
               checklist: list[str], config: dict, program: str,
               logger: logging.Logger, dry_run: bool = False) -> ModuleOutcome:
    """Run a single audit module."""
    start_time = time.time()

    layer_names = {1: "Coherence", 2: "Validity", 3: "Adversarial"}
    logger.info(f"  [{layer_names[layer]}] Running {module_id}...")

    outcome = ModuleOutcome(
        group=group_id, layer=layer, module_id=module_id,
        result=ModuleResult.PENDING
    )

    if dry_run:
        outcome.result = ModuleResult.PASS
        outcome.findings_summary = "Dry run"
        outcome.duration_seconds = 0
        logger.info(f"    [DRY RUN] Would execute {module_id}")
        return outcome

    # Build the appropriate prompt
    if layer == 1:
        prompt = build_coherence_prompt(
            group_id, module_id, group_section, proof_files, checklist, program
        )
    elif layer == 2:
        prompt = build_validity_prompt(
            group_id, module_id, group_section, proof_files, program
        )
    elif layer == 3:
        prompt = build_adversarial_prompt(
            group_id, module_id, group_section, proof_files, program
        )
    else:
        outcome.result = ModuleResult.ERROR
        return outcome

    # Invoke the agent
    timeout = config["time_budgets"]["per_module_minutes"]
    output, success = invoke_agent(prompt, config, logger, timeout)

    # Parse results — try stdout first, then fall back to reading the report file
    result_json = extract_json_from_output(output)

    if not result_json:
        # Agent writes report via Write tool; JSON summary is in the file, not stdout
        rpt_file = group_reviews_dir(group_id) / report_filename(group_id, layer, module_id)
        if rpt_file.exists():
            try:
                rpt_text = rpt_file.read_text()
                result_json = extract_json_from_output(rpt_text)
                if result_json:
                    logger.debug(f"    Parsed JSON from report file: {rpt_file.name}")
            except Exception:
                pass

    if result_json:
        if layer == 1:
            outcome.checks_total = result_json.get("checks_total", 0)
            outcome.checks_passed = result_json.get("checks_passed", 0)
            outcome.checks_failed = result_json.get("checks_failed", 0)
            outcome.checks_noted = result_json.get("checks_noted", 0)
            overall = result_json.get("overall_result", "PENDING")
            outcome.result = ModuleResult.PASS if overall == "PASS" else ModuleResult.FAIL

        elif layer == 2:
            outcome.checks_total = result_json.get("checks_total", 0)
            outcome.checks_passed = result_json.get("sound", 0) + result_json.get("qualified", 0)
            outcome.checks_failed = result_json.get("weak", 0) + result_json.get("invalid", 0)
            outcome.checks_noted = result_json.get("smuggled", 0)
            has_invalid = result_json.get("invalid", 0) > 0
            outcome.result = ModuleResult.FAIL if has_invalid else ModuleResult.PASS

        elif layer == 3:
            outcome.checks_total = result_json.get("attacks_total", 0)
            outcome.checks_passed = result_json.get("survived", 0)
            dented = result_json.get("dented", 0)
            cracked = result_json.get("cracked", 0)
            broken = result_json.get("broken", 0)
            outcome.checks_failed = cracked + broken
            outcome.checks_noted = dented
            outcome.result = ModuleResult.FAIL if broken > 0 else ModuleResult.PASS
            outcome.findings_summary = (
                f"Resilience: {result_json.get('resilience_score', 'N/A')}% "
                f"({outcome.checks_passed}S {dented}D {cracked}C {broken}B)"
            )

        if not outcome.findings_summary:
            outcome.findings_summary = (
                f"{outcome.checks_passed}/{outcome.checks_total} passed, "
                f"{outcome.checks_failed} failed, {outcome.checks_noted} noted"
            )
    else:
        outcome.result = ModuleResult.ERROR if not success else ModuleResult.PASS
        outcome.findings_summary = "Could not parse structured results"

    # Record report file
    outcome.report_file = report_filename(group_id, layer, module_id)
    outcome.duration_seconds = time.time() - start_time

    status_icon = {
        ModuleResult.PASS: "+++",
        ModuleResult.FAIL: "---",
        ModuleResult.NOTE: " ! ",
        ModuleResult.PENDING: " ? ",
        ModuleResult.ERROR: "ERR",
    }

    logger.info(
        f"    [{status_icon[outcome.result]}] {module_id}: {outcome.findings_summary} "
        f"({outcome.duration_seconds:.0f}s)"
    )

    return outcome


def run_layer(group_id: str, layer: int, config: dict, program: str,
              logger: logging.Logger, specific_module: Optional[str] = None,
              dry_run: bool = False) -> list[ModuleOutcome]:
    """Run all modules in a layer for a group."""
    meta = GROUP_METADATA[group_id]
    layer_names = {1: "Coherence", 2: "Validity", 3: "Adversarial"}

    logger.info(f"Layer {layer} ({layer_names[layer]}) — {group_id}: {meta['name']}")
    logger.info("-" * 50)

    # Extract group info
    group_section = extract_group_section(group_id)
    proof_files = extract_proof_files(group_section)
    checklist = extract_coherence_checklist(group_section)

    if not proof_files:
        logger.warning(f"  No proof files extracted for {group_id}")

    logger.info(f"  {len(proof_files)} proof files, {len(checklist)} checklist items")

    # Determine modules to run
    if layer == 1:
        modules_map = COHERENCE_MODULES
        module_order = config["layers"]["coherence"]["modules"]
    elif layer == 2:
        modules_map = VALIDITY_MODULES
        module_order = config["layers"]["validity"]["execution_order"]
    elif layer == 3:
        modules_map = ADVERSARIAL_MODULES
        # Flatten phase execution order
        phases = config["layers"]["adversarial"]["execution_phases"]
        module_order = []
        for phase_modules in phases.values():
            module_order.extend(phase_modules)
    else:
        return []

    if specific_module:
        if specific_module in modules_map:
            module_order = [specific_module]
        else:
            logger.warning(f"Module {specific_module} not valid for layer {layer}")
            return []

    # Run modules — parallel for Layer 1 & 2, phased for Layer 3
    outcomes = []

    if layer == 3:
        # Layer 3: run in phases with gates between them
        phases = config["layers"]["adversarial"]["execution_phases"]
        halt = False
        for phase_name, phase_modules in phases.items():
            if halt:
                break
            phase_order = [m for m in phase_modules if m in module_order]
            if not phase_order:
                continue

            logger.info(f"  Adversarial {phase_name} — {len(phase_order)} modules in parallel")
            with concurrent.futures.ThreadPoolExecutor(max_workers=len(phase_order)) as pool:
                futures = {
                    pool.submit(
                        run_module, group_id, layer, mid, group_section,
                        proof_files, checklist, config, program, logger, dry_run
                    ): mid for mid in phase_order
                }
                for future in concurrent.futures.as_completed(futures):
                    outcome = future.result()
                    outcomes.append(outcome)
                    if (config["layers"]["adversarial"]["halt_on_broken"]
                            and outcome.result == ModuleResult.FAIL
                            and outcome.checks_failed > 0):
                        logger.warning(
                            f"  HALT: {outcome.module_id} found BROKEN results "
                            f"— stopping adversarial audit"
                        )
                        halt = True
    else:
        # Layer 1 & 2: run all modules in parallel
        max_workers = config.get("_max_parallel", 0) or len(module_order)
        logger.info(f"  Launching {len(module_order)} modules ({max_workers} parallel)")
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as pool:
            futures = {
                pool.submit(
                    run_module, group_id, layer, mid, group_section,
                    proof_files, checklist, config, program, logger, dry_run
                ): mid for mid in module_order
            }
            for future in concurrent.futures.as_completed(futures):
                outcomes.append(future.result())

        # Sort outcomes back to module order for consistent reporting
        order_map = {mid: i for i, mid in enumerate(module_order)}
        outcomes.sort(key=lambda o: order_map.get(o.module_id, 999))

    return outcomes


# ── Results Logging ───────────────────────────────────────────

def init_results_file():
    if not RESULTS_PATH.exists():
        with open(RESULTS_PATH, "w") as f:
            f.write("\t".join([
                "timestamp", "group", "layer", "module",
                "result", "checks_total", "checks_passed",
                "checks_failed", "checks_noted",
                "duration_s", "report_file", "summary"
            ]) + "\n")


def log_outcomes(outcomes: list[ModuleOutcome]):
    with open(RESULTS_PATH, "a") as f:
        for o in outcomes:
            f.write("\t".join([
                datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                o.group,
                str(o.layer),
                o.module_id,
                o.result.value,
                str(o.checks_total),
                str(o.checks_passed),
                str(o.checks_failed),
                str(o.checks_noted),
                f"{o.duration_seconds:.1f}",
                o.report_file,
                o.findings_summary.replace("\t", " ").replace("\n", " ")[:200]
            ]) + "\n")


# ── Synthesis Report ──────────────────────────────────────────

def generate_synthesis(group_id: str, all_outcomes: list[ModuleOutcome],
                       logger: logging.Logger):
    """Generate a synthesis report summarizing all layers."""
    meta = GROUP_METADATA[group_id]

    layer_1 = [o for o in all_outcomes if o.layer == 1]
    layer_2 = [o for o in all_outcomes if o.layer == 2]
    layer_3 = [o for o in all_outcomes if o.layer == 3]

    def layer_summary(outcomes):
        if not outcomes:
            return "Not run"
        total = sum(o.checks_total for o in outcomes)
        passed = sum(o.checks_passed for o in outcomes)
        failed = sum(o.checks_failed for o in outcomes)
        return f"{passed}/{total} passed, {failed} failed"

    # Compute adversarial resilience
    adv_total = sum(o.checks_total for o in layer_3)
    adv_survived = sum(o.checks_passed for o in layer_3)
    adv_dented = sum(o.checks_noted for o in layer_3)
    if adv_total > 0:
        resilience = (adv_survived * 3 + adv_dented * 1) / (adv_total * 3) * 100
        resilience_str = f"{resilience:.0f}%"
    else:
        resilience_str = "N/A"

    report = f"""# {group_id} {meta['name']} — Audit Synthesis

> **Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M')}
> **Tool:** AutoVerifier-CG

---

## Summary

| Layer | Result | Details |
|-------|--------|---------|
| **Layer 1 (Coherence)** | {layer_summary(layer_1)} | {', '.join(o.module_id + ':' + o.result.value for o in layer_1)} |
| **Layer 2 (Validity)** | {layer_summary(layer_2)} | {', '.join(o.module_id + ':' + o.result.value for o in layer_2)} |
| **Layer 3 (Adversarial)** | Resilience: {resilience_str} | {', '.join(o.module_id + ':' + o.result.value for o in layer_3)} |

## Module Details

"""

    for o in all_outcomes:
        layer_name = {1: "Coherence", 2: "Validity", 3: "Adversarial"}[o.layer]
        report += f"### {o.module_id} ({layer_name})\n"
        report += f"- **Result:** {o.result.value}\n"
        report += f"- **Checks:** {o.checks_passed}/{o.checks_total} passed"
        if o.checks_failed:
            report += f", **{o.checks_failed} failed**"
        if o.checks_noted:
            report += f", {o.checks_noted} noted"
        report += "\n"
        report += f"- **Summary:** {o.findings_summary}\n"
        if o.report_file:
            report += f"- **Report:** [{o.report_file}]({o.report_file})\n"
        report += f"- **Duration:** {o.duration_seconds:.0f}s\n\n"

    # Write synthesis
    synthesis_file = group_reviews_dir(group_id) / f"{group_id}-{meta['short']}-Audit-Synthesis.md"
    with open(synthesis_file, "w") as f:
        f.write(report)

    logger.info(f"Synthesis written to {synthesis_file.relative_to(ROOT)}")


# ── Main ──────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="AutoVerifier-CG: Autonomous three-layer group audit"
    )
    parser.add_argument("--group", type=str, required=False,
                        help="Group to audit (G1-G12 or 'all')")
    parser.add_argument("--layer", type=int, choices=[1, 2, 3],
                        help="Run only this layer (1=Coherence, 2=Validity, 3=Adversarial)")
    parser.add_argument("--module", type=str,
                        help="Run only this module (e.g., M1, V3, A4)")
    parser.add_argument("--list-groups", action="store_true",
                        help="List all groups and exit")
    parser.add_argument("--max-parallel", type=int, default=0,
                        help="Max parallel agent sessions (0 = all modules at once)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be done without running agents")
    args = parser.parse_args()

    config = load_config()

    # Apply max-parallel override
    if args.max_parallel > 0:
        config["_max_parallel"] = args.max_parallel
    program = load_program()
    logger = setup_logging(config)
    init_results_file()

    if args.list_groups:
        print(f"\n{'Group':<8} {'Name':<35} {'Status'}")
        print("-" * 65)
        for gid, meta in GROUP_METADATA.items():
            # Check for existing audit files
            gdir = REVIEWS_DIR / gid
            existing = list(gdir.glob("*.md")) if gdir.exists() else []
            status = f"{len(existing)} audit files" if existing else "Not started"
            print(f"{gid:<8} {meta['name']:<35} {status}")
        return

    if not args.group:
        parser.print_help()
        return

    # Determine which groups to audit
    if args.group.lower() == "all":
        groups = list(GROUP_METADATA.keys())
    else:
        groups = [args.group.upper()]
        if groups[0] not in GROUP_METADATA:
            logger.error(f"Unknown group: {groups[0]}. Use --list-groups to see options.")
            return

    logger.info("=" * 60)
    logger.info("  AutoVerifier-CG: Three-Layer Group Audit")
    logger.info(f"  Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    logger.info(f"  Groups: {', '.join(groups)}")
    if args.layer:
        logger.info(f"  Layer: {args.layer}")
    if args.module:
        logger.info(f"  Module: {args.module}")
    logger.info("=" * 60)

    # Determine layers to run
    if args.layer:
        layers = [args.layer]
    else:
        layers = []
        if config["layers"]["coherence"]["enabled"]:
            layers.append(1)
        if config["layers"]["validity"]["enabled"]:
            layers.append(2)
        if config["layers"]["adversarial"]["enabled"]:
            layers.append(3)

    # Campaign deadline
    campaign_hours = config["time_budgets"]["campaign_hours"]
    deadline = (
        datetime.now() + timedelta(hours=campaign_hours)
        if campaign_hours > 0 else None
    )

    # Run audits
    for group_id in groups:
        logger.info(f"\n{'=' * 60}")
        logger.info(f"AUDITING: {group_id} — {GROUP_METADATA[group_id]['name']}")
        logger.info(f"{'=' * 60}")

        all_outcomes = []

        for layer in layers:
            if deadline and datetime.now() >= deadline:
                logger.info("Campaign time budget exhausted")
                break

            outcomes = run_layer(
                group_id, layer, config, program, logger,
                specific_module=args.module, dry_run=args.dry_run
            )
            all_outcomes.extend(outcomes)
            log_outcomes(outcomes)

            # Layer gate: don't proceed if coherence fails
            if layer == 1:
                failures = [o for o in outcomes if o.result == ModuleResult.FAIL]
                if failures and not args.dry_run:
                    logger.warning(
                        f"  Layer 1 has {len(failures)} FAIL(s) — "
                        f"resolve before proceeding to Layer 2"
                    )
                    if 2 in layers or 3 in layers:
                        logger.warning("  Skipping subsequent layers")
                        break

        # Generate synthesis report
        if all_outcomes and not args.dry_run:
            generate_synthesis(group_id, all_outcomes, logger)

    # Campaign summary
    logger.info(f"\n{'=' * 60}")
    logger.info("  CAMPAIGN COMPLETE")
    logger.info(f"  Results: {RESULTS_PATH}")
    logger.info(f"  Reports: {REVIEWS_DIR}")
    logger.info(f"{'=' * 60}")


if __name__ == "__main__":
    main()
