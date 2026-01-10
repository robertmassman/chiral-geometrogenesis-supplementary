# CLAUDE.md - Computational Verification Guide

This file provides guidance to Claude when working on computational verification scripts for Chiral Geometrogenesis.

## Purpose

The `verification/` directory contains Python scripts that numerically verify the mathematical claims in the proof documents. These serve as an independent check complementing the Lean 4 formalization.

**Primary Objectives:**
1. Verify numerical predictions against PDG (Particle Data Group) values
2. Check dimensional consistency across all equations
3. Test limiting cases and boundary conditions
4. Perform adversarial analysis to find potential weaknesses
5. Generate verification reports for peer review

---

## Directory Structure

```
verification/
├── foundations/           # Phase -1: 0.0.x theorem verification
│   ├── theorem_0_0_0_verification.py
│   ├── theorem_0_0_1_verification.py
│   ├── theorem_0_0_2_verification.py
│   ├── theorem_0_0_3_*.py           # Multiple verification aspects
│   ├── theorem_0_0_4_*.py
│   ├── theorem_0_0_5_*.py
│   ├── theorem_0_0_6_*.py
│   ├── theorem_0_0_8_*.py
│   └── *_results.json               # JSON output files
├── Phase0/                # 0.1.x - 0.3.x verification
├── Phase1/                # 1.x.x verification
├── Phase2/                # 2.x.x verification
├── Phase3/                # 3.x.x verification (mass generation)
│   ├── theorem_3_1_1_verification.py  # Phase-gradient mass generation
│   ├── theorem_3_2_1_verification.py  # Low-energy equivalence
│   └── corollary_3_1_3_*.py           # Neutrino predictions
├── Phase4/                # 4.x.x verification (solitons)
├── Phase5/                # 5.x.x verification (gravity)
│   ├── theorem_5_2_0_*.py             # Wick rotation
│   ├── theorem_5_2_1_*.py             # Emergent metric
│   └── theorem_5_2_4_*.py             # Newton's constant
├── Phase7/                # 7.x.x verification (consistency)
├── Phase8/                # 8.x.x verification (predictions)
├── shared/                # Cross-cutting utilities and reports
│   ├── chiral_geometrogenesis_verification.py  # Master verification
│   ├── theorem_analyzer.py            # Dependency analysis
│   ├── theorem_graph.py               # Dependency graph tools
│   ├── theorem_graph_data.json        # Graph data
│   ├── *_Verification-Report.md       # Multi-agent reports
│   └── *_verification_results.json    # Aggregated results
├── plots/                 # Generated visualization plots
│   ├── *.png              # Plot images
│   └── verification_checklist.md
├── CLAUDE.md              # This file
└── README.md              # Directory overview
```

### Corresponding Directories

| Verification Directory | Proof Documents | Lean Formalization |
|------------------------|-----------------|-------------------|
| `foundations/` | `docs/proofs/foundations/` | `lean/ChiralGeometrogenesis/Foundations/` |
| `Phase0/` | `docs/proofs/Phase0/` | `lean/ChiralGeometrogenesis/Phase0/` |
| `Phase3/` | `docs/proofs/Phase3/` | `lean/ChiralGeometrogenesis/Phase3/` |
| `Phase5/` | `docs/proofs/Phase5/` | `lean/ChiralGeometrogenesis/Phase5/` |

---

## File Naming Convention

### Python Scripts
```
theorem_X_X_X_verification.py      # Main verification
theorem_X_X_X_issue_resolution.py  # Issue fixes
theorem_X_X_X_adversarial_*.py     # Adversarial testing
theorem_X_X_X_strengthening.py     # Proof strengthening
definition_X_X_X_verification.py   # Definition verification
corollary_X_X_X_verification.py    # Corollary verification
```

### JSON Results
```
theorem_X_X_X_results.json              # Standard results
theorem_X_X_X_verification_results.json # Detailed results
theorem_X_X_X_issue_resolution_results.json
```

### Markdown Reports
```
Theorem-X.X.X-Verification-Report.md
Theorem-X.X.X-Multi-Agent-Verification-Report.md
Theorem-X.X.X-Adversarial-Physics-Verification.md
Theorem-X.X.X-EXECUTIVE-SUMMARY.md
```

---

## Verification Script Structure

Every verification script should follow this structure:

```python
#!/usr/bin/env python3
"""
Theorem X.X.X: [Title] Verification
====================================

Verifies [brief description].

Related Documents:
- Proof: docs/proofs/PhaseN/Theorem-X.X.X-*.md
- Lean: lean/ChiralGeometrogenesis/PhaseN/Theorem_X_X_X.lean

Verification Date: YYYY-MM-DD
"""

import numpy as np
from scipy import constants
import json
from datetime import datetime

# ==============================================================================
# PHYSICAL CONSTANTS (CODATA 2018 / PDG 2024)
# ==============================================================================

# Always use scipy.constants where available
HBAR = constants.hbar  # 1.054571817e-34 J·s
C = constants.c        # 299792458 m/s
G_NEWTON = constants.G # 6.67430e-11 m³/(kg·s²)

# PDG 2024 values
HIGGS_VEV_GEV = 246.22          # GeV
F_PI_GEV = 0.0921               # 92.1 MeV pion decay constant
M_PLANCK_GEV = 1.220890e19      # GeV

# ==============================================================================
# VERIFICATION FUNCTIONS
# ==============================================================================

def verify_claim_1():
    """Verify specific claim with dimensional analysis."""
    results = {
        "claim": "Description of claim",
        "expected": value_expected,
        "computed": value_computed,
        "relative_error": abs(value_computed - value_expected) / value_expected,
        "passed": relative_error < tolerance,
        "notes": "Any relevant notes"
    }
    return results

# ==============================================================================
# DIMENSIONAL ANALYSIS
# ==============================================================================

def check_dimensions():
    """Verify all equations have consistent dimensions."""
    # [mass] = GeV/c²
    # [length] = GeV⁻¹ (in natural units)
    # [time] = GeV⁻¹ (in natural units)
    pass

# ==============================================================================
# LIMITING CASES
# ==============================================================================

def verify_limiting_cases():
    """Check that known physics is recovered in appropriate limits."""
    # Low energy: should match Standard Model
    # Weak field: should match Newtonian gravity
    # Classical: should match classical mechanics
    pass

# ==============================================================================
# MAIN EXECUTION
# ==============================================================================

def main():
    results = {
        "theorem": "X.X.X",
        "title": "[Title]",
        "timestamp": datetime.now().isoformat(),
        "verifications": []
    }

    # Run all verifications
    results["verifications"].append(verify_claim_1())
    results["verifications"].append(check_dimensions())
    results["verifications"].append(verify_limiting_cases())

    # Summary
    all_passed = all(v.get("passed", True) for v in results["verifications"])
    results["overall_status"] = "PASSED" if all_passed else "FAILED"

    # Save results
    with open("theorem_X_X_X_results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    # Print summary
    print(f"Theorem X.X.X Verification: {results['overall_status']}")
    return results

if __name__ == "__main__":
    main()
```

---

## Verification Checklist

Before marking a verification complete:

### Numerical Accuracy
- [ ] All constants use PDG 2024 / CODATA 2018 values
- [ ] Relative errors calculated and within tolerance
- [ ] Uncertainties propagated correctly
- [ ] Natural units (ℏ = c = 1) used consistently

### Dimensional Analysis
- [ ] Every equation checked for dimensional consistency
- [ ] Unit conversions verified (GeV ↔ kg, etc.)
- [ ] Planck units handled correctly

### Limiting Cases
- [ ] Low-energy limit → Standard Model
- [ ] Weak-field limit → Newtonian gravity
- [ ] Classical limit (ℏ → 0) checked
- [ ] Non-relativistic limit (v << c) checked

### Consistency Checks
- [ ] Cross-verified with other theorems
- [ ] No contradictions with established physics
- [ ] Gauge invariance preserved
- [ ] Unitarity maintained

### Documentation
- [ ] Docstring describes purpose
- [ ] References to proof documents included
- [ ] Results saved to JSON
- [ ] Summary printed to stdout

---

## Key Physical Constants

Use these standard values throughout:

```python
# Fundamental (CODATA 2018)
HBAR = 1.054571817e-34      # J·s
C = 299792458               # m/s
G_NEWTON = 6.67430e-11      # m³/(kg·s²)

# Particle Physics (PDG 2024)
HIGGS_VEV_GEV = 246.22      # GeV
HIGGS_MASS_GEV = 125.11     # GeV ± 0.11
F_PI_GEV = 0.0921           # 92.1 MeV pion decay constant
PROTON_MASS_GEV = 0.938272  # GeV
ALPHA_QED = 1/137.036       # Fine structure constant

# Planck Scale
M_PLANCK_GEV = 1.220890e19  # GeV
L_PLANCK_M = 1.616255e-35   # m

# Conversions
GEV_TO_KG = 1.78266192e-27  # 1 GeV/c² in kg
GEV_TO_JOULE = 1.602176634e-10
```

---

## Adversarial Verification Protocol

For critical theorems, spawn adversarial verification:

```python
"""
ADVERSARIAL VERIFICATION PROTOCOL

You are an independent verification agent. Your role is ADVERSARIAL.
Your job is to find errors, gaps, and inconsistencies.

CHECKLIST:
1. LOGICAL VALIDITY - Does each step follow? Hidden assumptions?
2. MATHEMATICAL CORRECTNESS - Re-derive key equations independently
3. DIMENSIONAL ANALYSIS - Consistent units throughout?
4. LIMITING CASES - Reduces to known physics appropriately?
5. PHYSICAL REASONABLENESS - No pathologies?
6. NUMERICAL ACCURACY - Within experimental bounds?

OUTPUT:
- VERIFIED: [Yes/No/Partial]
- ERRORS FOUND: [List with locations]
- WARNINGS: [Potential issues]
- CONFIDENCE: [High/Medium/Low]
"""
```

---

## Common Patterns

### Loading Previous Results
```python
import json

def load_previous_results(theorem_id):
    """Load results from a previous verification."""
    filename = f"theorem_{theorem_id.replace('.', '_')}_results.json"
    with open(filename, 'r') as f:
        return json.load(f)
```

### Cross-Theorem Verification
```python
def verify_consistency_with(other_theorem_id):
    """Check that results are consistent with another theorem."""
    other_results = load_previous_results(other_theorem_id)
    # Compare relevant values
    pass
```

### Plotting Results
```python
import matplotlib.pyplot as plt

def plot_verification_results(results, output_path):
    """Generate verification plots."""
    # Save to verification/plots/
    plt.savefig(f"../plots/{output_path}")
```

---

## Running Verification

```bash
# Single script
python verification/Phase3/theorem_3_1_1_verification.py

# All scripts in a phase
for f in verification/Phase3/*.py; do python "$f"; done

# Master verification
python verification/shared/chiral_geometrogenesis_verification.py
```

---

## Related Resources

- **Proof Documents:** [../docs/proofs/](../docs/proofs/)
- **Lean Formalization:** [../lean/ChiralGeometrogenesis/](../lean/ChiralGeometrogenesis/)
- **Master Plan:** [../docs/Mathematical-Proof-Plan.md](../docs/Mathematical-Proof-Plan.md)
- **Physical Constants:** [../docs/proofs/reference/Physical-Constants-and-Data.md](../docs/proofs/reference/Physical-Constants-and-Data.md)

---

*Last Updated: 2025-12-30*
*Status: Active Development*
