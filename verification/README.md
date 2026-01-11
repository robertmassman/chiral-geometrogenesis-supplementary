# Verification Scripts

This directory contains computational verification scripts for the Chiral Geometrogenesis proofs.

## Directory Structure

| Phase | Description | Files |
|-------|-------------|-------|
| [foundations/](foundations/) | Pre-geometric foundations verification | 82 |
| [Phase0/](Phase0/) | Foundational definitions verification | 22 |
| [Phase1/](Phase1/) | SU(3) geometry verification | 2 |
| [Phase2/](Phase2/) | Pressure-depression verification | 53 |
| [Phase3/](Phase3/) | Mass generation verification | 107 |
| [Phase4/](Phase4/) | Solitons and matter verification | 60 |
| [Phase5/](Phase5/) | Emergent gravity verification | 232 |
| [Phase7/](Phase7/) | Consistency checks verification | 4 |
| [Phase8/](Phase8/) | Predictions verification | 53 |
| [shared/](shared/) | Cross-cutting verification and utilities | 325 |
| [plots/](plots/) | Generated visualization plots | 243 |

## File Naming Convention

- **Python scripts:** `theorem_X_X_X_verification.py` (underscores replace dots)
- **JSON results:** `theorem_X_X_X_results.json`
- **Reports:** `Theorem-X.X.X-Verification-Summary.md`

## Installation

```bash
# Install Python dependencies
pip install -r verification/requirements.txt

# For Lean verification, see lean/README.md
```

## Running Verification

```bash
# Run a specific verification script
python verification/Phase3/theorem_3_1_1_verification.py

# Run all verifications for a phase
for f in verification/Phase3/*.py; do python "$f"; done

# Run all tests via pytest
python -m pytest verification/ -v
```

## Related Resources

- **Proof Documents:** [../docs/proofs/](../docs/proofs/)
- **Master Plan:** [../docs/Mathematical-Proof-Plan.md](../docs/Mathematical-Proof-Plan.md)
