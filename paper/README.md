# Unified Chiral Geometrogenesis arXiv Preprint

**Status:** Initial Draft Created (2026-01-06)
**Target:** arXiv submission (hep-th primary, math-ph, gr-qc)

## Contents

- `main.tex` — Main unified paper combining Papers 1 and 2
- `references.bib` — Combined bibliography
- `figures/` — All figures from Papers 1 and 2

## Building

```bash
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

Or with latexmk:
```bash
latexmk -pdf main.tex
```

## Paper Structure

The unified paper follows this structure:

1. **Introduction** — Framework overview, key claims, axiom reduction achievement
2. **Part I: Geometric Foundations**
   - Definitions and Framework
   - Observer-Compatible Spacetime Dimensionality (D=4)
   - Euclidean Metric from SU(3) Killing Form
   - Uniqueness of the Stella Octangula
   - Spatial Extension from the Honeycomb
3. **Part II: Axiom Reduction**
   - A0' (Fisher Metric): Chentsov Uniqueness
   - A5 (Born Rule): Geodesic Flow Ergodicity
   - A6 (Square-Integrability): Finite Energy
   - A7/A7' (Measurement and Outcomes): Phase Averaging + Z₃
   - Summary: Zero Irreducible Axioms
4. **Part III: Dynamics**
   - Mass Generation via Phase-Gradient Coupling
   - The Strong CP Problem: Z₃ Resolution
   - Time's Arrow from QCD Topology
   - Baryogenesis via Chiral Bias
5. **Part IV: Emergent Gravity**
   - Einstein's Equations from Fixed-Point Structure
   - Newton's Constant Derivation
6. **Part V: Phenomenological Verification**
   - Fermion Mass Predictions (99%+ PDG agreement)
   - Cosmological Predictions (n_s = 0.9649, 0σ from Planck)
7. **Part VI: Lean Formalization**
   - Methodology
   - Statistics (133K lines, 39/39 tests passing)
8. **Part VII: Discussion**
   - Scope and Limitations
   - Comparison with Other Approaches
   - Testable Predictions

## Key Achievement

**Zero Irreducible Axioms** — All interpretational axioms (Born rule, measurement, 
square-integrability) and phenomenological inputs (Lagrangian form, parameters, 
fermion masses) are systematically derived from geometric structure.

## Source Papers

This unified paper combines content from:
- `papers/paper-1-foundations/` — Geometric foundations
- `papers/paper-2-dynamics/` — Dynamics and phenomenology

## Next Steps

1. [ ] Notation consistency review
2. [ ] Cross-reference verification
3. [ ] Figure numbering update
4. [ ] Test compilation
5. [ ] Final review before arXiv submission

## Related Files

- Verification scripts: `verification/foundations/`
- Lean formalization: `lean/`
- Axiom reduction documentation: `docs/proofs/foundations/Axiom-Reduction-Action-Plan.md`
