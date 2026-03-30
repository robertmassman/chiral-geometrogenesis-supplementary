# G1 Validity — Resolution Report

**Date:** 2026-03-15
**Group:** G1 — Geometric Foundation
**Layer:** 2 (Validity)
**Tool:** AutoInvestigator-CG

## Summary

| Status | Count |
|--------|-------|
| Resolved | 6 |
| Partial | 0 |
| Failed | 0 |
| Skipped | 0 |
| **Total** | **6** |

## Findings

### ✅ V3.4 — MAJOR

**Finding:** D=4 independence inflation: Thm 0.0.9 reproduces Thm 0.0.1 inputs (same Ehrenfest physics), not an independent derivation
**Evidence:** Thm 0.0.1 (Ehrenfest), Thm 0.0.2b (depends on 0.0.1 + P5), Thm 0.0.9 §2.1 ('Thm 0.0.1 is the TARGET, NOT a premise')
**Result:** RESOLVED
**Summary:** Added prominent non-independence notice to Thm 0.0.9 purpose block
**Files modified:** docs/proofs/foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md, verification/autoinvestigator/results.tsv
**Commit:** 7b4c8f71
**Duration:** 132s

### ✅ V3.6 — MAJOR

**Finding:** Prop 0.0.40 Part C derives d_embed = N using framework axiom that encodes coupling→dimension correspondence
**Evidence:** Prop 0.0.40 §5 Step C4 (framework axiom invocation), §9.2 (honest admission of irreducible framework dependency)
**Result:** RESOLVED
**Summary:** Reframed Prop 0.0.40 from claiming to 'derive' 0.0.0f to honestly presenting it as a 'reduction' of 0.0.0f from independent hypothesis to consequence of the core framework axiom (Def 0.0.0). Updated 7 locations across the document.
**Files modified:** docs/proofs/foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md, verification/autoinvestigator/results.tsv
**Commit:** f27e5452
**Duration:** 147s

### ✅ V3.9 — MAJOR

**Finding:** Coupling-to-dimension correspondence (Def 0.0.0 GR1-GR3) is hidden common axiom underlying multiple dimensionality derivations
**Evidence:** Same principle invoked as: 'angular from weight space' (0.0.2b), 'coupling→radial' (0.0.40), 'affine independence' (0.0.2a), 'tiling ℝ³' (0.0.6)
**Result:** RESOLVED
**Summary:** Added Common Axiom Dependency (V3.9) notes to all four dimensionality proof files, making explicit that their results all flow from the same gauge↔geometry correspondence in Def 0.0.0 (GR1–GR3)
**Files modified:** docs/proofs/foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md, docs/proofs/foundations/Lemma-0.0.2a-Confinement-Dimension.md, docs/proofs/foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md, docs/proofs/foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md
**Commit:** f1356c04
**Duration:** 176s

### ✅ V4.2 — MAJOR

**Finding:** Polyhedral necessity depends on non-circular emergence axiom (methodological choice) and conflates 'discrete' with 'polyhedral' — simplicial complexes and causal sets are viable alternatives not refuted
**Evidence:** Theorem-0.0.0a §3.1–§3.5, §4 (methodological note), §5.2 (scope disclaimer)
**Result:** RESOLVED
**Summary:** Qualified the discrete-vs-polyhedral conflation and non-circularity axiom dependency throughout the theorem's Statement file
**Files modified:** docs/proofs/foundations/Theorem-0.0.0a-Polyhedral-Necessity.md
**Commit:** e92a29f4
**Duration:** 192s

### ✅ V4.14 — MAJOR

**Finding:** SU(3) from distinguishability — lower bound N ≥ 3 depends entirely on A-IF (quantum interference form), a framework assumption encoding quantum mechanics; honestly labeled as retrodiction post-V7.8
**Evidence:** Proposition-0.0.XX §3 (A-IF), §5 (N=2 elimination), §0 (epistemic status)
**Result:** RESOLVED
**Summary:** Aligned headline claims (status line, boxed conclusion, summary status) with the file's own honest epistemic disclaimers about retrodiction and A-IF dependency
**Files modified:** docs/proofs/foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md
**Commit:** a96a4b46
**Duration:** 135s

### ✅ V4.15 — MAJOR

**Finding:** GR1–GR3 + MIN1–MIN3 collectively function as a selection device for the stella octangula — alternative axiom sets (adjoint rep, non-minimal, simplicial) could select different objects; axiom package does the work attributed to derivation
**Evidence:** Definition-0.0.0 §2–§3, Theorem-0.0.3, Theorem-0.0.3b
**Result:** RESOLVED
**Summary:** Added epistemic transparency notes making the axiom package's role as a definition space explicit, with analysis of three concrete alternative axiom sets
**Files modified:** docs/proofs/foundations/Definition-0.0.0-Minimal-Geometric-Realization.md, docs/proofs/foundations/Theorem-0.0.3-Stella-Uniqueness.md, docs/proofs/foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md, verification/autoinvestigator/results.tsv
**Commit:** 551830a6
**Duration:** 204s
