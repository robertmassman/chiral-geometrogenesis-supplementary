# Proof Index: Chiral Geometrogenesis

> **Auto-generated hierarchical index of all proof documents**
> Last updated: 2026-02-16

This document provides an organized, hierarchical listing of all proof files in `docs/proofs/`. For theorem status, dependencies, and verification details, see [Mathematical-Proof-Plan.md](../Mathematical-Proof-Plan.md).

---

## Table of Contents

1. [Foundations (Phase -1)](#foundations-phase--1) — Minimal axioms, 0.0.x theorems
2. [Phase 0](#phase-0) — Pre-geometric foundations, 0.1.x-0.3.x
3. [Phase 1](#phase-1) — SU(3) geometry and chiral fields
4. [Phase 2](#phase-2) — Pressure-depression dynamics
5. [Phase 3](#phase-3) — Mass generation
6. [Phase 4](#phase-4) — Topological solitons
7. [Phase 5](#phase-5) — Emergent spacetime and gravity
8. [Phase 6](#phase-6) — Scattering theory
9. [Phase 7](#phase-7) — Renormalization and consistency
10. [Phase 8](#phase-8) — Predictions and tests
11. [Reference](#reference) — Constants, techniques, protocols
12. [Supporting](#supporting) — Research and analysis documents
13. [Verification Records](#verification-records) — Multi-agent verification reports

---

## Naming Conventions

| Prefix | Description |
|--------|-------------|
| `Definition-` | Mathematical/physical definitions |
| `Theorem-` | Major theorems requiring proof |
| `Proposition-` | Significant propositions |
| `Lemma-` | Supporting lemmas |
| `Corollary-` | Consequences of theorems |
| `Derivation-` | Detailed derivations |
| `Prediction-` | Experimental/theoretical predictions |
| `Proof-` | Additional proofs |
| `Extension-` | Extensions of existing results |

**3-File Structure** (for major theorems):
- `[Type]-X.Y.Z.md` — Main statement
- `[Type]-X.Y.Z-Derivation.md` — Full proof
- `[Type]-X.Y.Z-Applications.md` — Verification & predictions

---

## Foundations (Phase -1)

**132 files** — Minimal axioms, 0.0.x theorems

### Definitions

| Number | Title | File |
|--------|-------|------|
| 0.0.0 | Minimal Geometric Realization | [Definition-0.0.0-Minimal-Geometric-Realization.md](foundations/Definition-0.0.0-Minimal-Geometric-Realization.md) |
| 0.0.32 | Internal Observer | [Definition-0.0.32-Internal-Observer.md](foundations/Definition-0.0.32-Internal-Observer.md) |

### Lemmas

| Number | Title | File |
|--------|-------|------|
| 0.0.2a | Confinement Dimension | [Lemma-0.0.2a-Confinement-Dimension.md](foundations/Lemma-0.0.2a-Confinement-Dimension.md) |
| 0.0.17c | Fisher Killing Equivalence | [Lemma-0.0.17c-Fisher-Killing-Equivalence.md](foundations/Lemma-0.0.17c-Fisher-Killing-Equivalence.md) |

### Propositions

| Number | Title | Files |
|--------|-------|-------|
| 0.0.XX | SU(3) From Distinguishability Constraints | [Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md](foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md) |
| 0.0.XXa | First Stable Principle | [Proposition-0.0.XXa-First-Stable-Principle.md](foundations/Proposition-0.0.XXa-First-Stable-Principle.md) |
| 0.0.XXb | Bootstrap Computability | [Proposition-0.0.XXb-Bootstrap-Computability.md](foundations/Proposition-0.0.XXb-Bootstrap-Computability.md) |
| 0.0.XXd | Computational Universality of CG Primitives | [Proposition-0.0.XXd-Computational-Universality-CG-Primitives.md](foundations/Proposition-0.0.XXd-Computational-Universality-CG-Primitives.md) · [Lean 4](../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XXd.lean) |
| 0.0.XXe | Continuum Limit of Self-Replicating Fields | [Proposition-0.0.XXe-Continuum-Self-Replicating-Fields.md](foundations/Proposition-0.0.XXe-Continuum-Self-Replicating-Fields.md) |
| 0.0.XXf | Computational Classification of Stella Dynamics | [Proposition-0.0.XXf-Computational-Classification-Stella-Dynamics.md](foundations/Proposition-0.0.XXf-Computational-Classification-Stella-Dynamics.md) · [Lean 4](../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XXf.lean) |
| 0.0.XXg | Q₃ Spectral Structure on the Stella Octangula | [Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md](foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md) · [Derivation](foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Derivation.md) · [Applications](foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Applications.md) |
| 0.0.5a | Z3 Center Constrains Theta Angle | [Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md](foundations/Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md) |
| 0.0.5b | Quark Mass Phase Constraint | [Proposition-0.0.5b-Quark-Mass-Phase-Constraint.md](foundations/Proposition-0.0.5b-Quark-Mass-Phase-Constraint.md) |
| 0.0.6b | Continuum Limit Procedure | [Proposition-0.0.6b-Continuum-Limit-Procedure.md](foundations/Proposition-0.0.6b-Continuum-Limit-Procedure.md) |
| 0.0.16a | A3 From Physical Requirements | [Proposition-0.0.16a-A3-From-Physical-Requirements.md](foundations/Proposition-0.0.16a-A3-From-Physical-Requirements.md) |
| 0.0.17a | Born Rule From Geodesic Flow | [Proposition-0.0.17a-Born-Rule-From-Geodesic-Flow.md](foundations/Proposition-0.0.17a-Born-Rule-From-Geodesic-Flow.md) |
| 0.0.17aa | Nf Topological Analysis | [Statement](foundations/Proposition-0.0.17aa-Nf-Topological-Analysis.md), [Resolution Plan](foundations/Proposition-0.0.17aa-Resolution-Plan.md), [Scale Separation Analysis](foundations/Proposition-0.0.17aa-Scale-Separation-Analysis.md), [Spectral Index From First Principles](foundations/Proposition-0.0.17aa-Spectral-Index-From-First-Principles.md), [dim8 2pi Derivation Plan](foundations/Proposition-0.0.17aa-dim8-2pi-Derivation-Plan.md) |
| 0.0.17ab | Newtons Constant From Topology | [Statement](foundations/Proposition-0.0.17ab-Newtons-Constant-From-Topology.md), [Derivation](foundations/Proposition-0.0.17ab-Newtons-Constant-From-Topology-Derivation.md), [Applications](foundations/Proposition-0.0.17ab-Newtons-Constant-From-Topology-Applications.md) |
| 0.0.17ac | Edge Mode Decomposition UV Coupling | [Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md](foundations/Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md) |
| 0.0.17b | Fisher Metric Uniqueness | [Proposition-0.0.17b-Fisher-Metric-Uniqueness.md](foundations/Proposition-0.0.17b-Fisher-Metric-Uniqueness.md) |
| 0.0.17c | Arrow of Time From Information Geometry | [Proposition-0.0.17c-Arrow-of-Time-From-Information-Geometry.md](foundations/Proposition-0.0.17c-Arrow-of-Time-From-Information-Geometry.md) |
| 0.0.17d | EFT Cutoff From Confinement | [Proposition-0.0.17d-EFT-Cutoff-From-Confinement.md](foundations/Proposition-0.0.17d-EFT-Cutoff-From-Confinement.md) |
| 0.0.17e | Square Integrability From Finite Energy | [Proposition-0.0.17e-Square-Integrability-From-Finite-Energy.md](foundations/Proposition-0.0.17e-Square-Integrability-From-Finite-Energy.md) |
| 0.0.17f | Decoherence From Geodesic Mixing | [Proposition-0.0.17f-Decoherence-From-Geodesic-Mixing.md](foundations/Proposition-0.0.17f-Decoherence-From-Geodesic-Mixing.md) |
| 0.0.17g | Objective Collapse From Z3 Discretization | [Proposition-0.0.17g-Objective-Collapse-From-Z3-Discretization.md](foundations/Proposition-0.0.17g-Objective-Collapse-From-Z3-Discretization.md) |
| 0.0.17h | Information Horizon Derivation | [Proposition-0.0.17h-Information-Horizon-Derivation.md](foundations/Proposition-0.0.17h-Information-Horizon-Derivation.md) |
| 0.0.17i | Z3 Measurement Extension | [Proposition-0.0.17i-Z3-Measurement-Extension.md](foundations/Proposition-0.0.17i-Z3-Measurement-Extension.md) |
| 0.0.17j | String Tension From Casimir Energy | [Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md](foundations/Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md) |
| 0.0.17k | Pion Decay Constant From Phase Lock | [Proposition-0.0.17k-Pion-Decay-Constant-From-Phase-Lock.md](foundations/Proposition-0.0.17k-Pion-Decay-Constant-From-Phase-Lock.md) |
| 0.0.17k1 | One Loop Correction To Pion Decay Constant | [Proposition-0.0.17k1-One-Loop-Correction-To-Pion-Decay-Constant.md](foundations/Proposition-0.0.17k1-One-Loop-Correction-To-Pion-Decay-Constant.md) |
| 0.0.17k2 | CG Effective Action Op4 GL Matching | [Proposition-0.0.17k2-CG-Effective-Action-Op4-GL-Matching.md](foundations/Proposition-0.0.17k2-CG-Effective-Action-Op4-GL-Matching.md) |
| 0.0.17k3 | First Principles Ell4 From Stella Octangula | [Proposition-0.0.17k3-First-Principles-Ell4-From-Stella-Octangula.md](foundations/Proposition-0.0.17k3-First-Principles-Ell4-From-Stella-Octangula.md) |
| 0.0.17k4 | cV From Z3 Phase Structure | [Proposition-0.0.17k4-cV-From-Z3-Phase-Structure.md](foundations/Proposition-0.0.17k4-cV-From-Z3-Phase-Structure.md) |
| 0.0.17l | Internal Frequency From Casimir Equipartition | [Proposition-0.0.17l-Internal-Frequency-From-Casimir-Equipartition.md](foundations/Proposition-0.0.17l-Internal-Frequency-From-Casimir-Equipartition.md) |
| 0.0.17m | Chiral VEV From Phase Lock Stiffness | [Proposition-0.0.17m-Chiral-VEV-From-Phase-Lock-Stiffness.md](foundations/Proposition-0.0.17m-Chiral-VEV-From-Phase-Lock-Stiffness.md) |
| 0.0.17n | P4 Fermion Mass Comparison | [Proposition-0.0.17n-P4-Fermion-Mass-Comparison.md](foundations/Proposition-0.0.17n-P4-Fermion-Mass-Comparison.md) |
| 0.0.17o | Regularization Parameter Derivation | [Proposition-0.0.17o-Regularization-Parameter-Derivation.md](foundations/Proposition-0.0.17o-Regularization-Parameter-Derivation.md) |
| 0.0.17p | Resolution of Problem of Time | [Proposition-0.0.17p-Resolution-of-Problem-of-Time.md](foundations/Proposition-0.0.17p-Resolution-of-Problem-of-Time.md) |
| 0.0.17q | QCD Scale From Dimensional Transmutation | [Proposition-0.0.17q-QCD-Scale-From-Dimensional-Transmutation.md](foundations/Proposition-0.0.17q-QCD-Scale-From-Dimensional-Transmutation.md) |
| 0.0.17r | Lattice Spacing From Holographic Self Consistency | [Proposition-0.0.17r-Lattice-Spacing-From-Holographic-Self-Consistency.md](foundations/Proposition-0.0.17r-Lattice-Spacing-From-Holographic-Self-Consistency.md) |
| 0.0.17s | Strong Coupling From Gauge Unification | [Proposition-0.0.17s-Strong-Coupling-From-Gauge-Unification.md](foundations/Proposition-0.0.17s-Strong-Coupling-From-Gauge-Unification.md) |
| 0.0.17t | Topological Origin Of Scale Hierarchy | [Proposition-0.0.17t-Topological-Origin-Of-Scale-Hierarchy.md](foundations/Proposition-0.0.17t-Topological-Origin-Of-Scale-Hierarchy.md) |
| 0.0.17u | Cosmological Initial Conditions From Pre Geometry | [Proposition-0.0.17u-Cosmological-Initial-Conditions-From-Pre-Geometry.md](foundations/Proposition-0.0.17u-Cosmological-Initial-Conditions-From-Pre-Geometry.md) |
| 0.0.17v | Holographic Scale From Self Consistency | [Proposition-0.0.17v-Holographic-Scale-From-Self-Consistency.md](foundations/Proposition-0.0.17v-Holographic-Scale-From-Self-Consistency.md) |
| 0.0.17w | Equipartition From Maximum Entropy | [Proposition-0.0.17w-Equipartition-From-Maximum-Entropy.md](foundations/Proposition-0.0.17w-Equipartition-From-Maximum-Entropy.md) |
| 0.0.17x | UV Coupling And Index Theorem Connection | [Proposition-0.0.17x-UV-Coupling-And-Index-Theorem-Connection.md](foundations/Proposition-0.0.17x-UV-Coupling-And-Index-Theorem-Connection.md) |
| 0.0.17y | Bootstrap Fixed Point Uniqueness | [Proposition-0.0.17y-Bootstrap-Fixed-Point-Uniqueness.md](foundations/Proposition-0.0.17y-Bootstrap-Fixed-Point-Uniqueness.md) |
| 0.0.17z | Non Perturbative Corrections To Bootstrap | [Proposition-0.0.17z-Non-Perturbative-Corrections-To-Bootstrap.md](foundations/Proposition-0.0.17z-Non-Perturbative-Corrections-To-Bootstrap.md) |
| 0.0.17z1 | Geometric Derivation Non Perturbative Coefficients | [Proposition-0.0.17z1-Geometric-Derivation-Non-Perturbative-Coefficients.md](foundations/Proposition-0.0.17z1-Geometric-Derivation-Non-Perturbative-Coefficients.md) |
| 0.0.17z2 | Scale Dependent Effective Euler Characteristic | [Proposition-0.0.17z2-Scale-Dependent-Effective-Euler-Characteristic.md](foundations/Proposition-0.0.17z2-Scale-Dependent-Effective-Euler-Characteristic.md) |
| 0.0.18 | Electroweak Scale From Chi Field | [Proposition-0.0.18-Electroweak-Scale-From-Chi-Field.md](foundations/Proposition-0.0.18-Electroweak-Scale-From-Chi-Field.md) |
| 0.0.19 | Electroweak Topological Index | [Proposition-0.0.19-Electroweak-Topological-Index.md](foundations/Proposition-0.0.19-Electroweak-Topological-Index.md) |
| 0.0.20 | Electroweak Scale From Central Charge Flow | [Proposition-0.0.20-Electroweak-Scale-From-Central-Charge-Flow.md](foundations/Proposition-0.0.20-Electroweak-Scale-From-Central-Charge-Flow.md) |
| 0.0.21 | Unified Electroweak Scale Derivation | [Proposition-0.0.21-Unified-Electroweak-Scale-Derivation.md](foundations/Proposition-0.0.21-Unified-Electroweak-Scale-Derivation.md) |
| 0.0.22 | SU(2) Substructure From Stella Octangula | [Proposition-0.0.22-SU2-Substructure-From-Stella-Octangula.md](foundations/Proposition-0.0.22-SU2-Substructure-From-Stella-Octangula.md) |
| 0.0.23 | Hypercharge From Geometric Embedding | [Proposition-0.0.23-Hypercharge-From-Geometric-Embedding.md](foundations/Proposition-0.0.23-Hypercharge-From-Geometric-Embedding.md) |
| 0.0.24 | SU(2) Gauge Coupling From Unification | [Proposition-0.0.24-SU2-Gauge-Coupling-From-Unification.md](foundations/Proposition-0.0.24-SU2-Gauge-Coupling-From-Unification.md) |
| 0.0.24a | Electroweak Precision Oblique Parameters | [Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md](foundations/Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md) |
| 0.0.25 | Alpha GUT Threshold Formula | [Proposition-0.0.25-Alpha-GUT-Threshold-Formula.md](foundations/Proposition-0.0.25-Alpha-GUT-Threshold-Formula.md) |
| 0.0.26 | Electroweak Cutoff Derivation | [Proposition-0.0.26-Electroweak-Cutoff-Derivation.md](foundations/Proposition-0.0.26-Electroweak-Cutoff-Derivation.md) |
| 0.0.27 | Gauge Fermion Instanton Structure | [Statement](foundations/Proposition-0.0.27-Gauge-Fermion-Instanton-Structure.md), [Higgs Mass From Geometry](foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md), [Lattice QFT On Stella](foundations/Proposition-0.0.27-Lattice-QFT-On-Stella.md) |
| 0.0.27a | Quartic Normalization From Equipartition | [Proposition-0.0.27a-Quartic-Normalization-From-Equipartition.md](foundations/Proposition-0.0.27a-Quartic-Normalization-From-Equipartition.md) |
| 0.0.28 | Theory Space Fixed Point | [Proposition-0.0.28-Theory-Space-Fixed-Point.md](foundations/Proposition-0.0.28-Theory-Space-Fixed-Point.md) |
| 0.0.30 | Holographic Saturation From Thermodynamic Equilibrium | [Proposition-0.0.30-Holographic-Saturation-From-Thermodynamic-Equilibrium.md](foundations/Proposition-0.0.30-Holographic-Saturation-From-Thermodynamic-Equilibrium.md) |
| 0.0.32a | Observer Fixed Point | [Proposition-0.0.32a-Observer-Fixed-Point.md](foundations/Proposition-0.0.32a-Observer-Fixed-Point.md) |
| 0.0.34 | Observer Participation | [Proposition-0.0.34-Observer-Participation.md](foundations/Proposition-0.0.34-Observer-Participation.md) |
| 0.0.35 | Dimensional Uniqueness Of R Stella | [Statement](foundations/Proposition-0.0.35-Dimensional-Uniqueness-Of-R-Stella.md), [Derivation](foundations/Proposition-0.0.35-Dimensional-Uniqueness-Of-R-Stella-Derivation.md), [Applications](foundations/Proposition-0.0.35-Dimensional-Uniqueness-Of-R-Stella-Applications.md) |
| 0.0.36 | Anthropic Bounds On R Stella | [Proposition-0.0.36-Anthropic-Bounds-On-R-Stella.md](foundations/Proposition-0.0.36-Anthropic-Bounds-On-R-Stella.md) |
| 0.0.37 | Complete Higgs Potential And Trilinear Coupling | [Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md](foundations/Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md) |
| 0.0.38 | Exact Stella Gauge Partition Function | [Proposition-0.0.38-Exact-Stella-Gauge-Partition-Function.md](foundations/Proposition-0.0.38-Exact-Stella-Gauge-Partition-Function.md) |
| 0.0.38a | Stella Gauge Spectrum | [Proposition-0.0.38a-Stella-Gauge-Spectrum.md](foundations/Proposition-0.0.38a-Stella-Gauge-Spectrum.md) |
| 0.0.39 | Stella Adjoint Decomposition | [Proposition-0.0.39-Stella-Adjoint-Decomposition.md](foundations/Proposition-0.0.39-Stella-Adjoint-Decomposition.md) |
| 0.0.40 | Embedding Dimension From Confinement | [Proposition-0.0.40-Embedding-Dimension-From-Confinement.md](foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md) |
| 0.0.41a | CG Dimensional Optimality | [Proposition-0.0.41a-CG-Dimensional-Optimality.md](foundations/Proposition-0.0.41a-CG-Dimensional-Optimality.md) |

### Theorems

| Number | Title | Files |
|--------|-------|-------|
| 0.0.0 | GR Conditions Derivation | [Theorem-0.0.0-GR-Conditions-Derivation.md](foundations/Theorem-0.0.0-GR-Conditions-Derivation.md) |
| 0.0.XXc | Godel Bootstrap Separation | [Statement](foundations/Theorem-0.0.XXc-Godel-Bootstrap-Separation.md), [Derivation](foundations/Theorem-0.0.XXc-Godel-Bootstrap-Separation-Derivation.md), [Applications](foundations/Theorem-0.0.XXc-Godel-Bootstrap-Separation-Applications.md) |
| 0.0.0a | Polyhedral Necessity | [Statement](foundations/Theorem-0.0.0a-Polyhedral-Necessity.md), [Derivation](foundations/Theorem-0.0.0a-Polyhedral-Necessity-Derivation.md), [Applications](foundations/Theorem-0.0.0a-Polyhedral-Necessity-Applications.md) |
| 0.0.0b | Geometric Realization From Finite Information | [Theorem-0.0.0b-Geometric-Realization-From-Finite-Information.md](foundations/Theorem-0.0.0b-Geometric-Realization-From-Finite-Information.md) |
| 0.0.0c | Finite Information From Observer Existence | [Theorem-0.0.0c-Finite-Information-From-Observer-Existence.md](foundations/Theorem-0.0.0c-Finite-Information-From-Observer-Existence.md) |
| 0.0.1 | D=4 From Observer Existence | [Theorem-0.0.1-D4-From-Observer-Existence.md](foundations/Theorem-0.0.1-D4-From-Observer-Existence.md) |
| 0.0.2 | Euclidean From SU(3) | [Theorem-0.0.2-Euclidean-From-SU3.md](foundations/Theorem-0.0.2-Euclidean-From-SU3.md) |
| 0.0.2b | Dimension Color Correspondence | [Theorem-0.0.2b-Dimension-Color-Correspondence.md](foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md) |
| 0.0.3 | Stella Uniqueness | [Theorem-0.0.3-Stella-Uniqueness.md](foundations/Theorem-0.0.3-Stella-Uniqueness.md) |
| 0.0.3a | Computational Crystallization of Stella Octangula | [Statement](foundations/Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula.md), [Derivation](foundations/Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Derivation.md), [Applications](foundations/Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Applications.md) |
| 0.0.3b (Prop) | Spontaneous Lattice Formation from Z₃ Fields | [Proposition-0.0.3b-Spontaneous-Lattice-Formation-From-Z3-Fields.md](foundations/Proposition-0.0.3b-Spontaneous-Lattice-Formation-From-Z3-Fields.md) |
| 0.0.3b (Thm) | Geometric Realization Completeness | [Theorem-0.0.3b-Geometric-Realization-Completeness.md](foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md) |
| 0.0.4 | GUT Structure From Stella Octangula | [Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md](foundations/Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md) |
| 0.0.5 | Chirality Selection From Geometry | [Theorem-0.0.5-Chirality-Selection-From-Geometry.md](foundations/Theorem-0.0.5-Chirality-Selection-From-Geometry.md) |
| 0.0.6 | Spatial Extension From Octet Truss | [Statement](foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md), [Derivation](foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss-Derivation.md), [Applications](foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss-Applications.md) |
| 0.0.7 | Lorentz Violation Bounds | [Theorem-0.0.7-Lorentz-Violation-Bounds.md](foundations/Theorem-0.0.7-Lorentz-Violation-Bounds.md) |
| 0.0.8 | Emergent Rotational Symmetry | [Theorem-0.0.8-Emergent-Rotational-Symmetry.md](foundations/Theorem-0.0.8-Emergent-Rotational-Symmetry.md) |
| 0.0.9 | Framework Internal D=4 Consistency Check | [Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md](foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md) |
| 0.0.10 | Quantum Mechanics Emergence | [Theorem-0.0.10-Quantum-Mechanics-Emergence.md](foundations/Theorem-0.0.10-Quantum-Mechanics-Emergence.md) |
| 0.0.11 | Lorentz Boost Emergence | [Theorem-0.0.11-Lorentz-Boost-Emergence.md](foundations/Theorem-0.0.11-Lorentz-Boost-Emergence.md) |
| 0.0.12 | Categorical Equivalence | [Statement](foundations/Theorem-0.0.12-Categorical-Equivalence.md), [Derivation](foundations/Theorem-0.0.12-Categorical-Equivalence-Derivation.md), [Applications](foundations/Theorem-0.0.12-Categorical-Equivalence-Applications.md) |
| 0.0.13 | Tannaka Reconstruction SU(3) | [Statement](foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md), [Derivation](foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3-Derivation.md), [Applications](foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3-Applications.md) |
| 0.0.14 | Novel Lorentz Violation Pattern | [Theorem-0.0.14-Novel-Lorentz-Violation-Pattern.md](foundations/Theorem-0.0.14-Novel-Lorentz-Violation-Pattern.md) |
| 0.0.15 | Topological Determination SU(3) | [Theorem-0.0.15-Topological-Determination-SU3.md](foundations/Theorem-0.0.15-Topological-Determination-SU3.md) |
| 0.0.16 | Adjacency From SU(3) | [Theorem-0.0.16-Adjacency-From-SU3.md](foundations/Theorem-0.0.16-Adjacency-From-SU3.md) |
| 0.0.17 | Information Geometric Unification | [Theorem-0.0.17-Information-Geometric-Unification.md](foundations/Theorem-0.0.17-Information-Geometric-Unification.md) |
| 0.0.18 | Signature Equations | [Theorem-0.0.18-Signature-Equations.md](foundations/Theorem-0.0.18-Signature-Equations.md) |
| 0.0.19 | Quantitative Self Reference Uniqueness | [Theorem-0.0.19-Quantitative-Self-Reference-Uniqueness.md](foundations/Theorem-0.0.19-Quantitative-Self-Reference-Uniqueness.md) |
| 0.0.29 | Lawvere Bootstrap Uniqueness | [Theorem-0.0.29-Lawvere-Bootstrap-Uniqueness.md](foundations/Theorem-0.0.29-Lawvere-Bootstrap-Uniqueness.md) |
| 0.0.31 | Unconditional Uniqueness CG Fixed Point | [Theorem-0.0.31-Unconditional-Uniqueness-CG-Fixed-Point.md](foundations/Theorem-0.0.31-Unconditional-Uniqueness-CG-Fixed-Point.md) |
| 0.0.33 | Information Geometry Duality | [Theorem-0.0.33-Information-Geometry-Duality.md](foundations/Theorem-0.0.33-Information-Geometry-Duality.md) |
| 0.0.41 | Dimensional Incompleteness | [Theorem-0.0.41-Dimensional-Incompleteness.md](foundations/Theorem-0.0.41-Dimensional-Incompleteness.md) |

### Other Documents

| Title | File |
|-------|------|
| Axiom Reduction Action Plan | [Axiom-Reduction-Action-Plan.md](foundations/Axiom-Reduction-Action-Plan.md) |
| CATEGORY INDEX | [CATEGORY-INDEX.md](foundations/CATEGORY-INDEX.md) |
| Foundation Assessment | [Foundation-Assessment.md](foundations/Foundation-Assessment.md) |
| Gap Analysis Pre Geometric Structure | [Gap-Analysis-Pre-Geometric-Structure.md](foundations/Gap-Analysis-Pre-Geometric-Structure.md) |
| RENUMBERING PLAN | [RENUMBERING-PLAN.md](foundations/RENUMBERING-PLAN.md) |
| Research D1 Strong CP Problem Analysis | [Research-D1-Strong-CP-Problem-Analysis.md](foundations/Research-D1-Strong-CP-Problem-Analysis.md) |
| Research D2 Direct Einstein Equation Derivation | [Research-D2-Direct-Einstein-Equation-Derivation.md](foundations/Research-D2-Direct-Einstein-Equation-Derivation.md) |
| Research D2 Implementation Plan | [Research-D2-Implementation-Plan.md](foundations/Research-D2-Implementation-Plan.md) |
| Research D2 Path F Direct Einstein Derivation | [Research-D2-Path-F-Direct-Einstein-Derivation.md](foundations/Research-D2-Path-F-Direct-Einstein-Derivation.md) |
| Research D3 Bootstrap Equations Analysis | [Research-D3-Bootstrap-Equations-Analysis.md](foundations/Research-D3-Bootstrap-Equations-Analysis.md) |
| Research D3 Category Theoretic Formalization | [Research-D3-Category-Theoretic-Formalization.md](foundations/Research-D3-Category-Theoretic-Formalization.md) |
| Research D3 Computational Bootstrap | [Research-D3-Computational-Bootstrap.md](foundations/Research-D3-Computational-Bootstrap.md) |
| Research D3 Fixed Point Proof | [Research-D3-Fixed-Point-Proof.md](foundations/Research-D3-Fixed-Point-Proof.md) |
| Research D3 Higher Loop Analysis | [Research-D3-Higher-Loop-Analysis.md](foundations/Research-D3-Higher-Loop-Analysis.md) |
| Research P2 P4 Physical Inputs Unification | [Research-P2-P4-Physical-Inputs-Unification.md](foundations/Research-P2-P4-Physical-Inputs-Unification.md) |
| Research Plan Summary | [Research-Plan-Summary.md](foundations/Research-Plan-Summary.md) |

---

## Phase 0

**16 files** — Pre-geometric foundations, 0.1.x-0.3.x

### Definitions

| Number | Title | Files |
|--------|-------|-------|
| 0.1.1 | Stella Octangula Boundary Topology | [Statement](Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md), [Derivation](Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology-Derivation.md), [Applications](Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology-Applications.md) |
| 0.1.2 | Three Color Fields Relative Phases | [Definition-0.1.2-Three-Color-Fields-Relative-Phases.md](Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md) |
| 0.1.3 | Pressure Functions | [Definition-0.1.3-Pressure-Functions.md](Phase0/Definition-0.1.3-Pressure-Functions.md) |
| 0.1.4 | Color Field Domains | [Definition-0.1.4-Color-Field-Domains.md](Phase0/Definition-0.1.4-Color-Field-Domains.md) |

### Propositions

| Number | Title | File |
|--------|-------|------|
| 0.1.3a | Pressure Function Form-Independence | [Proposition-0.1.3a-Pressure-Function-Form-Independence.md](Phase0/Proposition-0.1.3a-Pressure-Function-Form-Independence.md) · [Lean 4](../../lean/ChiralGeometrogenesis/Phase0/Proposition_0_1_3a.lean) |

### Theorems

| Number | Title | Files |
|--------|-------|-------|
| 0.1.0 | Field Existence From Distinguishability | [Statement](Phase0/Theorem-0.1.0-Field-Existence-From-Distinguishability.md), [Prime Fields From Gauge Bundle Structure](Phase0/Theorem-0.1.0-Prime-Fields-From-Gauge-Bundle-Structure.md) |
| 0.2.1 | Total Field Superposition | [Theorem-0.2.1-Total-Field-Superposition.md](Phase0/Theorem-0.2.1-Total-Field-Superposition.md) |
| 0.2.2 | Internal Time Emergence | [Theorem-0.2.2-Internal-Time-Emergence.md](Phase0/Theorem-0.2.2-Internal-Time-Emergence.md) |
| 0.2.3 | Stable Convergence Point | [Statement](Phase0/Theorem-0.2.3-Stable-Convergence-Point.md), [Derivation](Phase0/Theorem-0.2.3-Stable-Convergence-Point-Derivation.md), [Applications](Phase0/Theorem-0.2.3-Stable-Convergence-Point-Applications.md) |
| 0.2.4 | Pre Geometric Energy Functional | [Theorem-0.2.4-Pre-Geometric-Energy-Functional.md](Phase0/Theorem-0.2.4-Pre-Geometric-Energy-Functional.md) |
| 0.3.1 | W Direction Correspondence | [Theorem-0.3.1-W-Direction-Correspondence.md](Phase0/Theorem-0.3.1-W-Direction-Correspondence.md) |

---

## Phase 1

**5 files** — SU(3) geometry and chiral fields

### Theorems

| Number | Title | File |
|--------|-------|------|
| 1.1.1 | SU(3) Stella Octangula | [Theorem-1.1.1-SU3-Stella-Octangula.md](Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md) |
| 1.1.2 | Charge Conjugation | [Theorem-1.1.2-Charge-Conjugation.md](Phase1/Theorem-1.1.2-Charge-Conjugation.md) |
| 1.1.3 | Color Confinement Geometry | [Theorem-1.1.3-Color-Confinement-Geometry.md](Phase1/Theorem-1.1.3-Color-Confinement-Geometry.md) |
| 1.1.4 | Stella Diagram Rules | [Definition-1.1.4-Stella-Diagram-Rules.md](Phase1/Definition-1.1.4-Stella-Diagram-Rules.md) |
| 1.2.1 | Vacuum Expectation Value | [Theorem-1.2.1-Vacuum-Expectation-Value.md](Phase1/Theorem-1.2.1-Vacuum-Expectation-Value.md) |
| 1.2.2 | Chiral Anomaly | [Theorem-1.2.2-Chiral-Anomaly.md](Phase1/Theorem-1.2.2-Chiral-Anomaly.md) |

---

## Phase 2

**39 files** — Pressure-depression dynamics

### Lemmas

| Number | Title | File |
|--------|-------|------|
| 2.1.3 | Depression Symmetry Breaking | [Lemma-2.1.3-Depression-Symmetry-Breaking.md](Phase2/Lemma-2.1.3-Depression-Symmetry-Breaking.md) |

### Propositions

| Number | Title | Files |
|--------|-------|-------|
| 2.4.2 | Pre Geometric Beta Function | [Proposition-2.4.2-Pre-Geometric-Beta-Function.md](Phase2/Proposition-2.4.2-Pre-Geometric-Beta-Function.md) |
| 2.5.2a | Wilson Loop Area Law From Geometry | [Statement](Phase2/Proposition-2.5.2a-Wilson-Loop-Area-Law-From-Geometry.md), [Derivation](Phase2/Proposition-2.5.2a-Wilson-Loop-Area-Law-From-Geometry-Derivation.md), [Applications](Phase2/Proposition-2.5.2a-Wilson-Loop-Area-Law-From-Geometry-Applications.md) |
| 2.5.2b | Inter Stella Gauge Coupling FCC | [Statement](Phase2/Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC.md), [Derivation](Phase2/Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Derivation.md), [Applications](Phase2/Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC-Applications.md) |
| 2.5.2c | Transfer Matrix FCC Layers | [Statement](Phase2/Proposition-2.5.2c-Transfer-Matrix-FCC-Layers.md), [Derivation](Phase2/Proposition-2.5.2c-Transfer-Matrix-FCC-Layers-Derivation.md), [Applications](Phase2/Proposition-2.5.2c-Transfer-Matrix-FCC-Layers-Applications.md) |

### Theorems

| Number | Title | Files |
|--------|-------|-------|
| 2.1.1 | Bag Model Derivation | [Theorem-2.1.1-Bag-Model-Derivation.md](Phase2/Theorem-2.1.1-Bag-Model-Derivation.md) |
| 2.1.2 | Pressure Field Gradient | [Theorem-2.1.2-Pressure-Field-Gradient.md](Phase2/Theorem-2.1.2-Pressure-Field-Gradient.md) |
| 2.2.1 | Phase Locked Oscillation | [Theorem-2.2.1-Phase-Locked-Oscillation.md](Phase2/Theorem-2.2.1-Phase-Locked-Oscillation.md) |
| 2.2.2 | Limit Cycle | [Theorem-2.2.2-Limit-Cycle.md](Phase2/Theorem-2.2.2-Limit-Cycle.md) |
| 2.2.3 | Time Irreversibility | [Theorem-2.2.3-Time-Irreversibility.md](Phase2/Theorem-2.2.3-Time-Irreversibility.md) |
| 2.2.4 | EFT Derivation | [Theorem-2.2.4-EFT-Derivation.md](Phase2/Theorem-2.2.4-EFT-Derivation.md) |
| 2.2.5 | Coarse Grained Entropy Production | [Theorem-2.2.5-Coarse-Grained-Entropy-Production.md](Phase2/Theorem-2.2.5-Coarse-Grained-Entropy-Production.md) |
| 2.2.6 | Entropy Propagation | [Theorem-2.2.6-Entropy-Propagation.md](Phase2/Theorem-2.2.6-Entropy-Propagation.md) |
| 2.3.1 | Universal Chirality | [Statement](Phase2/Theorem-2.3.1-Universal-Chirality.md), [Derivation](Phase2/Theorem-2.3.1-Universal-Chirality-Derivation.md), [Applications](Phase2/Theorem-2.3.1-Universal-Chirality-Applications.md) |
| 2.4.1 | Gauge Unification | [Statement](Phase2/Theorem-2.4.1-Gauge-Unification.md), [Derivation](Phase2/Theorem-2.4.1-Gauge-Unification-Derivation.md), [Applications](Phase2/Theorem-2.4.1-Gauge-Unification-Applications.md) |
| 2.4.2 | Topological Chirality | [Statement](Phase2/Theorem-2.4.2-Topological-Chirality.md), [Derivation](Phase2/Theorem-2.4.2-Topological-Chirality-Derivation.md), [Applications](Phase2/Theorem-2.4.2-Topological-Chirality-Applications.md) |
| 2.5.1 | CG Lagrangian Derivation | [Theorem-2.5.1-CG-Lagrangian-Derivation.md](Phase2/Theorem-2.5.1-CG-Lagrangian-Derivation.md) |
| 2.5.2 | Dynamical Confinement | [Statement](Phase2/Theorem-2.5.2-Dynamical-Confinement.md), [Derivation](Phase2/Theorem-2.5.2-Dynamical-Confinement-Derivation.md), [Applications](Phase2/Theorem-2.5.2-Dynamical-Confinement-Applications.md) |

### Derivations

| Number | Title | File |
|--------|-------|------|
| 2.1.2a | Equilibrium Radius | [Derivation-2.1.2a-Equilibrium-Radius.md](Phase2/Derivation-2.1.2a-Equilibrium-Radius.md) |
| 2.1.2b | Chi Profile | [Derivation-2.1.2b-Chi-Profile.md](Phase2/Derivation-2.1.2b-Chi-Profile.md) |
| 2.1.2c | Bag Constant From Stella Geometry | [Derivation-2.1.2c-Bag-Constant-From-Stella-Geometry.md](Phase2/Derivation-2.1.2c-Bag-Constant-From-Stella-Geometry.md) |
| 2.2.5a | Coupling Constant K | [Derivation-2.2.5a-Coupling-Constant-K.md](Phase2/Derivation-2.2.5a-Coupling-Constant-K.md) |
| 2.2.5b | QCD Bath Degrees Freedom | [Derivation-2.2.5b-QCD-Bath-Degrees-Freedom.md](Phase2/Derivation-2.2.5b-QCD-Bath-Degrees-Freedom.md) |
| 2.2.6a | QGP Entropy Production | [Derivation-2.2.6a-QGP-Entropy-Production.md](Phase2/Derivation-2.2.6a-QGP-Entropy-Production.md) |
| 2.2.6b | QCD EM Coupling Efficiency | [Derivation-2.2.6b-QCD-EM-Coupling-Efficiency.md](Phase2/Derivation-2.2.6b-QCD-EM-Coupling-Efficiency.md) |
| 2.3.1a | Chirality Propagation | [Derivation-2.3.1a-Chirality-Propagation.md](Phase2/Derivation-2.3.1a-Chirality-Propagation.md) |

---

## Phase 3

**30 files** — Mass generation

### Lemmas

| Number | Title | File |
|--------|-------|------|
| 3.1.2a | 24 Cell Two Tetrahedra Connection | [Lemma-3.1.2a-24-Cell-Two-Tetrahedra-Connection.md](Phase3/Lemma-3.1.2a-24-Cell-Two-Tetrahedra-Connection.md) |
| 3.3.1 | Boundary Site Density | [Lemma-3.3.1-Boundary-Site-Density.md](Phase3/Lemma-3.3.1-Boundary-Site-Density.md) |

### Propositions

| Number | Title | Files |
|--------|-------|-------|
| 3.1.1a | Lagrangian Form From Symmetry | [Proposition-3.1.1a-Lagrangian-Form-From-Symmetry.md](Phase3/Proposition-3.1.1a-Lagrangian-Form-From-Symmetry.md) |
| 3.1.1b | RG Fixed Point Analysis | [Proposition-3.1.1b-RG-Fixed-Point-Analysis.md](Phase3/Proposition-3.1.1b-RG-Fixed-Point-Analysis.md) |
| 3.1.1c | Geometric Coupling Formula | [Statement](Phase3/Proposition-3.1.1c-Geometric-Coupling-Formula.md), [Derivation](Phase3/Proposition-3.1.1c-Geometric-Coupling-Formula-Derivation.md) |
| 3.1.1d | WSR From CG Spectral Functions | [Proposition-3.1.1d-WSR-From-CG-Spectral-Functions.md](Phase3/Proposition-3.1.1d-WSR-From-CG-Spectral-Functions.md) |
| 3.1.2b | 4D Extension From Radial Structure | [Proposition-3.1.2b-4D-Extension-From-Radial-Structure.md](Phase3/Proposition-3.1.2b-4D-Extension-From-Radial-Structure.md) |
| 3.1.4 | Neutrino Mass Sum Bound | [Proposition-3.1.4-Neutrino-Mass-Sum-Bound.md](Phase3/Proposition-3.1.4-Neutrino-Mass-Sum-Bound.md) |

### Theorems

| Number | Title | Files |
|--------|-------|-------|
| 3.0.1 | Pressure Modulated Superposition | [Theorem-3.0.1-Pressure-Modulated-Superposition.md](Phase3/Theorem-3.0.1-Pressure-Modulated-Superposition.md) |
| 3.0.2 | Non Zero Phase Gradient | [Statement](Phase3/Theorem-3.0.2-Non-Zero-Phase-Gradient.md), [Derivation](Phase3/Theorem-3.0.2-Non-Zero-Phase-Gradient-Derivation.md), [Applications](Phase3/Theorem-3.0.2-Non-Zero-Phase-Gradient-Applications.md) |
| 3.0.3 | Temporal Fiber Structure | [Theorem-3.0.3-Temporal-Fiber-Structure.md](Phase3/Theorem-3.0.3-Temporal-Fiber-Structure.md) |
| 3.0.4 | Planck Length Phase Coherence | [Theorem-3.0.4-Planck-Length-Phase-Coherence.md](Phase3/Theorem-3.0.4-Planck-Length-Phase-Coherence.md) |
| 3.1.1 | Chiral Drag Mass Formula | [Statement](Phase3/Theorem-3.1.1-Chiral-Drag-Mass-Formula.md), [Derivation](Phase3/Theorem-3.1.1-Chiral-Drag-Mass-Formula-Derivation.md), [Applications](Phase3/Theorem-3.1.1-Chiral-Drag-Mass-Formula-Applications.md) |
| 3.1.2 | Mass Hierarchy From Geometry | [Statement](Phase3/Theorem-3.1.2-Mass-Hierarchy-From-Geometry.md), [Derivation](Phase3/Theorem-3.1.2-Mass-Hierarchy-From-Geometry-Derivation.md), [Applications](Phase3/Theorem-3.1.2-Mass-Hierarchy-From-Geometry-Applications.md) |
| 3.1.5 | Majorana Scale From Geometry | [Theorem-3.1.5-Majorana-Scale-From-Geometry.md](Phase3/Theorem-3.1.5-Majorana-Scale-From-Geometry.md) |
| 3.2.1 | Low Energy Equivalence | [Statement](Phase3/Theorem-3.2.1-Low-Energy-Equivalence.md), [Derivation](Phase3/Theorem-3.2.1-Low-Energy-Equivalence-Derivation.md), [Applications](Phase3/Theorem-3.2.1-Low-Energy-Equivalence-Applications.md) |
| 3.2.2 | High Energy Deviations | [Theorem-3.2.2-High-Energy-Deviations.md](Phase3/Theorem-3.2.2-High-Energy-Deviations.md) |

### Corollarys

| Number | Title | File |
|--------|-------|------|
| 3.1.3 | Massless Right Handed Neutrinos | [Corollary-3.1.3-Massless-Right-Handed-Neutrinos.md](Phase3/Corollary-3.1.3-Massless-Right-Handed-Neutrinos.md) |

### Extensions

| Number | Title | File |
|--------|-------|------|
| 3.1.2b | Complete Wolfenstein Parameters | [Extension-3.1.2b-Complete-Wolfenstein-Parameters.md](Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md) |
| 3.1.2c | Instanton Overlap Derivation | [Extension-3.1.2c-Instanton-Overlap-Derivation.md](Phase3/Extension-3.1.2c-Instanton-Overlap-Derivation.md) |
| 3.1.2d | Complete PMNS Parameters | [Extension-3.1.2d-Complete-PMNS-Parameters.md](Phase3/Extension-3.1.2d-Complete-PMNS-Parameters.md) |

---

## Phase 4

**20 files** — Topological solitons

### Definitions

| Number | Title | File |
|--------|-------|------|
| 4.1.5 | Soliton Effective Potential | [Definition-4.1.5-Soliton-Effective-Potential.md](Phase4/Definition-4.1.5-Soliton-Effective-Potential.md) |
| 4.3.1 | W-Sector Field Theory | [Definition-4.3.1-W-Sector-Field-Theory.md](Phase4/Definition-4.3.1-W-Sector-Field-Theory.md) |

### Propositions

| Number | Title | File |
|--------|-------|------|
| 4.2.4 | Sphaleron Rate From CG Topology | [Proposition-4.2.4-Sphaleron-Rate-From-CG-Topology.md](Phase4/Proposition-4.2.4-Sphaleron-Rate-From-CG-Topology.md) |
| 4.3.3 | W-Soliton Cosmological Abundance | [Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md](Phase4/Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md) |
| 4.3.4 | W-Soliton Structure Formation | [Proposition-4.3.4-W-Soliton-Structure-Formation.md](Phase4/Proposition-4.3.4-W-Soliton-Structure-Formation.md) |
| 4.3.5 | Skyrme Parameter from Pressure-Kurtosis Geometry | [Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md](Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md) |

### Theorems

| Number | Title | Files |
|--------|-------|-------|
| 4.1.1 | Existence of Solitons | [Theorem-4.1.1-Existence-of-Solitons.md](Phase4/Theorem-4.1.1-Existence-of-Solitons.md) |
| 4.1.2 | Soliton Mass Spectrum | [Theorem-4.1.2-Soliton-Mass-Spectrum.md](Phase4/Theorem-4.1.2-Soliton-Mass-Spectrum.md) |
| 4.1.3 | Fermion Number Topology | [Theorem-4.1.3-Fermion-Number-Topology.md](Phase4/Theorem-4.1.3-Fermion-Number-Topology.md) |
| 4.1.4 | Dynamic Suspension Equilibrium | [Statement](Phase4/Theorem-4.1.4-Dynamic-Suspension-Equilibrium.md), [Derivation](Phase4/Theorem-4.1.4-Dynamic-Suspension-Equilibrium-Derivation.md), [Applications](Phase4/Theorem-4.1.4-Dynamic-Suspension-Equilibrium-Applications.md) |
| 4.2.1 | Chiral Bias Soliton Formation | [Statement](Phase4/Theorem-4.2.1-Chiral-Bias-Soliton-Formation.md), [Derivation](Phase4/Theorem-4.2.1-Chiral-Bias-Soliton-Formation-Derivation.md), [Applications](Phase4/Theorem-4.2.1-Chiral-Bias-Soliton-Formation-Applications.md) |
| 4.2.2 | Sakharov Conditions | [Statement](Phase4/Theorem-4.2.2-Sakharov-Conditions.md), [Derivation](Phase4/Theorem-4.2.2-Sakharov-Conditions-Derivation.md), [Applications](Phase4/Theorem-4.2.2-Sakharov-Conditions-Applications.md) |
| 4.2.3 | First Order Phase Transition | [Theorem-4.2.3-First-Order-Phase-Transition.md](Phase4/Theorem-4.2.3-First-Order-Phase-Transition.md) |
| 4.3.2 | W-Soliton Existence and Properties | [Theorem-4.3.2-W-Soliton-Existence-And-Properties.md](Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md) |

---

## Phase 5

**44 files** — Emergent spacetime and gravity

### Lemmas

| Number | Title | File |
|--------|-------|------|
| 5.2.3b.1 | Lattice Spacing Coefficient | [Lemma-5.2.3b.1-Lattice-Spacing-Coefficient.md](Phase5/Lemma-5.2.3b.1-Lattice-Spacing-Coefficient.md) |
| 5.2.3b.2 | Z3 Discretization Mechanism | [Lemma-5.2.3b.2-Z3-Discretization-Mechanism.md](Phase5/Lemma-5.2.3b.2-Z3-Discretization-Mechanism.md) |
| 5.4.1a | Maximum Curvature Bound | [Lemma-5.4.1a-Maximum-Curvature-Bound.md](Phase5/Lemma-5.4.1a-Maximum-Curvature-Bound.md) |

### Propositions

| Number | Title | File |
|--------|-------|------|
| 5.1.2a | Matter Density From Geometry | [Proposition-5.1.2a-Matter-Density-From-Geometry.md](Phase5/Proposition-5.1.2a-Matter-Density-From-Geometry.md) |
| 5.1.2b | Precision Cosmological Densities | [Proposition-5.1.2b-Precision-Cosmological-Densities.md](Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) |
| 5.2.1b | Einstein Equations From Fixed Point Uniqueness | [Proposition-5.2.1b-Einstein-Equations-From-Fixed-Point-Uniqueness.md](Phase5/Proposition-5.2.1b-Einstein-Equations-From-Fixed-Point-Uniqueness.md) |
| 5.2.3a | Local Thermodynamic Equilibrium | [Proposition-5.2.3a-Local-Thermodynamic-Equilibrium.md](Phase5/Proposition-5.2.3a-Local-Thermodynamic-Equilibrium.md) |
| 5.2.3b | FCC Lattice Entropy | [Proposition-5.2.3b-FCC-Lattice-Entropy.md](Phase5/Proposition-5.2.3b-FCC-Lattice-Entropy.md) |
| 5.2.4a | Induced Gravity From Chiral One Loop | [Proposition-5.2.4a-Induced-Gravity-From-Chiral-One-Loop.md](Phase5/Proposition-5.2.4a-Induced-Gravity-From-Chiral-One-Loop.md) |
| 5.2.4b | Spin 2 From Stress Energy Conservation | [Proposition-5.2.4b-Spin-2-From-Stress-Energy-Conservation.md](Phase5/Proposition-5.2.4b-Spin-2-From-Stress-Energy-Conservation.md) |
| 5.2.4c | Tensor Rank From Derivative Structure | [Proposition-5.2.4c-Tensor-Rank-From-Derivative-Structure.md](Phase5/Proposition-5.2.4c-Tensor-Rank-From-Derivative-Structure.md) |
| 5.2.4d | Geometric Higher Spin Exclusion | [Proposition-5.2.4d-Geometric-Higher-Spin-Exclusion.md](Phase5/Proposition-5.2.4d-Geometric-Higher-Spin-Exclusion.md) |
| 5.2.5e | Holographic Self-Encoding Scale Invariance | [Proposition-5.2.5e-Holographic-Self-Encoding-Scale-Invariance.md](Phase5/Proposition-5.2.5e-Holographic-Self-Encoding-Scale-Invariance.md) |

### Theorems

| Number | Title | Files |
|--------|-------|-------|
| 5.1.1 | Stress Energy Tensor | [Theorem-5.1.1-Stress-Energy-Tensor.md](Phase5/Theorem-5.1.1-Stress-Energy-Tensor.md) |
| 5.1.2 | Vacuum Energy Density | [Statement](Phase5/Theorem-5.1.2-Vacuum-Energy-Density.md), [Derivation](Phase5/Theorem-5.1.2-Vacuum-Energy-Density-Derivation.md), [Applications](Phase5/Theorem-5.1.2-Vacuum-Energy-Density-Applications.md) |
| 5.2.0 | Wick Rotation Validity | [Theorem-5.2.0-Wick-Rotation-Validity.md](Phase5/Theorem-5.2.0-Wick-Rotation-Validity.md) |
| 5.2.1 | Emergent Metric | [Statement](Phase5/Theorem-5.2.1-Emergent-Metric.md), [Derivation](Phase5/Theorem-5.2.1-Emergent-Metric-Derivation.md), [Applications](Phase5/Theorem-5.2.1-Emergent-Metric-Applications.md) |
| 5.2.2 | Pre Geometric Cosmic Coherence | [Theorem-5.2.2-Pre-Geometric-Cosmic-Coherence.md](Phase5/Theorem-5.2.2-Pre-Geometric-Cosmic-Coherence.md) |
| 5.2.3 | Einstein Equations Thermodynamic | [Statement](Phase5/Theorem-5.2.3-Einstein-Equations-Thermodynamic.md), [Derivation](Phase5/Theorem-5.2.3-Einstein-Equations-Thermodynamic-Derivation.md), [Applications](Phase5/Theorem-5.2.3-Einstein-Equations-Thermodynamic-Applications.md) |
| 5.2.4 | Newtons Constant Chiral Parameters | [Statement](Phase5/Theorem-5.2.4-Newtons-Constant-Chiral-Parameters.md), [Derivation](Phase5/Theorem-5.2.4-Newtons-Constant-Chiral-Parameters-Derivation.md), [Applications](Phase5/Theorem-5.2.4-Newtons-Constant-Chiral-Parameters-Applications.md) |
| 5.2.5 | Bekenstein Hawking Coefficient | [Statement](Phase5/Theorem-5.2.5-Bekenstein-Hawking-Coefficient.md), [Derivation](Phase5/Theorem-5.2.5-Bekenstein-Hawking-Coefficient-Derivation.md), [Applications](Phase5/Theorem-5.2.5-Bekenstein-Hawking-Coefficient-Applications.md) |
| 5.2.6 | Planck Mass Emergence | [Statement](Phase5/Theorem-5.2.6-Planck-Mass-Emergence.md), [Derivation](Phase5/Theorem-5.2.6-Planck-Mass-Emergence-Derivation.md), [Applications](Phase5/Theorem-5.2.6-Planck-Mass-Emergence-Applications.md) |
| 5.2.7 | Diffeomorphism Emergence | [Theorem-5.2.7-Diffeomorphism-Emergence.md](Phase5/Theorem-5.2.7-Diffeomorphism-Emergence.md) |
| 5.3.1 | Torsion From Chiral Current | [Theorem-5.3.1-Torsion-From-Chiral-Current.md](Phase5/Theorem-5.3.1-Torsion-From-Chiral-Current.md) |
| 5.3.2 | Spin Orbit Coupling | [Statement](Phase5/Theorem-5.3.2-Spin-Orbit-Coupling.md), [Derivation](Phase5/Theorem-5.3.2-Spin-Orbit-Coupling-Derivation.md), [Applications](Phase5/Theorem-5.3.2-Spin-Orbit-Coupling-Applications.md) |
| 5.4.1 | Singularity Resolution Emergent Gravity | [Statement](Phase5/Theorem-5.4.1-Singularity-Resolution-Emergent-Gravity.md), [Derivation](Phase5/Theorem-5.4.1-Singularity-Resolution-Emergent-Gravity-Derivation.md), [Applications](Phase5/Theorem-5.4.1-Singularity-Resolution-Emergent-Gravity-Applications.md) |

### Derivations

| Number | Title | File |
|--------|-------|------|
| 5.2.5a | Surface Gravity | [Derivation-5.2.5a-Surface-Gravity.md](Phase5/Derivation-5.2.5a-Surface-Gravity.md) |
| 5.2.5b | Hawking Temperature | [Derivation-5.2.5b-Hawking-Temperature.md](Phase5/Derivation-5.2.5b-Hawking-Temperature.md) |
| 5.2.5c | First Law and Entropy | [Derivation-5.2.5c-First-Law-and-Entropy.md](Phase5/Derivation-5.2.5c-First-Law-and-Entropy.md) |

---

## Phase 6

**12 files** — Scattering theory

### Propositions

| Number | Title | File |
|--------|-------|------|
| 6.3.1 | One Loop QCD Corrections | [Proposition-6.3.1-One-Loop-QCD-Corrections.md](Phase6/Proposition-6.3.1-One-Loop-QCD-Corrections.md) |
| 6.3.2 | Decay Widths | [Proposition-6.3.2-Decay-Widths.md](Phase6/Proposition-6.3.2-Decay-Widths.md) |
| 6.3.3 | Higgs Diphoton Decay | [Proposition-6.3.3-Higgs-Diphoton-Decay.md](Phase6/Proposition-6.3.3-Higgs-Diphoton-Decay.md) |
| 6.3.4 | Higgs Z Gamma Decay | [Proposition-6.3.4-Higgs-Z-Gamma-Decay.md](Phase6/Proposition-6.3.4-Higgs-Z-Gamma-Decay.md) |
| 6.4.1 | Hadronization Framework | [Proposition-6.4.1-Hadronization-Framework.md](Phase6/Proposition-6.4.1-Hadronization-Framework.md) |
| 6.5.1 | LHC Cross Section Predictions | [Proposition-6.5.1-LHC-Cross-Section-Predictions.md](Phase6/Proposition-6.5.1-LHC-Cross-Section-Predictions.md) |

### Theorems

| Number | Title | File |
|--------|-------|------|
| 6.1.1 | Complete Feynman Rules | [Theorem-6.1.1-Complete-Feynman-Rules.md](Phase6/Theorem-6.1.1-Complete-Feynman-Rules.md) |
| 6.2.1 | Tree Level Scattering Amplitudes | [Theorem-6.2.1-Tree-Level-Scattering-Amplitudes.md](Phase6/Theorem-6.2.1-Tree-Level-Scattering-Amplitudes.md) |
| 6.2.2 | Helicity Amplitudes Spinor Helicity Formalism | [Theorem-6.2.2-Helicity-Amplitudes-Spinor-Helicity-Formalism.md](Phase6/Theorem-6.2.2-Helicity-Amplitudes-Spinor-Helicity-Formalism.md) |
| 6.6.1 | Electroweak Scattering | [Theorem-6.6.1-Electroweak-Scattering.md](Phase6/Theorem-6.6.1-Electroweak-Scattering.md) |
| 6.7.1 | Electroweak Gauge Fields From 24 Cell | [Theorem-6.7.1-Electroweak-Gauge-Fields-From-24-Cell.md](Phase6/Theorem-6.7.1-Electroweak-Gauge-Fields-From-24-Cell.md) |
| 6.7.2 | Electroweak Symmetry Breaking Dynamics | [Theorem-6.7.2-Electroweak-Symmetry-Breaking-Dynamics.md](Phase6/Theorem-6.7.2-Electroweak-Symmetry-Breaking-Dynamics.md) |

---

## Phase 7

**111 files** — Renormalization and consistency

### Propositions

| Number | Title | Files |
|--------|-------|-------|
| 7.3.2a | Pressure Balance Asymptotic Freedom | [Proposition-7.3.2a-Pressure-Balance-Asymptotic-Freedom.md](Phase7/Proposition-7.3.2a-Pressure-Balance-Asymptotic-Freedom.md) |
| 7.4.3 | FCC Lattice Perturbation Theory | [Statement](Phase7/Proposition-7.4.3-FCC-Lattice-Perturbation-Theory.md), [Derivation](Phase7/Proposition-7.4.3-FCC-Lattice-Perturbation-Theory-Derivation.md), [Applications](Phase7/Proposition-7.4.3-FCC-Lattice-Perturbation-Theory-Applications.md) |
| 7.4.4 | Scaling Window FCC | [Statement](Phase7/Proposition-7.4.4-Scaling-Window-FCC.md), [Derivation](Phase7/Proposition-7.4.4-Scaling-Window-FCC-Derivation.md), [Applications](Phase7/Proposition-7.4.4-Scaling-Window-FCC-Applications.md) |
| 7.4.4a | Exact Wilson Loop FCC | [Proposition-7.4.4a-Exact-Wilson-Loop-FCC.md](Phase7/Proposition-7.4.4a-Exact-Wilson-Loop-FCC.md) |
| 7.5.1 | Symanzik Effective Theory FCC | [Statement](Phase7/Proposition-7.5.1-Symanzik-Effective-Theory-FCC.md), [Derivation](Phase7/Proposition-7.5.1-Symanzik-Effective-Theory-FCC-Derivation.md), [Applications](Phase7/Proposition-7.5.1-Symanzik-Effective-Theory-FCC-Applications.md) |
| 7.6.1 | FCC Averaging Kernel | [Statement](Phase7/Proposition-7.6.1-FCC-Averaging-Kernel.md), [Derivation](Phase7/Proposition-7.6.1-FCC-Averaging-Kernel-Derivation.md), [Applications](Phase7/Proposition-7.6.1-FCC-Averaging-Kernel-Applications.md) |
| 7.6.2 | FCC Propagator Bounds | [Statement](Phase7/Proposition-7.6.2-FCC-Propagator-Bounds.md), [Derivation](Phase7/Proposition-7.6.2-FCC-Propagator-Bounds-Derivation.md), [Applications](Phase7/Proposition-7.6.2-FCC-Propagator-Bounds-Applications.md) |
| 7.6.3 | Regular Configurations Variational Problem | [Statement](Phase7/Proposition-7.6.3-Regular-Configurations-Variational-Problem.md), [Derivation](Phase7/Proposition-7.6.3-Regular-Configurations-Variational-Problem-Derivation.md), [Applications](Phase7/Proposition-7.6.3-Regular-Configurations-Variational-Problem-Applications.md) |
| 7.6.4 | Large Field Estimates | [Statement](Phase7/Proposition-7.6.4-Large-Field-Estimates.md), [Derivation](Phase7/Proposition-7.6.4-Large-Field-Estimates-Derivation.md), [Applications](Phase7/Proposition-7.6.4-Large-Field-Estimates-Applications.md) |
| 7.6.6 | Correlation Decay Weak Coupling D=4 | [Statement](Phase7/Proposition-7.6.6-Correlation-Decay-Weak-Coupling-D4.md), [Derivation](Phase7/Proposition-7.6.6-Correlation-Decay-Weak-Coupling-D4-Derivation.md), [Applications](Phase7/Proposition-7.6.6-Correlation-Decay-Weak-Coupling-D4-Applications.md) |
| 7.6.9 | Scaling Window Mass Ratio Stabilization D=4 | [Statement](Phase7/Proposition-7.6.9-Scaling-Window-Mass-Ratio-Stabilization-D4.md), [Derivation](Phase7/Proposition-7.6.9-Scaling-Window-Mass-Ratio-Stabilization-D4-Derivation.md), [Applications](Phase7/Proposition-7.6.9-Scaling-Window-Mass-Ratio-Stabilization-D4-Applications.md) |

### Theorems

| Number | Title | Files |
|--------|-------|-------|
| 7.1.1 | Power Counting | [Statement](Phase7/Theorem-7.1.1-Power-Counting.md), [Derivation](Phase7/Theorem-7.1.1-Power-Counting-Derivation.md), [Applications](Phase7/Theorem-7.1.1-Power-Counting-Applications.md) |
| 7.2.1 | S Matrix Unitarity | [Theorem-7.2.1-S-Matrix-Unitarity.md](Phase7/Theorem-7.2.1-S-Matrix-Unitarity.md) |
| 7.3.1 | UV Completeness Emergent Gravity | [Statement](Phase7/Theorem-7.3.1-UV-Completeness-Emergent-Gravity.md), [Derivation](Phase7/Theorem-7.3.1-UV-Completeness-Emergent-Gravity-Derivation.md), [Applications](Phase7/Theorem-7.3.1-UV-Completeness-Emergent-Gravity-Applications.md) |
| 7.3.2 | Asymptotic Freedom | [Statement](Phase7/Theorem-7.3.2-Asymptotic-Freedom.md), [Derivation](Phase7/Theorem-7.3.2-Asymptotic-Freedom-Derivation.md), [Applications](Phase7/Theorem-7.3.2-Asymptotic-Freedom-Applications.md), [Two Loop Calculation](Phase7/Theorem-7.3.2-Two-Loop-Calculation.md) |
| 7.3.3 | Beta Function Structure | [Statement](Phase7/Theorem-7.3.3-Beta-Function-Structure.md), [Derivation](Phase7/Theorem-7.3.3-Beta-Function-Structure-Derivation.md), [Applications](Phase7/Theorem-7.3.3-Beta-Function-Structure-Applications.md) |
| 7.4.1 | Reflection Positivity FCC | [Statement](Phase7/Theorem-7.4.1-Reflection-Positivity-FCC.md), [Derivation](Phase7/Theorem-7.4.1-Reflection-Positivity-FCC-Derivation.md), [Applications](Phase7/Theorem-7.4.1-Reflection-Positivity-FCC-Applications.md) |
| 7.4.2 | Mass Gap Thermodynamic Limit FCC | [Statement](Phase7/Theorem-7.4.2-Mass-Gap-Thermodynamic-Limit-FCC.md), [Derivation](Phase7/Theorem-7.4.2-Mass-Gap-Thermodynamic-Limit-FCC-Derivation.md), [Applications](Phase7/Theorem-7.4.2-Mass-Gap-Thermodynamic-Limit-FCC-Applications.md) |
| 7.4.5 | Continuum Mass Gap FCC | [Statement](Phase7/Theorem-7.4.5-Continuum-Mass-Gap-FCC.md), [Derivation](Phase7/Theorem-7.4.5-Continuum-Mass-Gap-FCC-Derivation.md), [Applications](Phase7/Theorem-7.4.5-Continuum-Mass-Gap-FCC-Applications.md) |
| 7.4.6 | OS Axioms CG Yang Mills | [Statement](Phase7/Theorem-7.4.6-OS-Axioms-CG-Yang-Mills.md), [Derivation](Phase7/Theorem-7.4.6-OS-Axioms-CG-Yang-Mills-Derivation.md), [Applications](Phase7/Theorem-7.4.6-OS-Axioms-CG-Yang-Mills-Applications.md) |
| 7.4.7 | CG Yang Mills Mass Gap | [Statement](Phase7/Theorem-7.4.7-CG-Yang-Mills-Mass-Gap.md), [Derivation](Phase7/Theorem-7.4.7-CG-Yang-Mills-Mass-Gap-Derivation.md), [Applications](Phase7/Theorem-7.4.7-CG-Yang-Mills-Mass-Gap-Applications.md) |
| 7.5.2 | Perturbative Universality FCC | [Statement](Phase7/Theorem-7.5.2-Perturbative-Universality-FCC.md), [Derivation](Phase7/Theorem-7.5.2-Perturbative-Universality-FCC-Derivation.md), [Applications](Phase7/Theorem-7.5.2-Perturbative-Universality-FCC-Applications.md) |
| 7.5.3 | Bulk Transition Termination FCC | [Statement](Phase7/Theorem-7.5.3-Bulk-Transition-Termination-FCC.md), [Derivation](Phase7/Theorem-7.5.3-Bulk-Transition-Termination-FCC-Derivation.md), [Applications](Phase7/Theorem-7.5.3-Bulk-Transition-Termination-FCC-Applications.md) |
| 7.5.4 | Non-Perturbative Universality FCC | [Statement](Phase7/Theorem-7.5.4-Non-Perturbative-Universality-FCC.md), [Derivation](Phase7/Theorem-7.5.4-Non-Perturbative-Universality-FCC-Derivation.md), [Applications](Phase7/Theorem-7.5.4-Non-Perturbative-Universality-FCC-Applications.md) |
| 7.6.5 | Small Field UV Stability | [Statement](Phase7/Theorem-7.6.5-Small-Field-UV-Stability.md), [Derivation](Phase7/Theorem-7.6.5-Small-Field-UV-Stability-Derivation.md), [Applications](Phase7/Theorem-7.6.5-Small-Field-UV-Stability-Applications.md) |
| 7.6.7 | Infrared Coercivity Exact Mass Gap | [Statement](Phase7/Theorem-7.6.7-Infrared-Coercivity-Exact-Mass-Gap.md), [Derivation](Phase7/Theorem-7.6.7-Infrared-Coercivity-Exact-Mass-Gap-Derivation.md), [Applications](Phase7/Theorem-7.6.7-Infrared-Coercivity-Exact-Mass-Gap-Applications.md) |
| 7.6.8 | Effective Action Convergence Multi Scale RG D=4 | [Statement](Phase7/Theorem-7.6.8-Effective-Action-Convergence-Multi-Scale-RG-D4.md), [Derivation](Phase7/Theorem-7.6.8-Effective-Action-Convergence-Multi-Scale-RG-D4-Derivation.md), [Applications](Phase7/Theorem-7.6.8-Effective-Action-Convergence-Multi-Scale-RG-D4-Applications.md) |
| 7.6.10 | Constructive SU(3) Yang Mills Mass Gap D=4 | [Statement](Phase7/Theorem-7.6.10-Constructive-SU3-Yang-Mills-Mass-Gap-D4.md), [Derivation](Phase7/Theorem-7.6.10-Constructive-SU3-Yang-Mills-Mass-Gap-D4-Derivation.md), [Applications](Phase7/Theorem-7.6.10-Constructive-SU3-Yang-Mills-Mass-Gap-D4-Applications.md) |
| 7.7.1 | Unconditional OS FOS Axioms SU(3) Yang Mills | [Theorem-7.7.1-Unconditional-OS-FOS-Axioms-SU3-Yang-Mills.md](Phase7/Theorem-7.7.1-Unconditional-OS-FOS-Axioms-SU3-Yang-Mills.md) |
| 7.7.2 | Wightman Reconstruction Mass Gap SU(3) Yang Mills | [Theorem-7.7.2-Wightman-Reconstruction-Mass-Gap-SU3-Yang-Mills.md](Phase7/Theorem-7.7.2-Wightman-Reconstruction-Mass-Gap-SU3-Yang-Mills.md) |
| 7.7.3 | Quantitative Mass Gap Lower Bound SU(3) Yang Mills | [Theorem-7.7.3-Quantitative-Mass-Gap-Lower-Bound-SU3-Yang-Mills.md](Phase7/Theorem-7.7.3-Quantitative-Mass-Gap-Lower-Bound-SU3-Yang-Mills.md) |
| 7.7.4 | Yang Mills Mass Gap General Compact Simple G | [Theorem-7.7.4-Yang-Mills-Mass-Gap-General-Compact-Simple-G.md](Phase7/Theorem-7.7.4-Yang-Mills-Mass-Gap-General-Compact-Simple-G.md) |
| 7.7.5 | Yang Mills Mass Gap Complete Proof | [Statement](Phase7/Theorem-7.7.5-Yang-Mills-Mass-Gap-Complete-Proof.md), [Derivation](Phase7/Theorem-7.7.5-Yang-Mills-Mass-Gap-Complete-Proof-Derivation.md), [Applications](Phase7/Theorem-7.7.5-Yang-Mills-Mass-Gap-Complete-Proof-Applications.md) |
| 7.8.1 | Exceptional Group Glueball Predictions | [Statement](Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions.md), [Derivation](Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions-Derivation.md), [Applications](Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions-Applications.md) |
| 7.8.2 | Framework-Internal Glueball Mass Ratio | [Statement](Phase7/Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio.md), [Derivation](Phase7/Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Derivation.md), [Applications](Phase7/Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Applications.md) |
| 7.8.3 | Bethe-Salpeter Glueball Mass Ratio | [Statement](Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md), [Derivation](Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio-Derivation.md), [Applications](Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio-Applications.md) |
| 7.8.4 | V-Scheme BLM Glueball Mass Ratio | [Statement](Phase7/Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio.md), [Derivation](Phase7/Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Derivation.md), [Applications](Phase7/Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio-Applications.md) |
| 7.8.5 | Explicit Crossover Mass Gap Computation | [Statement](Phase7/Proposition-7.8.5-Explicit-Crossover-Mass-Gap-Computation.md), [Derivation](Phase7/Proposition-7.8.5-Explicit-Crossover-Mass-Gap-Computation-Derivation.md), [Applications](Phase7/Proposition-7.8.5-Explicit-Crossover-Mass-Gap-Computation-Applications.md) |
| 7.8.6 | Full Two-Gluon Glueball Spectrum | [Statement](Phase7/Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum.md), [Derivation](Phase7/Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Derivation.md), [Applications](Phase7/Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum-Applications.md) |
| 7.8.7 | Three-Gluon Glueball Spectrum | [Statement](Phase7/Proposition-7.8.7-Three-Gluon-Glueball-Spectrum.md), [Derivation](Phase7/Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Derivation.md), [Applications](Phase7/Proposition-7.8.7-Three-Gluon-Glueball-Spectrum-Applications.md) · [Lean 4](../../lean/ChiralGeometrogenesis/Phase7/Proposition_7_8_7.lean) |
| 7.9.1 | Mass Gap Persistence with Dynamical Fermions | [Statement](Phase7/Proposition-7.9.1-Mass-Gap-Dynamical-Fermions.md), [Derivation](Phase7/Proposition-7.9.1-Mass-Gap-Dynamical-Fermions-Derivation.md), [Applications](Phase7/Proposition-7.9.1-Mass-Gap-Dynamical-Fermions-Applications.md) |

---

## Phase 8

**18 files** — Predictions and tests

### Propositions

| Number | Title | Files |
|--------|-------|-------|
| 8.4.4 | Atmospheric Angle Correction | [Proposition-8.4.4-Atmospheric-Angle-Correction.md](Phase8/Proposition-8.4.4-Atmospheric-Angle-Correction.md) |
| 8.5.1 | Lattice QCD Heavy Ion Predictions | [Statement](Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md), [Derivation](Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions-Derivation.md), [Applications](Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions-Applications.md) |

### Derivations

| Number | Title | File |
|--------|-------|------|
| 8.1.3 | Three Generation Necessity | [Derivation-8.1.3-Three-Generation-Necessity.md](Phase8/Derivation-8.1.3-Three-Generation-Necessity.md) |
| 8.4.2 | Theta13 First Principles | [Derivation-8.4.2-Theta13-First-Principles.md](Phase8/Derivation-8.4.2-Theta13-First-Principles.md) |
| 8.4.3 | Euler Characteristic Signature | [Derivation-8.4.3-Euler-Characteristic-Signature.md](Phase8/Derivation-8.4.3-Euler-Characteristic-Signature.md) |

### Predictions

| Number | Title | Files |
|--------|-------|-------|
| 8.2.1 | Experimental Proposal | [Statement](Phase8/Prediction-8.2.1-Experimental-Proposal.md), [Derivation](Phase8/Prediction-8.2.1-QGP-Phase-Coherence-Derivation.md), [Applications](Phase8/Prediction-8.2.1-QGP-Phase-Coherence-Applications.md), [QGP Phase Coherence](Phase8/Prediction-8.2.1-QGP-Phase-Coherence.md) |
| 8.2.3 | Pre Geometric Relics | [Statement](Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md), [Derivation](Phase8/Prediction-8.2.3-Pre-Geometric-Relics-Derivation.md), [Applications](Phase8/Prediction-8.2.3-Pre-Geometric-Relics-Applications.md) |
| 8.2.4 | W-Sector Gravitational Waves | [Prediction-8.2.4-W-Sector-Gravitational-Waves.md](Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md) |
| 8.3.1 | W Condensate Dark Matter | [Prediction-8.3.1-W-Condensate-Dark-Matter.md](Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md) |
| 8.4.1 | Proton Decay From Geometric GUT | [Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md](Phase8/Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md) |

### Proofs

| Number | Title | File |
|--------|-------|------|
| 8.1.3b | Topological Generation Count | [Proof-8.1.3b-Topological-Generation-Count.md](Phase8/Proof-8.1.3b-Topological-Generation-Count.md) |

---

## Reference

**12 files** — Constants, techniques, protocols

| Title | File |
|-------|------|
| **Predictions Master Reference** | [**Predictions-Master-Reference.md**](reference/Predictions-Master-Reference.md) |
| Challenge Resolutions | [Challenge-Resolutions.md](reference/Challenge-Resolutions.md) |
| Mathematical Techniques Reference | [Mathematical-Techniques-Reference.md](reference/Mathematical-Techniques-Reference.md) |
| Physical Constants and Data | [Physical-Constants-and-Data.md](reference/Physical-Constants-and-Data.md) |
| Proof Templates | [Proof-Templates.md](reference/Proof-Templates.md) |
| Unification Points Details | [Unification-Points-Details.md](reference/Unification-Points-Details.md) |
| Verification Protocol Details | [Verification-Protocol-Details.md](reference/Verification-Protocol-Details.md) |
| cosmological constants | [cosmological-constants.md](reference/cosmological-constants.md) |
| coupling constants | [coupling-constants.md](reference/coupling-constants.md) |
| notation glossary | [notation-glossary.md](reference/notation-glossary.md) |
| pdg particle data | [pdg-particle-data.md](reference/pdg-particle-data.md) |
| sources | [sources.md](reference/sources.md) |

---

## Supporting

**72 files** — Research and analysis documents

| Title | File |
|-------|------|
| Alpha GUT Derivation Research Summary | [Alpha-GUT-Derivation-Research-Summary.md](supporting/Alpha-GUT-Derivation-Research-Summary.md) |
| Analysis 1 dim adj Derivation Paths | [Analysis-1-dim-adj-Derivation-Paths.md](supporting/Analysis-1-dim-adj-Derivation-Paths.md) |
| Analysis 1 dim adj Path Integral Rigorous Derivation | [Analysis-1-dim-adj-Path-Integral-Rigorous-Derivation.md](supporting/Analysis-1-dim-adj-Path-Integral-Rigorous-Derivation.md) |
| Analysis 1 dim adj Rigorous Derivation | [Analysis-1-dim-adj-Rigorous-Derivation.md](supporting/Analysis-1-dim-adj-Rigorous-Derivation.md) |
| Analysis 2pi2 Normalization Investigation | [Analysis-2pi2-Normalization-Investigation.md](supporting/Analysis-2pi2-Normalization-Investigation.md) |
| Analysis 5 Equals 3 Plus 2 Decomposition | [Analysis-5-Equals-3-Plus-2-Decomposition.md](supporting/Analysis-5-Equals-3-Plus-2-Decomposition.md) |
| Analysis A Theorem Extension CFT To Massive Flows | [Analysis-A-Theorem-Extension-CFT-To-Massive-Flows.md](supporting/Analysis-A-Theorem-Extension-CFT-To-Massive-Flows.md) |
| Analysis A Theorem Extension To Massive IR | [Analysis-A-Theorem-Extension-To-Massive-IR.md](supporting/Analysis-A-Theorem-Extension-To-Massive-IR.md) |
| Analysis Delta a Beyond Free Field | [Analysis-Delta-a-Beyond-Free-Field.md](supporting/Analysis-Delta-a-Beyond-Free-Field.md) |
| Analysis EW Specificity Why Formula Fails For QCD | [Analysis-EW-Specificity-Why-Formula-Fails-For-QCD.md](supporting/Analysis-EW-Specificity-Why-Formula-Fails-For-QCD.md) |
| Analysis Exp Functional Form Derivation | [Analysis-Exp-Functional-Form-Derivation.md](supporting/Analysis-Exp-Functional-Form-Derivation.md) |
| Analysis Experimental Discrimination 5 Equals 3 Plus 2 | [Analysis-Experimental-Discrimination-5-Equals-3-Plus-2.md](supporting/Analysis-Experimental-Discrimination-5-Equals-3-Plus-2.md) |
| Analysis Higgs Quartic From Vertex Counting | [Analysis-Higgs-Quartic-From-Vertex-Counting.md](supporting/Analysis-Higgs-Quartic-From-Vertex-Counting.md) |
| Analysis Independent Falsifiable Predictions | [Analysis-Independent-Falsifiable-Predictions.md](supporting/Analysis-Independent-Falsifiable-Predictions.md) |
| Analysis Lambda QCD Correction Uncertainty | [Analysis-Lambda-QCD-Correction-Uncertainty.md](supporting/Analysis-Lambda-QCD-Correction-Uncertainty.md) |
| Analysis PMNS 5 Copy Structure Connection | [Analysis-PMNS-5-Copy-Structure-Connection.md](supporting/Analysis-PMNS-5-Copy-Structure-Connection.md) |
| Analysis Quaternionic Structure Icosian Group | [Analysis-Quaternionic-Structure-Icosian-Group.md](supporting/Analysis-Quaternionic-Structure-Icosian-Group.md) |
| Analysis Unified Geometric Mismatch Resolution | [Analysis-Unified-Geometric-Mismatch-Resolution.md](supporting/Analysis-Unified-Geometric-Mismatch-Resolution.md) |
| Color Constraints Necessity Conclusion | [Color-Constraints-Necessity-Conclusion.md](supporting/Color-Constraints-Necessity-Conclusion.md) |
| Color Constraints Necessity Research Plan | [Color-Constraints-Necessity-Research-Plan.md](supporting/Color-Constraints-Necessity-Research-Plan.md) |
| Configuration Space Topology Analysis | [Configuration-Space-Topology-Analysis.md](supporting/Configuration-Space-Topology-Analysis.md) |
| Derivation Attempt 1 dim adj From Goldstone Theorem | [Derivation-Attempt-1-dim-adj-From-Goldstone-Theorem.md](supporting/Derivation-Attempt-1-dim-adj-From-Goldstone-Theorem.md) |
| Derivation D4 Triality A4 Irreps Connection | [Derivation-D4-Triality-A4-Irreps-Connection.md](supporting/Derivation-D4-Triality-A4-Irreps-Connection.md) |
| Derivation Heavy Generation Predictions | [Derivation-Heavy-Generation-Predictions.md](supporting/Derivation-Heavy-Generation-Predictions.md) |
| Derivation Sin72 Angular Factor Explicit | [Derivation-Sin72-Angular-Factor-Explicit.md](supporting/Derivation-Sin72-Angular-Factor-Explicit.md) |
| Derivation Sqrt2 Factor From First Principles | [Derivation-Sqrt2-Factor-From-First-Principles.md](supporting/Derivation-Sqrt2-Factor-From-First-Principles.md) |
| Derivation Three Phi Factors Explicit | [Derivation-Three-Phi-Factors-Explicit.md](supporting/Derivation-Three-Phi-Factors-Explicit.md) |
| Derivation Triality Squared In EW Formula | [Derivation-Triality-Squared-In-EW-Formula.md](supporting/Derivation-Triality-Squared-In-EW-Formula.md) |
| Derivation Unified Z3 Origin Of Three | [Derivation-Unified-Z3-Origin-Of-Three.md](supporting/Derivation-Unified-Z3-Origin-Of-Three.md) |
| Experimental Verification Roadmap | [Experimental-Verification-Roadmap.md](supporting/Experimental-Verification-Roadmap.md) |
| Gap Resolution Summary | Consolidated into [Research-Remaining-Gaps-Worksheet.md](supporting/Research-Remaining-Gaps-Worksheet.md) §"Earlier Gap Resolution" |
| Global Minimality Decidability Analysis | [Global-Minimality-Decidability-Analysis.md](supporting/Global-Minimality-Decidability-Analysis.md) |
| Hedgehog Ansatz Global Minimality Research | [Hedgehog-Ansatz-Global-Minimality-Research.md](supporting/Hedgehog-Ansatz-Global-Minimality-Research.md) |
| Hedgehog Global Minimality Attack Plan | [Hedgehog-Global-Minimality-Attack-Plan.md](supporting/Hedgehog-Global-Minimality-Attack-Plan.md) |
| Heterotic String Connection Development | [Heterotic-String-Connection-Development.md](supporting/Heterotic-String-Connection-Development.md) |
| Intuitive Analogies Collection | [Intuitive-Analogies-Collection.md](supporting/Intuitive-Analogies-Collection.md) |
| Lemma 0.0.XXe-BC Bilayer Coupling Geometric Derivation | [Lemma-0.0.XXe-Bilayer-Coupling-Geometric-Derivation.md](supporting/Lemma-0.0.XXe-Bilayer-Coupling-Geometric-Derivation.md) · [Lean 4](../../lean/ChiralGeometrogenesis/PureMath/Polyhedra/BilayerCoupling.lean) |
| Lemma 0.0.XXe-NP Nucleation Probability Proof | [Lemma-0.0.XXe-Nucleation-Probability-Proof.md](supporting/Lemma-0.0.XXe-Nucleation-Probability-Proof.md) |
| Lemma A CG Energy Decomposition Proof | [Lemma-A-CG-Energy-Decomposition-Proof.md](supporting/Lemma-A-CG-Energy-Decomposition-Proof.md) |
| Macroscopic Arrow of Time Roadmap | [Macroscopic-Arrow-of-Time-Roadmap.md](supporting/Macroscopic-Arrow-of-Time-Roadmap.md) |
| Open Question 1 Lattice Spacing (Resolved) | Consolidated into [Research-Remaining-Gaps-Worksheet.md](supporting/Research-Remaining-Gaps-Worksheet.md) §"Resolved Open Questions: OQ-2" |
| Open Question Quantitative Predictions (Resolved) | Consolidated into [Research-Remaining-Gaps-Worksheet.md](supporting/Research-Remaining-Gaps-Worksheet.md) §"Resolved Open Questions: OQ-1" |
| Phase 0 Emergence Chain Synthesis | [Phase-0-Emergence-Chain-Synthesis.md](supporting/Phase-0-Emergence-Chain-Synthesis.md) |
| Phase6 Scattering Theory Plan | [Phase6-Scattering-Theory-Plan.md](supporting/Phase6-Scattering-Theory-Plan.md) |
| Plan 5.2.5 Bekenstein Hawking Coefficient Derivation | [Plan-5.2.5-Bekenstein-Hawking-Coefficient-Derivation.md](supporting/Plan-5.2.5-Bekenstein-Hawking-Coefficient-Derivation.md) |
| Plan Millennium Mass Gap Resolution | [Plan-Millennium-Mass-Gap-Resolution.md](supporting/Plan-Millennium-Mass-Gap-Resolution.md) |
| Plan Yang Mills Mass Gap Phases A E | [Plan-Yang-Mills-Mass-Gap-Phases-A-E.md](supporting/Plan-Yang-Mills-Mass-Gap-Phases-A-E.md) |
| Profound Philosophical Statements | [Profound-Philosophical-Statements.md](supporting/Profound-Philosophical-Statements.md) |
| QCD Skyrme CG Connection Analysis | [QCD-Skyrme-CG-Connection-Analysis.md](supporting/QCD-Skyrme-CG-Connection-Analysis.md) |
| RESTRUCTURED FILES NOTE Theorem 0.2.3 | [RESTRUCTURED-FILES-NOTE-Theorem-0.2.3.md](supporting/RESTRUCTURED-FILES-NOTE-Theorem-0.2.3.md) |
| RESTRUCTURED FILES NOTE Theorem 5.2.4 | [RESTRUCTURED-FILES-NOTE-Theorem-5.2.4.md](supporting/RESTRUCTURED-FILES-NOTE-Theorem-5.2.4.md) |
| RESTRUCTURED FILES NOTE | [RESTRUCTURED-FILES-NOTE.md](supporting/RESTRUCTURED-FILES-NOTE.md) |
| Research Alternative Derivations 2sqrtPi To 4 Bridge | [Research-Alternative-Derivations-2sqrtPi-To-4-Bridge.md](supporting/Research-Alternative-Derivations-2sqrtPi-To-4-Bridge.md) |
| Research Fisher Killing Loop Groups | [Research-Fisher-Killing-Loop-Groups.md](supporting/Research-Fisher-Killing-Loop-Groups.md) |
| Research Meta Foundational Directions | [Research-Meta-Foundational-Directions.md](supporting/Research-Meta-Foundational-Directions.md) |
| Research Note Balaban RG Adaptation FCC | [Research-Note-Balaban-RG-Adaptation-FCC.md](supporting/Research-Note-Balaban-RG-Adaptation-FCC.md) |
| Research Plan Graviton Dynamics Extension | [Research-Plan-Graviton-Dynamics-Extension.md](supporting/Research-Plan-Graviton-Dynamics-Extension.md) |
| Research Plan Lambda Equals Ngen Over 24 | [Research-Plan-Lambda-Equals-Ngen-Over-24.md](supporting/Research-Plan-Lambda-Equals-Ngen-Over-24.md) |
| Research Pure Information Bound On N | [Research-Pure-Information-Bound-On-N.md](supporting/Research-Pure-Information-Bound-On-N.md) |
| Research Remaining Gaps Worksheet | [Research-Remaining-Gaps-Worksheet.md](supporting/Research-Remaining-Gaps-Worksheet.md) |
| Unified Visualization Development | [Unified-Visualization-Development.md](supporting/Unified-Visualization-Development.md) |
| asymptotic safety collaboration proposal | [asymptotic-safety-collaboration-proposal.md](supporting/asymptotic-safety-collaboration-proposal.md) |
| asymptotic safety gauge coupling research | [asymptotic-safety-gauge-coupling-research.md](supporting/asymptotic-safety-gauge-coupling-research.md) |
| entanglement gravity 64 research | [entanglement-gravity-64-research.md](supporting/entanglement-gravity-64-research.md) |
| holographic qcd analysis | [holographic-qcd-analysis.md](supporting/holographic-qcd-analysis.md) |
| lattice qcd deconfinement temperature | [lattice-qcd-deconfinement-temperature.md](supporting/lattice-qcd-deconfinement-temperature.md) |
| reverse engineering analysis | [reverse-engineering-analysis.md](supporting/reverse-engineering-analysis.md) |
| rigorous alpha s derivation | [rigorous-alpha-s-derivation.md](supporting/rigorous-alpha-s-derivation.md) |
| su5 phase cancellation research | [su5-phase-cancellation-research.md](supporting/su5-phase-cancellation-research.md) |
| theorem 5.2.6 historical development | [theorem-5.2.6-historical-development.md](supporting/theorem-5.2.6-historical-development.md) |
| tqft coupling quantization research | [tqft-coupling-quantization-research.md](supporting/tqft-coupling-quantization-research.md) |
| tqft research summary | [tqft-research-summary.md](supporting/tqft-research-summary.md) |
| tqft specific findings | [tqft-specific-findings.md](supporting/tqft-specific-findings.md) |
| two loop QCD analysis | [two-loop-QCD-analysis.md](supporting/two-loop-QCD-analysis.md) |

---

## Verification Records

**454 files** — Multi-agent verification reports

See [verification-records/](verification-records/) for the complete collection of:
- Multi-agent verification reports
- Adversarial physics verification
- Mathematical verification
- Literature verification
- Executive summaries
- Issue resolution documents

---

## Statistics

| Directory | Files | Description |
|-----------|-------|-------------|
| foundations/ | 131 | Minimal axioms, 0.0.x theorems |
| Phase0/ | 16 | Pre-geometric foundations, 0.1.x-0.3.x |
| Phase1/ | 5 | SU(3) geometry and chiral fields |
| Phase2/ | 39 | Pressure-depression dynamics |
| Phase3/ | 30 | Mass generation |
| Phase4/ | 15 | Topological solitons |
| Phase5/ | 40 | Emergent spacetime and gravity |
| Phase6/ | 12 | Scattering theory |
| Phase7/ | 83 | Renormalization and consistency |
| Phase8/ | 16 | Predictions and tests |
| reference/ | 12 | Constants, techniques, protocols |
| supporting/ | 74 | Research and analysis documents |
| verification-records/ | 454 | Multi-agent verification reports |
| **TOTAL** | **926** | All proof files |

---

*Generated from filesystem scan on 2026-02-16*
