# Thematic Groups: Chiral Geometrogenesis

> **Cross-phase organization of all proofs by conceptual thread**
> Last updated: 2026-03-29

This document organizes proofs into thematic groups that cut across phase boundaries. While the [PROOF-INDEX](PROOF-INDEX.md) organizes by phase (build-order) and the [CATEGORY-INDEX](foundations/CATEGORY-INDEX.md) covers foundations only, this document lets you review entire conceptual threads as a unit — checking that a single idea (e.g., "mass generation" or "chirality") is treated coherently everywhere it appears.

**Purpose:** Detect fragmentation, verify consistency, and enable whole-thread review.

**Companion documents:**
- [PROOF-INDEX.md](PROOF-INDEX.md) — Phase-ordered listing of all proof files
- [Mathematical-Proof-Plan.md](../Mathematical-Proof-Plan.md) — Status, axiom tracking, derivation chains
- [Unification-Points-Details.md](reference/Unification-Points-Details.md) — 7 critical cross-cutting consistency requirements
- [CATEGORY-INDEX.md](foundations/CATEGORY-INDEX.md) — Thematic categories for foundations only

**Audit plans and findings:**
- [G1 Geometric Foundation Audit](reviews/G1/G1-Geometric-Foundation-Coherence-Audit.md) — Coherence (87/87), Validity (60/60), Adversarial (40/40) — **COMPLETE**
- See [Appendix D](#appendix-d-publication-paper-boundaries) for paper-level organization
- See [Appendix E](#appendix-e-three-layer-audit-protocol) for the standardized audit process

---

## How to Use This Document

1. **Coherence review:** Pick a group. Read every proof in order. Check that definitions, notation, and physical mechanisms are identical throughout.
2. **Fragmentation hunt:** For each group, walk the coherence checklist. Any "no" answer is a potential fragmentation point.
3. **Cross-group audit:** Check the dependency map. If Group X imports a concept from Group Y, verify the import is consistent with Y's primary definition.

---

## Group Overview

| Group | Name | Phases | Proofs | Core Question |
|-------|------|--------|--------|---------------|
| [G1](#g1-geometric-foundation) | Geometric Foundation | -1, 0, 1 | ~25 | Why D=4? Why SU(3)? Why stella octangula? |
| [G2](#g2-gauge-theory--confinement) | Gauge Theory & Confinement | -1, 1, 2, 7 | ~25 | How does SU(3) gauge structure produce confinement? |
| [G3](#g3-time--entropy) | Time & Entropy | -1, 0, 2, 5 | ~15 | How does time emerge and why does it have an arrow? |
| [G4](#g4-chirality--cp-violation) | Chirality & CP Violation | -1, 0, 2, 4 | ~16 | Why is the weak force left-handed? Why more matter than antimatter? |
| [G5](#g5-mass-generation) | Mass Generation | 0, 2, 3, 4, 6 | ~28 | How do particles get mass without assuming the Higgs? |
| [G6](#g6-qcd-scale-derivation) | QCD Scale Derivation | -1 | ~20 | Can all QCD parameters come from one geometric input? |
| [G7](#g7-quantum-foundations) | Quantum Foundations | -1 | ~12 | Does quantum mechanics emerge from geometry? |
| [G8](#g8-emergent-gravity) | Emergent Gravity | -1, 5 | ~25 | Does general relativity emerge from pre-geometric dynamics? |
| [G9](#g9-electroweak-sector) | Electroweak Sector | -1, 3, 6 | ~20 | Can SU(2)×U(1) and the Higgs potential be derived geometrically? |
| [G10](#g10-renormalization--yang-mills) | Renormalization & Yang-Mills | 7 | ~55 | Is the theory mathematically consistent? Does it have a mass gap? |
| [G11](#g11-bootstrap--uniqueness) | Bootstrap & Uniqueness | -1 | ~13 | Is this framework the UNIQUE self-consistent theory on ∂S? |
| [G12](#g12-predictions--falsifiability) | Predictions & Falsifiability | 3, 4, 6, 8 | ~25 | What does the framework predict that can be tested? |

---

## Cross-Group Dependency Map

```
G1 (Geometry) ──────────────────────────────────────────────────┐
  │                                                             │
  ├──→ G2 (Gauge & Confinement) ──→ G10 (Renorm & YM)           │
  │      │                            │                         │
  │      ├──→ G5 (Mass Generation) ──→ G12 (Predictions)        │
  │      │      │                                               │
  │      │      └──→ G8 (Emergent Gravity) ──→ G12              │
  │      │                                                      │
  │      └──→ G4 (Chirality & CP) ──→ G12                       │
  │                                                             │
  ├──→ G3 (Time & Entropy) ──→ G8 (Emergent Gravity)            │
  │                                                             │
  ├──→ G6 (QCD Scales) ──→ G5, G10, G12                         │
  │                                                             │
  ├──→ G7 (Quantum Foundations)                                 │
  │                                                             │
  ├──→ G9 (Electroweak) ──→ G12                                 │
  │                                                             │
  └──→ G11 (Bootstrap & Uniqueness) ←── G6, G8 (feedback)       │
                                                                │
  (All groups ultimately depend on G1) ─────────────────────────┘
```

---

## G1: Geometric Foundation

**Core question:** Why does the framework live on two interpenetrating tetrahedra in 4 dimensions with SU(3) gauge symmetry?

**Unification points touched:** None directly (G1 establishes the substrate for all others)

**Coherence audit:** [G1-Geometric-Foundation-Coherence-Audit.md](reviews/G1/G1-Geometric-Foundation-Coherence-Audit.md)

### Proofs (theorem-number order)

> **Note:** This table is ordered by theorem number, not by dependency. The [audit plan](reviews/G1/G1-Geometric-Foundation-Coherence-Audit.md) organizes these into 6 **thematic categories** (C1–C6) by conceptual role, not dependency order. The actual dependency DAG crosses category boundaries freely — in particular, Phase 0 definitions (Def 0.1.1–0.1.4) and the Thm 1.1.1 bridge are logically upstream of several foundational theorems (Thm 0.0.6, 0.0.12, 0.0.13). See the [M8 dependency analysis](reviews/G1/G1-Geometric-Foundation-Coherence-M8-Findings.md) for the complete DAG and topological ordering.

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | -1 | Def 0.0.0 | Minimal Geometric Realization | [foundations/Definition-0.0.0](foundations/Definition-0.0.0-Minimal-Geometric-Realization.md) |
| 2 | -1 | Thm 0.0.1 | D=4 From Observer Existence | [foundations/Theorem-0.0.1](foundations/Theorem-0.0.1-D4-From-Observer-Existence.md) |
| 3 | -1 | Thm 0.0.2 | Euclidean ℝ³ From SU(3) | [foundations/Theorem-0.0.2](foundations/Theorem-0.0.2-Euclidean-From-SU3.md) |
| 4 | -1 | Thm 0.0.2b | Dimension-Color Correspondence | [foundations/Theorem-0.0.2b](foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md) |
| 5 | -1 | Lem 0.0.2a | Confinement Dimension | [foundations/Lemma-0.0.2a](foundations/Lemma-0.0.2a-Confinement-Dimension.md) |
| 6 | -1 | Prop 0.0.40 | Embedding Dimension From Confinement | [foundations/Proposition-0.0.40](foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md) |
| 7 | -1 | Thm 0.0.0a | Polyhedral Necessity | [foundations/Theorem-0.0.0a](foundations/Theorem-0.0.0a-Polyhedral-Necessity.md) (3-file) |
| 7a | -1 | Thm 0.0.0b | Geometric Realization From Finite Information | [foundations/Theorem-0.0.0b](foundations/Theorem-0.0.0b-Geometric-Realization-From-Finite-Information.md) |
| 7b | -1 | Thm 0.0.0c | Finite Information From Observer Existence | [foundations/Theorem-0.0.0c](foundations/Theorem-0.0.0c-Finite-Information-From-Observer-Existence.md) |
| 8 | -1 | Prop 0.0.XX | SU(3) From Distinguishability | [foundations/Proposition-0.0.XX](foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md) |
| 9 | -1 | Thm 0.0.3 | Stella Uniqueness | [foundations/Theorem-0.0.3](foundations/Theorem-0.0.3-Stella-Uniqueness.md) |
| 9a | -1 | Prop 0.0.3a | Computational Crystallization of Stella | [foundations/Proposition-0.0.3a](foundations/Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula.md) |
| 9b | -1 | Prop 0.0.3b | Spontaneous Lattice Formation from Z₃ Fields | [foundations/Proposition-0.0.3b](foundations/Proposition-0.0.3b-Spontaneous-Lattice-Formation-From-Z3-Fields.md) |
| 10 | -1 | Thm 0.0.3b | Geometric Realization Completeness | [foundations/Theorem-0.0.3b](foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md) |
| 11 | -1 | Prop 0.0.16a | A₃ From Physical Requirements | [foundations/Proposition-0.0.16a](foundations/Proposition-0.0.16a-A3-From-Physical-Requirements.md) |
| 12 | -1 | Thm 0.0.16 | Adjacency From SU(3) | [foundations/Theorem-0.0.16](foundations/Theorem-0.0.16-Adjacency-From-SU3.md) |
| 13 | -1 | Thm 0.0.6 | Spatial Extension From Octet Truss | [foundations/Theorem-0.0.6](foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md) (3-file) |
| 14 | -1 | Prop 0.0.6b | Continuum Limit Procedure | [foundations/Proposition-0.0.6b](foundations/Proposition-0.0.6b-Continuum-Limit-Procedure.md) |
| 15 | -1 | Thm 0.0.9 | Framework-Internal D=4 Consistency Check | [foundations/Theorem-0.0.9](foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md) |
| 16 | -1 | Thm 0.0.15 | Topological Determination SU(3) | [foundations/Theorem-0.0.15](foundations/Theorem-0.0.15-Topological-Determination-SU3.md) |
| 17 | -1 | Thm 0.0.12 | Categorical Equivalence | [foundations/Theorem-0.0.12](foundations/Theorem-0.0.12-Categorical-Equivalence.md) (3-file) |
| 18 | -1 | Thm 0.0.13 | Tannaka Reconstruction SU(3) | [foundations/Theorem-0.0.13](foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md) (3-file) |
| 19 | 0 | Def 0.1.1 | Stella Octangula Boundary Topology | [Phase0/Definition-0.1.1](Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md) (3-file) |
| 20 | 0 | Def 0.1.2 | Three Color Fields & Relative Phases | [Phase0/Definition-0.1.2](Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md) |
| 21 | 0 | Def 0.1.3 | Pressure Functions | [Phase0/Definition-0.1.3](Phase0/Definition-0.1.3-Pressure-Functions.md) |
| 21a | 0 | Prop 0.1.3a | Pressure Function Form-Independence | [Phase0/Proposition-0.1.3a](Phase0/Proposition-0.1.3a-Pressure-Function-Form-Independence.md) · [Lean 4](../../lean/ChiralGeometrogenesis/Phase0/Proposition_0_1_3a.lean) |
| 22 | 0 | Def 0.1.4 | Color Field Domains | [Phase0/Definition-0.1.4](Phase0/Definition-0.1.4-Color-Field-Domains.md) |
| 23 | 0 | Thm 0.1.0 | Field Existence From Distinguishability | [Phase0/Theorem-0.1.0](Phase0/Theorem-0.1.0-Field-Existence-From-Distinguishability.md) |
| 24 | 1 | Thm 1.1.1 | SU(3) ↔ Stella Octangula | [Phase1/Theorem-1.1.1](Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md) |
| 25 | 1 | Def 1.1.4 | Stella Diagram Rules | [Phase1/Definition-1.1.4](Phase1/Definition-1.1.4-Stella-Diagram-Rules.md) |

### Internal dependency chain
```
Thm 0.0.0c (I1 → FI) → Thm 0.0.0b (FI → F1) → Def 0.0.0 → Thm 0.0.1 (D=4) → Thm 0.0.2 (ℝ³ from SU(3))
                                     ↓
                               Lem 0.0.2a (d ≥ N-1)
                                     ↓
                               Prop 0.0.40 (d_embed = N)
                                     ↓
                               Thm 0.0.3 (Stella uniqueness)
                                     ↓
                    ┌────────────────┼───────────────┐
                    ↓                ↓               ↓
              Def 0.1.1        Thm 0.0.6       Thm 1.1.1
         (Boundary topology)  (Octet truss)   (SU(3)↔Stella)
                    ↓
         ┌─────────┼─────────┐
         ↓         ↓         ↓
     Def 0.1.2  Def 0.1.3  Def 0.1.4
    (Colors)   (Pressure)  (Domains)
                   ↓
             Prop 0.1.3a
          (Form-independence)
```

### Cross-group exports
- **→ G2:** SU(3) gauge group (Thm 0.0.3, 1.1.1), FCC lattice (Thm 0.0.6)
- **→ G3:** Color fields (Def 0.1.2), pressure functions (Def 0.1.3)
- **→ G4:** Z₃ center structure (from SU(3)), stella chirality (Thm 0.0.5)
- **→ G5:** Color fields, pressure modulation
- **→ G6:** R_stella as geometric scale, stella topology for Casimir computation
- **→ G7:** Fisher metric substrate (Thm 0.0.17)
- **→ G8:** Pre-geometric arena, D=4 structure
- **→ G9:** SU(2) substructure of stella (Prop 0.0.22)
- **→ G11:** Stella as unique fixed point

### Independent input structure (V1 + V3 Audit)

> **Source:** [G1-Validity-Audit-Module-V1-Findings.md](reviews/G1/G1-Validity-Audit-Module-V1-Findings.md) §"The True Input Structure of G1", updated per [V3 (Semantic Circularity Detection)](reviews/G1/G1-Validity-Audit-Module-V3-Findings.md) §V3.5–V3.6

**The G1 foundation rests on 1 physical input and 7 framework axioms = 8 independent inputs total.**

The framework's narrative sometimes suggests fewer inputs ("derive everything from D = 4 and geometry"). The honest count is 8, of which 7 are framework-specific choices that reasonable physicists could make differently.

| # | Input | Class | Role |
|---|-------|-------|------|
| **I1** | Observer existence requires stable orbits + stable atoms → D = 4 | (E)/anthropic | Selects spacetime dimension |
| **I3** | Fisher information metric exists on configuration space (Axiom A0') | (F) | Field existence and distinguishability |
| **F1** | Gauge group must be geometrically realized in physical space | (F) | Central framework postulate — THE irreducible axiom |
| **F2** | GR1: Fund + anti-fund representation content | (F) | Matter + antimatter vertex structure |
| **F3** | GR3: Chirality/conjugation geometrically encoded | (F) | Two-tetrahedron structure |
| **F4** | MIN1: Nature prefers minimal vertex count | (F) | Selects stella over larger polyhedra |
| **F5** | Compact simple (not product) gauge group | (F) | Excludes SU(3)×SU(2)×U(1) at this stage |
| **F6** | Vertex-transitivity for spatial extension | (F) | Selects FCC over HCP |

**Derived (not independent):** I2 = F1 + established physics ([Prop 0.0.40](foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md)), D = 4 (from I1), N = 3 colors (from D = 4 + F1 constraints), SU(3) (from Z₃ + rank ≤ 2 + Cartan; requires I1, F1, F5), stella octangula (from I1 + F1–F5), Z₃ phases (from stella geometry), "color neutrality" (= Z₃; same origin), FCC lattice (from SU(3) + F6).

> **V3 update (2026-02-23):** Reduced from 9 to 8 inputs. I2 (Physical Hypothesis 0.0.0f: confinement ↔ d_embed = rank + 1) reclassified as **derived** — it equals F1 + established physics per [Prop 0.0.40](foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md) and [V3 §V3.5](reviews/G1/G1-Validity-Audit-Module-V3-Findings.md#v35--does-physical-hypothesis-000f-make-the-3d-embedding-circular). I3 reclassified from "physical input" to "framework axiom" (it is (F)-class). "Color neutrality" identified as semantically equivalent to Z₃ from stella geometry ([V3 §V3.3](reviews/G1/G1-Validity-Audit-Module-V3-Findings.md#v33--does-color-neutrality-independently-constrain-or-restate-su3)), not an additional input.

### Coherence checklist — 143/178 PASS
- [x] ∂S is always two disjoint tetrahedra (χ=4), never an octahedron (χ=2)
- [x] SU(3) derivation paths (topological, categorical, Tannaka) all give the same group
- [x] Vertex count = 8 (4+4), edge count = 12 (6+6), face count = 8 (4+4) everywhere
- [x] D=4 derivation (Thm 0.0.1) and framework-internal D=4 (Thm 0.0.9) are consistent
- [x] FCC lattice (Thm 0.0.6) uses correct stella vertex structure
- [x] Color field phases (0, 2π/3, 4π/3) match SU(3) Z₃ center everywhere

---

## G2: Gauge Theory & Confinement

**Core question:** How does the SU(3) gauge structure on ∂S produce color confinement and the QCD vacuum?

**Unification points touched:** UP4 (Instanton Physics)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | 1 | Thm 1.1.1 | SU(3) ↔ Stella Octangula | [Phase1/Theorem-1.1.1](Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md) |
| 2 | 1 | Thm 1.1.2 | Charge Conjugation | [Phase1/Theorem-1.1.2](Phase1/Theorem-1.1.2-Charge-Conjugation.md) |
| 3 | 1 | Thm 1.1.3 | Color Confinement Geometry | [Phase1/Theorem-1.1.3](Phase1/Theorem-1.1.3-Color-Confinement-Geometry.md) |
| 3a | 1 | Def 1.1.4 | Stella Diagram Rules | [Phase1/Definition-1.1.4](Phase1/Definition-1.1.4-Stella-Diagram-Rules.md) |
| 4 | 1 | Thm 1.2.1 | Vacuum Expectation Value | [Phase1/Theorem-1.2.1](Phase1/Theorem-1.2.1-Vacuum-Expectation-Value.md) |
| 5 | 1 | Thm 1.2.2 | Chiral Anomaly | [Phase1/Theorem-1.2.2](Phase1/Theorem-1.2.2-Chiral-Anomaly.md) |
| 6 | 2 | Thm 2.1.1 | Bag Model Derivation | [Phase2/Theorem-2.1.1](Phase2/Theorem-2.1.1-Bag-Model-Derivation.md) |
| 7 | 2 | Thm 2.1.2 | Pressure Field Gradient | [Phase2/Theorem-2.1.2](Phase2/Theorem-2.1.2-Pressure-Field-Gradient.md) |
| 8 | 2 | Lem 2.1.3 | Depression Symmetry Breaking | [Phase2/Lemma-2.1.3](Phase2/Lemma-2.1.3-Depression-Symmetry-Breaking.md) |
| 9 | 2 | Drv 2.1.2a | Equilibrium Radius | [Phase2/Derivation-2.1.2a](Phase2/Derivation-2.1.2a-Equilibrium-Radius.md) |
| 10 | 2 | Drv 2.1.2b | χ Profile | [Phase2/Derivation-2.1.2b](Phase2/Derivation-2.1.2b-Chi-Profile.md) |
| 10a | 2 | Drv 2.1.2c | Bag Constant From Stella Geometry | [Phase2/Derivation-2.1.2c](Phase2/Derivation-2.1.2c-Bag-Constant-From-Stella-Geometry.md) |
| 11 | 2 | Thm 2.5.1 | CG Lagrangian Derivation | [Phase2/Theorem-2.5.1](Phase2/Theorem-2.5.1-CG-Lagrangian-Derivation.md) |
| 12 | 2 | Thm 2.5.2 | Dynamical Confinement | [Phase2/Theorem-2.5.2](Phase2/Theorem-2.5.2-Dynamical-Confinement.md) (3-file) |
| 13 | 2 | Prop 2.5.2a | Wilson Loop Area Law | [Phase2/Proposition-2.5.2a](Phase2/Proposition-2.5.2a-Wilson-Loop-Area-Law-From-Geometry.md) (3-file) |
| 14 | 2 | Prop 2.5.2b | Inter-Stella Gauge Coupling FCC | [Phase2/Proposition-2.5.2b](Phase2/Proposition-2.5.2b-Inter-Stella-Gauge-Coupling-FCC.md) (3-file) |
| 15 | 2 | Prop 2.5.2c | Transfer Matrix FCC Layers | [Phase2/Proposition-2.5.2c](Phase2/Proposition-2.5.2c-Transfer-Matrix-FCC-Layers.md) (3-file) |
| 16 | 2 | Prop 2.4.2 | Pre-Geometric Beta Function | [Phase2/Proposition-2.4.2](Phase2/Proposition-2.4.2-Pre-Geometric-Beta-Function.md) |
| 17 | -1 | Prop 0.0.38 | Exact Stella Gauge Partition Function | [foundations/Proposition-0.0.38](foundations/Proposition-0.0.38-Exact-Stella-Gauge-Partition-Function.md) |
| 18 | -1 | Prop 0.0.38a | Stella Gauge Spectrum | [foundations/Proposition-0.0.38a](foundations/Proposition-0.0.38a-Stella-Gauge-Spectrum.md) |
| 19 | -1 | Prop 0.0.39 | Stella Adjoint Decomposition | [foundations/Proposition-0.0.39](foundations/Proposition-0.0.39-Stella-Adjoint-Decomposition.md) |
| 20 | -1 | Prop 0.0.17s | Strong Coupling From Gauge Unification | [foundations/Proposition-0.0.17s](foundations/Proposition-0.0.17s-Strong-Coupling-From-Gauge-Unification.md) |
| 21 | -1 | Prop 0.0.17ac | Edge Mode Decomposition UV Coupling | [foundations/Proposition-0.0.17ac](foundations/Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md) |
| 22 | -1 | Thm 0.0.4 | GUT Structure From Stella | [foundations/Theorem-0.0.4](foundations/Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md) |
| 23 | 7 | Thm 7.3.2 | Asymptotic Freedom | [Phase7/Theorem-7.3.2](Phase7/Theorem-7.3.2-Asymptotic-Freedom.md) (3-file + Two-Loop) |
| 24 | 7 | Thm 7.3.3 | Beta Function Structure | [Phase7/Theorem-7.3.3](Phase7/Theorem-7.3.3-Beta-Function-Structure.md) (3-file) |
| 25 | 7 | Prop 7.3.2a | Pressure-Balance Asymptotic Freedom | [Phase7/Proposition-7.3.2a](Phase7/Proposition-7.3.2a-Pressure-Balance-Asymptotic-Freedom.md) |

### Internal dependency chain
```
Thm 1.1.1 (SU(3)↔Stella) → Thm 1.1.3 (Confinement geometry)
     ↓                              ↓
Thm 1.2.2 (Chiral anomaly)    Thm 2.1.1 (Bag model)
     ↓                              ↓
Prop 0.0.38 (Partition fn)    Thm 2.5.1 (CG Lagrangian)
     ↓                              ↓
Prop 0.0.17s (α_s)            Thm 2.5.2 (Dynamical confinement)
                                     ↓
                               Prop 2.5.2a (Wilson loop area law)
                                     ↓
                               Thm 7.3.2 (Asymptotic freedom)
```

### Cross-group imports
- **← G1:** SU(3) gauge group, stella topology, FCC lattice

### Cross-group exports
- **→ G5:** CG Lagrangian (Thm 2.5.1), confinement mechanism
- **→ G10:** Asymptotic freedom (Thm 7.3.2), beta function (Thm 7.3.3)
- **→ G6:** UV coupling α_s (Prop 0.0.17s)

### Coherence checklist
- [ ] Anomaly coefficient 1/(16π²) is identical in Thm 1.2.2 and wherever instantons appear (G4)
- [ ] Wilson loop area law (Prop 2.5.2a) uses same string tension σ as G6
- [ ] Beta function in Prop 2.4.2 (pre-geometric) matches Thm 7.3.2 (perturbative) in appropriate limit
- [ ] α_s at UV (Prop 0.0.17s: 1/64) runs consistently to α_s(M_Z) via Thm 7.3.2
- [ ] Bag model (Thm 2.1.1) and dynamical confinement (Thm 2.5.2) describe the same physics at different approximation levels
- [ ] FCC lattice coupling (Prop 2.5.2b) is consistent with single-stella partition function (Prop 0.0.38)

---

## G3: Time & Entropy

**Core question:** How does time emerge from the pre-geometric framework, and why does it have a thermodynamic arrow?

**Unification points touched:** UP1 (Time and Evolution), UP2 (Energy and Stress-Energy)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | 0 | Thm 0.2.1 | Total Field Superposition | [Phase0/Theorem-0.2.1](Phase0/Theorem-0.2.1-Total-Field-Superposition.md) |
| 2 | 0 | Thm 0.2.2 | Internal Time Emergence | [Phase0/Theorem-0.2.2](Phase0/Theorem-0.2.2-Internal-Time-Emergence.md) |
| 3 | 0 | Thm 0.2.3 | Stable Convergence Point | [Phase0/Theorem-0.2.3](Phase0/Theorem-0.2.3-Stable-Convergence-Point.md) (3-file) |
| 4 | 0 | Thm 0.2.4 | Pre-Geometric Energy Functional | [Phase0/Theorem-0.2.4](Phase0/Theorem-0.2.4-Pre-Geometric-Energy-Functional.md) |
| 5 | -1 | Prop 0.0.17c | Arrow of Time From Information Geometry | [foundations/Proposition-0.0.17c](foundations/Proposition-0.0.17c-Arrow-of-Time-From-Information-Geometry.md) |
| 6 | -1 | Prop 0.0.17p | Resolution of Problem of Time | [foundations/Proposition-0.0.17p](foundations/Proposition-0.0.17p-Resolution-of-Problem-of-Time.md) |
| 7 | 2 | Thm 2.2.1 | Phase-Locked Oscillation | [Phase2/Theorem-2.2.1](Phase2/Theorem-2.2.1-Phase-Locked-Oscillation.md) |
| 8 | 2 | Thm 2.2.2 | Limit Cycle | [Phase2/Theorem-2.2.2](Phase2/Theorem-2.2.2-Limit-Cycle.md) |
| 9 | 2 | Thm 2.2.3 | Time Irreversibility | [Phase2/Theorem-2.2.3](Phase2/Theorem-2.2.3-Time-Irreversibility.md) |
| 10 | 2 | Thm 2.2.4 | EFT Derivation | [Phase2/Theorem-2.2.4](Phase2/Theorem-2.2.4-EFT-Derivation.md) |
| 11 | 2 | Thm 2.2.5 | Coarse-Grained Entropy Production | [Phase2/Theorem-2.2.5](Phase2/Theorem-2.2.5-Coarse-Grained-Entropy-Production.md) |
| 12 | 2 | Thm 2.2.6 | Entropy Propagation | [Phase2/Theorem-2.2.6](Phase2/Theorem-2.2.6-Entropy-Propagation.md) |
| 13 | 2 | Drv 2.2.5a | Coupling Constant K | [Phase2/Derivation-2.2.5a](Phase2/Derivation-2.2.5a-Coupling-Constant-K.md) |
| 14 | 2 | Drv 2.2.5b | QCD Bath Degrees of Freedom | [Phase2/Derivation-2.2.5b](Phase2/Derivation-2.2.5b-QCD-Bath-Degrees-Freedom.md) |
| 15 | 2 | Drv 2.2.6a | QGP Entropy Production | [Phase2/Derivation-2.2.6a](Phase2/Derivation-2.2.6a-QGP-Entropy-Production.md) |
| 16 | 2 | Drv 2.2.6b | QCD-EM Coupling Efficiency | [Phase2/Derivation-2.2.6b](Phase2/Derivation-2.2.6b-QCD-EM-Coupling-Efficiency.md) |
| 17 | 5 | Thm 5.2.0 | Wick Rotation Validity | [Phase5/Theorem-5.2.0](Phase5/Theorem-5.2.0-Wick-Rotation-Validity.md) |

### Internal dependency chain
```
Thm 0.2.1 (Superposition) → Thm 0.2.2 (Internal time λ)
                                   ↓
                    ┌──────────────┼──────────────┐
                    ↓              ↓              ↓
             Prop 0.0.17c    Thm 0.2.4      Thm 2.2.1
            (Arrow of time) (Energy E[χ])  (Phase-lock)
                    ↓                            ↓
             Prop 0.0.17p                  Thm 2.2.2 → 2.2.3
            (Problem of time)             (Limit cycle → Irreversibility)
                                                 ↓
                                           Thm 2.2.5 → 2.2.6
                                          (Entropy production & propagation)
```

### Cross-group imports
- **← G1:** Color fields (Def 0.1.2), pressure functions (Def 0.1.3)

### Cross-group exports
- **→ G5:** Internal time λ (Thm 0.2.2), EFT derivation (Thm 2.2.4)
- **→ G8:** Pre-geometric energy (Thm 0.2.4), Wick rotation (Thm 5.2.0)
- **→ G10:** Thermodynamic framework for lattice proofs

### Coherence checklist
- [ ] Internal time λ (Thm 0.2.2) and physical time t = λ/ω use the same ω everywhere
- [ ] Wick rotation (Thm 5.2.0) correctly handles the oscillating VEV χ(t) = v·e^{iωt} without divergence
- [ ] Entropy production (Thm 2.2.5) is consistent with thermodynamic emergence in G8
- [ ] Arrow of time (Prop 0.0.17c, information-geometric) matches irreversibility (Thm 2.2.3, dynamical)
- [ ] Problem of time resolution (Prop 0.0.17p) is compatible with GR time in G8
- [ ] Pre-geometric energy E[χ] (Thm 0.2.4) reduces to ∫d³x T₀₀ after metric emergence (G8)

---

## G4: Chirality & CP Violation

**Core question:** Why is the weak force left-handed? Why is there more matter than antimatter? Is it the same mechanism?

**Unification points touched:** UP3 (Chirality Selection), UP4 (Instanton Physics)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | -1 | Thm 0.0.5 | Chirality Selection From Geometry | [foundations/Theorem-0.0.5](foundations/Theorem-0.0.5-Chirality-Selection-From-Geometry.md) |
| 2 | -1 | Prop 0.0.5a | Z₃ Center Constrains θ Angle | [foundations/Proposition-0.0.5a](foundations/Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md) |
| 3 | -1 | Prop 0.0.5b | Quark Mass Phase Constraint | [foundations/Proposition-0.0.5b](foundations/Proposition-0.0.5b-Quark-Mass-Phase-Constraint.md) |
| 4 | 2 | Thm 2.3.1 | Universal Chirality | [Phase2/Theorem-2.3.1](Phase2/Theorem-2.3.1-Universal-Chirality.md) (3-file) |
| 5 | 2 | Drv 2.3.1a | Chirality Propagation | [Phase2/Derivation-2.3.1a](Phase2/Derivation-2.3.1a-Chirality-Propagation.md) |
| 6 | 2 | Thm 2.4.1 | Gauge Unification | [Phase2/Theorem-2.4.1](Phase2/Theorem-2.4.1-Gauge-Unification.md) (3-file) |
| 7 | 2 | Thm 2.4.2 | Topological Chirality | [Phase2/Theorem-2.4.2](Phase2/Theorem-2.4.2-Topological-Chirality.md) (3-file) |
| 8 | -1 | Prop 0.0.27 | Gauge-Fermion Instanton Structure | [foundations/Proposition-0.0.27](foundations/Proposition-0.0.27-Gauge-Fermion-Instanton-Structure.md) |
| 9 | 4 | Thm 4.2.1 | Chiral Bias Soliton Formation | [Phase4/Theorem-4.2.1](Phase4/Theorem-4.2.1-Chiral-Bias-Soliton-Formation.md) (3-file) |
| 10 | 4 | Thm 4.2.2 | Sakharov Conditions | [Phase4/Theorem-4.2.2](Phase4/Theorem-4.2.2-Sakharov-Conditions.md) (3-file) |
| 11 | 4 | Thm 4.2.3 | First-Order Phase Transition | [Phase4/Theorem-4.2.3](Phase4/Theorem-4.2.3-First-Order-Phase-Transition.md) |
| 12 | 4 | Prop 4.2.4 | Sphaleron Rate From CG Topology | [Phase4/Proposition-4.2.4](Phase4/Proposition-4.2.4-Sphaleron-Rate-From-CG-Topology.md) |
| 13 | 4 | Prop 4.3.3 | W-Soliton Cosmological Abundance | [Phase4/Proposition-4.3.3](Phase4/Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md) |

### Internal dependency chain
```
Thm 0.0.5 (Chirality from geometry: α = 2π/3 sign)
     ↓
Prop 0.0.5a (Z₃ → θ = 0)    Thm 2.3.1 (Universal chirality)
     ↓                              ↓
Prop 0.0.5b (Quark phases)    Thm 2.4.2 (Topological chirality)
                                     ↓
                               Prop 0.0.27 (Instanton structure)
                                     ↓
                    ┌────────────────┼────────────────┐
                    ↓                                 ↓
             Thm 4.2.1                          Thm 4.2.2
        (Chiral bias → solitons)           (Sakharov conditions)
                    ↓                                 ↓
             Thm 4.2.3 (Phase transition)    Prop 4.2.4 (Sphaleron rate)
                    ↓
             Prop 4.3.3 (W-soliton abundance via ADM — same chirality bias)
```

### Cross-group imports
- **← G1:** Z₃ center of SU(3), stella T₊/T₋ chirality
- **← G2:** Instanton density profile, anomaly coefficient 1/(16π²)

### Cross-group exports
- **→ G5:** Chiral drag mass mechanism (feeds Phase 3 → 5)
- **→ G9:** Electroweak chirality (left-handedness of weak force)
- **→ G12:** Baryogenesis predictions, CP violation observables

### Coherence checklist
- [ ] The SAME instanton density profile n(r) appears in Thm 2.2.4, Prop 0.0.27, and Thm 4.2.1
- [ ] Chirality sign (R→G→B) from Thm 0.0.5 propagates correctly to EW chirality (Thm 2.3.1)
- [ ] θ = 0 (Prop 0.0.5a, geometric) does not conflict with CP violation needed for baryogenesis
- [ ] Sphaleron rate (Prop 4.2.4) uses same instanton physics as chiral anomaly (Thm 1.2.2 in G2)
- [ ] N_f = 3 vs N_f = 6 choice for 't Hooft determinant is consistent across all proofs
- [ ] CKM phase at low energy connects to GUT-scale CP violation via single RG flow

---

## G5: Mass Generation

**Core question:** How do fermions acquire mass through phase-gradient coupling without assuming the Higgs mechanism?

**Unification points touched:** UP5 (Mass Generation)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | 3 | Thm 3.0.1 | Pressure-Modulated Superposition | [Phase3/Theorem-3.0.1](Phase3/Theorem-3.0.1-Pressure-Modulated-Superposition.md) |
| 2 | 3 | Thm 3.0.2 | Non-Zero Phase Gradient | [Phase3/Theorem-3.0.2](Phase3/Theorem-3.0.2-Non-Zero-Phase-Gradient.md) (3-file) |
| 3 | 3 | Thm 3.0.3 | Temporal Fiber Structure | [Phase3/Theorem-3.0.3](Phase3/Theorem-3.0.3-Temporal-Fiber-Structure.md) |
| 4 | 3 | Thm 3.0.4 | Planck Length Phase Coherence | [Phase3/Theorem-3.0.4](Phase3/Theorem-3.0.4-Planck-Length-Phase-Coherence.md) |
| 5 | 3 | Prop 3.1.1a | Lagrangian Form From Symmetry | [Phase3/Proposition-3.1.1a](Phase3/Proposition-3.1.1a-Lagrangian-Form-From-Symmetry.md) |
| 6 | 3 | Prop 3.1.1b | RG Fixed Point Analysis | [Phase3/Proposition-3.1.1b](Phase3/Proposition-3.1.1b-RG-Fixed-Point-Analysis.md) |
| 7 | 3 | Prop 3.1.1c | Geometric Coupling Formula | [Phase3/Proposition-3.1.1c](Phase3/Proposition-3.1.1c-Geometric-Coupling-Formula.md) (+ Derivation) |
| 8 | 3 | Prop 3.1.1d | WSR From CG Spectral Functions | [Phase3/Proposition-3.1.1d](Phase3/Proposition-3.1.1d-WSR-From-CG-Spectral-Functions.md) |
| 9 | 3 | Thm 3.1.1 | Chiral Drag Mass Formula | [Phase3/Theorem-3.1.1](Phase3/Theorem-3.1.1-Chiral-Drag-Mass-Formula.md) (3-file) |
| 10 | 3 | Thm 3.1.2 | Mass Hierarchy From Geometry | [Phase3/Theorem-3.1.2](Phase3/Theorem-3.1.2-Mass-Hierarchy-From-Geometry.md) (3-file) |
| 11 | 3 | Lem 3.1.2a | 24-Cell Two-Tetrahedra Connection | [Phase3/Lemma-3.1.2a](Phase3/Lemma-3.1.2a-24-Cell-Two-Tetrahedra-Connection.md) |
| 12 | 3 | Prop 3.1.2b | 4D Extension From Radial Structure | [Phase3/Proposition-3.1.2b](Phase3/Proposition-3.1.2b-4D-Extension-From-Radial-Structure.md) |
| 13 | 3 | Ext 3.1.2b | Complete Wolfenstein Parameters | [Phase3/Extension-3.1.2b](Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md) |
| 14 | 3 | Ext 3.1.2c | Instanton Overlap Derivation | [Phase3/Extension-3.1.2c](Phase3/Extension-3.1.2c-Instanton-Overlap-Derivation.md) |
| 15 | 3 | Cor 3.1.3 | Massless Right-Handed Neutrinos | [Phase3/Corollary-3.1.3](Phase3/Corollary-3.1.3-Massless-Right-Handed-Neutrinos.md) |
| 16 | 3 | Prop 3.1.4 | Neutrino Mass Sum Bound | [Phase3/Proposition-3.1.4](Phase3/Proposition-3.1.4-Neutrino-Mass-Sum-Bound.md) |
| 17 | 3 | Thm 3.1.5 | Majorana Scale From Geometry | [Phase3/Theorem-3.1.5](Phase3/Theorem-3.1.5-Majorana-Scale-From-Geometry.md) |
| 18 | 3 | Ext 3.1.2d | Complete PMNS Parameters | [Phase3/Extension-3.1.2d](Phase3/Extension-3.1.2d-Complete-PMNS-Parameters.md) |
| 19 | 3 | Lem 3.3.1 | Boundary Site Density | [Phase3/Lemma-3.3.1](Phase3/Lemma-3.3.1-Boundary-Site-Density.md) |
| 20 | 3 | Thm 3.2.1 | Low-Energy Equivalence (to Standard Model) | [Phase3/Theorem-3.2.1](Phase3/Theorem-3.2.1-Low-Energy-Equivalence.md) (3-file) |
| 21 | 3 | Thm 3.2.2 | High-Energy Deviations | [Phase3/Theorem-3.2.2](Phase3/Theorem-3.2.2-High-Energy-Deviations.md) |
| 22 | 4 | Thm 4.1.1 | Existence of Solitons | [Phase4/Theorem-4.1.1](Phase4/Theorem-4.1.1-Existence-of-Solitons.md) |
| 23 | 4 | Thm 4.1.2 | Soliton Mass Spectrum | [Phase4/Theorem-4.1.2](Phase4/Theorem-4.1.2-Soliton-Mass-Spectrum.md) |
| 24 | 4 | Thm 4.1.3 | Fermion Number Topology | [Phase4/Theorem-4.1.3](Phase4/Theorem-4.1.3-Fermion-Number-Topology.md) |
| 25 | 4 | Thm 4.1.4 | Dynamic Suspension Equilibrium | [Phase4/Theorem-4.1.4](Phase4/Theorem-4.1.4-Dynamic-Suspension-Equilibrium.md) (3-file) |
| 26 | 4 | Def 4.1.5 | Soliton Effective Potential | [Phase4/Definition-4.1.5](Phase4/Definition-4.1.5-Soliton-Effective-Potential.md) |
| 27 | 4 | Def 4.3.1 | W-Sector Field Theory | [Phase4/Definition-4.3.1](Phase4/Definition-4.3.1-W-Sector-Field-Theory.md) |
| 28 | 4 | Thm 4.3.2 | W-Soliton Existence and Properties | [Phase4/Theorem-4.3.2](Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md) |
| 29 | 4 | Prop 4.3.5 | Skyrme Parameter from Pressure-Kurtosis Geometry | [Phase4/Proposition-4.3.5](Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md) |

### Internal dependency chain
```
Thm 3.0.1 (Pressure modulation) → Thm 3.0.2 (Non-zero ∂μθ)
                                         ↓
                                   Prop 3.1.1a (Unique Lagrangian form)
                                         ↓
                                   Prop 3.1.1b (RG analysis: g_χ natural)
                                         ↓
                                   Thm 3.1.1 (Chiral drag mass formula)
                                         ↓
                    ┌────────────────────┼────────────────────┐
                    ↓                    ↓                    ↓
             Thm 3.1.2            Thm 3.2.1            Thm 4.1.1
        (Mass hierarchy)    (SM equivalence)      (Soliton existence)
                    ↓                    ↓                    ↓
        Ext 3.1.2b-d           Thm 3.2.2            Thm 4.1.2-4
      (CKM, PMNS)        (High-E deviations)    (Spectrum, topology)
                                                        ↓
                                                  Def 4.3.1 (W-sector field theory)
                                                        ↓
                                                  Thm 4.3.2 (W-soliton existence & mass)
                                                        ↑
                                                  Prop 4.3.5 (Skyrme parameter derivation)
```

### Cross-group imports
- **← G1:** Color fields, stella geometry
- **← G2:** CG Lagrangian (Thm 2.5.1), confinement structure
- **← G3:** Internal time λ, pre-geometric energy
- **← G6:** Parameters f_π, v_χ, ω, ε

### Cross-group exports
- **→ G8:** Stress-energy from massive fields (feeds metric emergence)
- **→ G9:** Higgs equivalence (Thm 3.2.1), high-energy deviations (Thm 3.2.2)
- **→ G12:** Mass predictions, CKM/PMNS parameters, neutrino bounds

### Coherence checklist
- [ ] Phase-gradient mass (Thm 3.1.1) and Higgs mechanism (Thm 3.2.1) are proven equivalent at low energy — not just claimed
- [ ] Mass type is explicit everywhere: pole mass, running mass, constituent mass, or current mass
- [ ] v_χ = f_π = 87.7 MeV is used consistently (not sometimes 92.2 MeV)
- [ ] g_χ ~ O(1) (Prop 3.1.1b) is used with consistent RG scale everywhere
- [ ] Instanton overlap (Ext 3.1.2c) uses same instanton profile as G4
- [ ] Soliton masses (Thm 4.1.2) are compatible with fermion masses (Thm 3.1.1)
- [ ] W-sector VEV $v_W = 123$ GeV (Def 4.3.1) is consistent with Higgs portal coupling $\lambda_{H\Phi} = 0.036$
- [ ] W-soliton mass (Thm 4.3.2, $M_W = 1620$ GeV) uses Skyrme parameter $e_W = 4.5$ derived from geometry (Prop 4.3.5)
- [ ] Neutrino sector (Cor 3.1.3, Prop 3.1.4, Thm 3.1.5) is internally consistent on Majorana vs Dirac

---

## G6: QCD Scale Derivation

**Core question:** Can all QCD parameters be derived from one geometric input (R_stella)?

**Unification points touched:** UP2 (Energy), UP4 (Instanton Physics)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | -1 | Prop 0.0.17j | String Tension From Casimir Energy | [foundations/Proposition-0.0.17j](foundations/Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md) |
| 2 | -1 | Prop 0.0.17k | Pion Decay Constant From Phase Lock | [foundations/Proposition-0.0.17k](foundations/Proposition-0.0.17k-Pion-Decay-Constant-From-Phase-Lock.md) |
| 3 | -1 | Prop 0.0.17k1 | One-Loop Correction To f_π | [foundations/Proposition-0.0.17k1](foundations/Proposition-0.0.17k1-One-Loop-Correction-To-Pion-Decay-Constant.md) |
| 4 | -1 | Prop 0.0.17k2 | CG Effective Action O(p⁴) GL Matching | [foundations/Proposition-0.0.17k2](foundations/Proposition-0.0.17k2-CG-Effective-Action-Op4-GL-Matching.md) |
| 5 | -1 | Prop 0.0.17k3 | First-Principles ℓ₄ From Stella | [foundations/Proposition-0.0.17k3](foundations/Proposition-0.0.17k3-First-Principles-Ell4-From-Stella-Octangula.md) |
| 6 | -1 | Prop 0.0.17k4 | c_V From Z₃ Phase Structure | [foundations/Proposition-0.0.17k4](foundations/Proposition-0.0.17k4-cV-From-Z3-Phase-Structure.md) |
| 7 | -1 | Prop 0.0.17l | Internal Frequency From Casimir Equipartition | [foundations/Proposition-0.0.17l](foundations/Proposition-0.0.17l-Internal-Frequency-From-Casimir-Equipartition.md) |
| 8 | -1 | Prop 0.0.17m | Chiral VEV From Phase Lock Stiffness | [foundations/Proposition-0.0.17m](foundations/Proposition-0.0.17m-Chiral-VEV-From-Phase-Lock-Stiffness.md) |
| 9 | -1 | Prop 0.0.17n | P4 Fermion Mass Comparison | [foundations/Proposition-0.0.17n](foundations/Proposition-0.0.17n-P4-Fermion-Mass-Comparison.md) |
| 10 | -1 | Prop 0.0.17o | Regularization Parameter Derivation | [foundations/Proposition-0.0.17o](foundations/Proposition-0.0.17o-Regularization-Parameter-Derivation.md) |
| 11 | -1 | Prop 0.0.17d | EFT Cutoff From Confinement | [foundations/Proposition-0.0.17d](foundations/Proposition-0.0.17d-EFT-Cutoff-From-Confinement.md) |
| 12 | -1 | Prop 0.0.17q | QCD Scale From Dimensional Transmutation | [foundations/Proposition-0.0.17q](foundations/Proposition-0.0.17q-QCD-Scale-From-Dimensional-Transmutation.md) |
| 13 | -1 | Prop 0.0.17r | Lattice Spacing From Holographic Self-Consistency | [foundations/Proposition-0.0.17r](foundations/Proposition-0.0.17r-Lattice-Spacing-From-Holographic-Self-Consistency.md) |
| 14 | -1 | Prop 0.0.17w | Equipartition From Maximum Entropy | [foundations/Proposition-0.0.17w](foundations/Proposition-0.0.17w-Equipartition-From-Maximum-Entropy.md) |
| 15 | -1 | Prop 0.0.17x | UV Coupling & Index Theorem Connection | [foundations/Proposition-0.0.17x](foundations/Proposition-0.0.17x-UV-Coupling-And-Index-Theorem-Connection.md) |
| 16 | -1 | Prop 0.0.17y | Bootstrap Fixed Point Uniqueness | [foundations/Proposition-0.0.17y](foundations/Proposition-0.0.17y-Bootstrap-Fixed-Point-Uniqueness.md) |
| 17 | -1 | Prop 0.0.17z | Non-Perturbative Corrections To Bootstrap | [foundations/Proposition-0.0.17z](foundations/Proposition-0.0.17z-Non-Perturbative-Corrections-To-Bootstrap.md) |
| 18 | -1 | Prop 0.0.17z1 | Geometric Derivation Non-Perturbative Coefficients | [foundations/Proposition-0.0.17z1](foundations/Proposition-0.0.17z1-Geometric-Derivation-Non-Perturbative-Coefficients.md) |
| 19 | -1 | Prop 0.0.17z2 | Scale-Dependent Effective Euler Characteristic | [foundations/Proposition-0.0.17z2](foundations/Proposition-0.0.17z2-Scale-Dependent-Effective-Euler-Characteristic.md) |
| 20 | -1 | Prop 0.0.35 | Dimensional Uniqueness Of R_stella | [foundations/Proposition-0.0.35](foundations/Proposition-0.0.35-Dimensional-Uniqueness-Of-R-Stella.md) (3-file) |
| 21 | -1 | Prop 0.0.36 | Anthropic Bounds On R_stella | [foundations/Proposition-0.0.36](foundations/Proposition-0.0.36-Anthropic-Bounds-On-R-Stella.md) |
| 22 | -1 | Thm 0.0.41 | Dimensional Incompleteness | [foundations/Theorem-0.0.41](foundations/Theorem-0.0.41-Dimensional-Incompleteness.md) |
| 23 | -1 | Prop 0.0.41a | CG Dimensional Optimality | [foundations/Proposition-0.0.41a](foundations/Proposition-0.0.41a-CG-Dimensional-Optimality.md) |
| 24 | 2 | Drv 2.1.2c | Bag Constant From Stella Geometry | [Phase2/Derivation-2.1.2c](Phase2/Derivation-2.1.2c-Bag-Constant-From-Stella-Geometry.md) |

### Internal dependency chain (the derivation chain)
```
R_stella = 0.44847 fm (observed input)
     │
     ├──→ Prop 0.0.17j: √σ = ℏc/R = 440 MeV (string tension)
     │         │
     │         ├──→ Prop 0.0.17k: f_π = √σ/5 = 88.0 MeV
     │         │         │
     │         │         ├──→ Prop 0.0.17k1: NLO correction → 92.4 MeV
     │         │         ├──→ Prop 0.0.17k2-k4: O(p⁴) matching
     │         │         └──→ Prop 0.0.17m: v_χ = f_π (energy matching)
     │         │
     │         ├──→ Prop 0.0.17l: ω = √σ/(N_c-1) = 219 MeV
     │         │
     │         ├──→ Prop 0.0.17d: Λ = 4πf_π = 1106 MeV
     │         │
     │         └──→ Drv 2.1.2c: B^{1/4} = √σ/N_c = 146.7 MeV (bag constant)
     │
     ├──→ Prop 0.0.17o: ε = 1/2 (Casimir mode structure)
     │
     ├──→ Prop 0.0.17q: R_stella ↔ M_P (dimensional transmutation)
     │
     └──→ Prop 0.0.17r: a² = (8/√3)ln(3)ℓ_P² (lattice spacing)

Bootstrap self-consistency check:
     Prop 0.0.17y (Fixed point) → Prop 0.0.17z (Non-perturbative corrections)
          → Predicts R_stella = 0.454 fm (1.2% from observed)

Metatheoretic capstone:
     Prop 0.0.35 (R_stella unique dimensional source) ─┐
     Prop 5.2.5e (Holographic no-go) ──────────────────┤
     Buckingham Pi theorem ─────────────────────────────┘
          → Thm 0.0.41 (Dimensional Incompleteness: 1 input is minimum)
               → Prop 0.0.41a (CG saturates the bound: N_total = 1)
```

### Cross-group imports
- **← G1:** R_stella, stella topology (for Casimir computation)
- **← G2:** SU(3) structure constants (for mode counting)

### Cross-group exports
- **→ G2:** α_s via Prop 0.0.17s
- **→ G5:** f_π, v_χ, ω, ε (all CG Lagrangian parameters)
- **→ G8:** √σ → M_P hierarchy (Prop 0.0.17q, 0.0.17t)
- **→ G10:** σ for lattice mass gap comparison
- **→ G11:** Bootstrap consistency check (Props 0.0.17y-z)
- **→ G12:** All numerical predictions

### Coherence checklist
- [ ] R_stella = 0.44847 fm (observed) is used for all downstream predictions, NEVER R_stella = 0.454 fm (bootstrap-predicted)
- [ ] √σ = 440 MeV appears identically in G2 (Wilson loops), G5 (mass formula), G10 (lattice), G12 (predictions)
- [ ] f_π = 88.0 MeV (tree-level) vs 92.4 MeV (NLO-corrected): which is used where must be explicit
- [ ] Denominator in f_π formula: (N_c-1) + (N_f²-1) = 5 — N_f = 2 (not 3 or 6) justified consistently
- [ ] ω = 219 MeV matches what G3 uses for t = λ/ω conversion
- [ ] Lattice spacing (Prop 0.0.17r) is consistent with G10 FCC lattice proofs
- [ ] Bootstrap prediction 0.454 fm vs observed 0.44847 fm: 1.2% discrepancy is correctly characterized everywhere

---

## G7: Quantum Foundations

**Core question:** Do the Born rule, decoherence, and measurement emerge from the pre-geometric structure?

**Unification points touched:** None directly (G7 establishes quantum interpretation)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | -1 | Thm 0.0.10 | Quantum Mechanics Emergence | [foundations/Theorem-0.0.10](foundations/Theorem-0.0.10-Quantum-Mechanics-Emergence.md) |
| 2 | -1 | Thm 0.0.17 | Information-Geometric Unification | [foundations/Theorem-0.0.17](foundations/Theorem-0.0.17-Information-Geometric-Unification.md) |
| 3 | -1 | Prop 0.0.17b | Fisher Metric Uniqueness | [foundations/Proposition-0.0.17b](foundations/Proposition-0.0.17b-Fisher-Metric-Uniqueness.md) |
| 4 | -1 | Lem 0.0.17c | Fisher-Killing Equivalence | [foundations/Lemma-0.0.17c](foundations/Lemma-0.0.17c-Fisher-Killing-Equivalence.md) |
| 5 | -1 | Prop 0.0.17a | Born Rule From Geodesic Flow | [foundations/Proposition-0.0.17a](foundations/Proposition-0.0.17a-Born-Rule-From-Geodesic-Flow.md) |
| 6 | -1 | Prop 0.0.17e | Square-Integrability From Finite Energy | [foundations/Proposition-0.0.17e](foundations/Proposition-0.0.17e-Square-Integrability-From-Finite-Energy.md) |
| 7 | -1 | Prop 0.0.17f | Decoherence From Geodesic Mixing | [foundations/Proposition-0.0.17f](foundations/Proposition-0.0.17f-Decoherence-From-Geodesic-Mixing.md) |
| 8 | -1 | Prop 0.0.17g | Objective Collapse From Z₃ Discretization | [foundations/Proposition-0.0.17g](foundations/Proposition-0.0.17g-Objective-Collapse-From-Z3-Discretization.md) |
| 9 | -1 | Prop 0.0.17h | Information Horizon Derivation | [foundations/Proposition-0.0.17h](foundations/Proposition-0.0.17h-Information-Horizon-Derivation.md) |
| 10 | -1 | Prop 0.0.17i | Z₃ Measurement Extension | [foundations/Proposition-0.0.17i](foundations/Proposition-0.0.17i-Z3-Measurement-Extension.md) |
| 11 | -1 | Def 0.0.32 | Internal Observer | [foundations/Definition-0.0.32](foundations/Definition-0.0.32-Internal-Observer.md) |
| 12 | -1 | Prop 0.0.32a | Observer Fixed Point | [foundations/Proposition-0.0.32a](foundations/Proposition-0.0.32a-Observer-Fixed-Point.md) |
| 13 | -1 | Prop 0.0.34 | Observer Participation | [foundations/Proposition-0.0.34](foundations/Proposition-0.0.34-Observer-Participation.md) |

### Internal dependency chain
```
Thm 0.0.17 (Information-geometric unification)
     ↓
Prop 0.0.17b (Fisher metric uniqueness via Chentsov)
     ↓
┌────┼────┬────────────┐
↓    ↓    ↓            ↓
17a  17e  17f        Def 0.0.32
Born L²   Decoherence  (Observer)
rule      ↓            ↓
          17g → 17h → 17i
          Collapse  Horizons  Z₃ measurement
```

### Cross-group imports
- **← G1:** SU(3) structure, Z₃ center (for discretization mechanism)

### Cross-group exports
- **→ G3:** Born rule probability interpretation (Prop 0.0.17a)
- **→ G5:** L² integrability condition (Prop 0.0.17e) for field normalization
- **→ G10:** Unitarity foundation for S-matrix (Thm 7.2.1)

### Coherence checklist
- [ ] Fisher metric (Prop 0.0.17b) = Killing metric (Lem 0.0.17c): proven rigorously, not just claimed similar
- [ ] Born rule (Prop 0.0.17a) from ergodicity: the ergodic limit is justified for physical systems
- [ ] Decoherence (Prop 0.0.17f) and collapse (Prop 0.0.17g) are complementary, not contradictory
- [ ] Z₃ discretization in collapse (0.0.17g) uses the same Z₃ as in G4 (chirality) and G6 (N_c structure)
- [ ] Observer definition (Def 0.0.32) is compatible with the observer in Thm 0.0.1 (D=4)
- [ ] No hidden collapse postulate — everything derives from geodesic mixing + Z₃

---

## G8: Emergent Gravity

**Core question:** Does general relativity emerge from pre-geometric dynamics? Does the framework predict G_N, Λ_cosm, and black hole thermodynamics?

**Unification points touched:** UP2 (Energy & Stress-Energy), UP6 (Metric/Gravity Emergence), UP7 (Vacuum Energy Cancellation)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | -1 | Thm 0.0.0 | GR Conditions Derivation | [foundations/Theorem-0.0.0](foundations/Theorem-0.0.0-GR-Conditions-Derivation.md) |
| 2 | -1 | Thm 0.0.11 | Lorentz Boost Emergence | [foundations/Theorem-0.0.11](foundations/Theorem-0.0.11-Lorentz-Boost-Emergence.md) |
| 3 | -1 | Thm 0.0.7 | Lorentz Violation Bounds | [foundations/Theorem-0.0.7](foundations/Theorem-0.0.7-Lorentz-Violation-Bounds.md) |
| 4 | -1 | Thm 0.0.8 | Emergent Rotational Symmetry | [foundations/Theorem-0.0.8](foundations/Theorem-0.0.8-Emergent-Rotational-Symmetry.md) |
| 5 | -1 | Thm 0.0.14 | Novel Lorentz Violation Pattern | [foundations/Theorem-0.0.14](foundations/Theorem-0.0.14-Novel-Lorentz-Violation-Pattern.md) |
| 6 | -1 | Prop 0.0.17t | Topological Origin of Scale Hierarchy | [foundations/Proposition-0.0.17t](foundations/Proposition-0.0.17t-Topological-Origin-Of-Scale-Hierarchy.md) |
| 7 | -1 | Prop 0.0.17ab | Newton's Constant From Topology | [foundations/Proposition-0.0.17ab](foundations/Proposition-0.0.17ab-Newtons-Constant-From-Topology.md) (3-file) |
| 8 | 5 | Thm 5.1.1 | Stress-Energy Tensor | [Phase5/Theorem-5.1.1](Phase5/Theorem-5.1.1-Stress-Energy-Tensor.md) |
| 9 | 5 | Thm 5.1.2 | Vacuum Energy Density | [Phase5/Theorem-5.1.2](Phase5/Theorem-5.1.2-Vacuum-Energy-Density.md) (3-file) |
| 10 | 5 | Prop 5.1.2a | Matter Density From Geometry | [Phase5/Proposition-5.1.2a](Phase5/Proposition-5.1.2a-Matter-Density-From-Geometry.md) |
| 11 | 5 | Prop 5.1.2b | Precision Cosmological Densities | [Phase5/Proposition-5.1.2b](Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) |
| 12 | 5 | Thm 5.2.0 | Wick Rotation Validity | [Phase5/Theorem-5.2.0](Phase5/Theorem-5.2.0-Wick-Rotation-Validity.md) |
| 13 | 5 | Thm 5.2.1 | Emergent Metric | [Phase5/Theorem-5.2.1](Phase5/Theorem-5.2.1-Emergent-Metric.md) (3-file) |
| 14 | 5 | Prop 5.2.1b | Einstein Equations From Fixed Point Uniqueness | [Phase5/Proposition-5.2.1b](Phase5/Proposition-5.2.1b-Einstein-Equations-From-Fixed-Point-Uniqueness.md) |
| 15 | 5 | Thm 5.2.2 | Pre-Geometric Cosmic Coherence | [Phase5/Theorem-5.2.2](Phase5/Theorem-5.2.2-Pre-Geometric-Cosmic-Coherence.md) |
| 16 | 5 | Thm 5.2.3 | Einstein Equations (Thermodynamic) | [Phase5/Theorem-5.2.3](Phase5/Theorem-5.2.3-Einstein-Equations-Thermodynamic.md) (3-file) |
| 17 | 5 | Prop 5.2.3a | Local Thermodynamic Equilibrium | [Phase5/Proposition-5.2.3a](Phase5/Proposition-5.2.3a-Local-Thermodynamic-Equilibrium.md) |
| 18 | 5 | Prop 5.2.3b | FCC Lattice Entropy | [Phase5/Proposition-5.2.3b](Phase5/Proposition-5.2.3b-FCC-Lattice-Entropy.md) |
| 19 | 5 | Lem 5.2.3b.1 | Lattice Spacing Coefficient | [Phase5/Lemma-5.2.3b.1](Phase5/Lemma-5.2.3b.1-Lattice-Spacing-Coefficient.md) |
| 20 | 5 | Lem 5.2.3b.2 | Z₃ Discretization Mechanism | [Phase5/Lemma-5.2.3b.2](Phase5/Lemma-5.2.3b.2-Z3-Discretization-Mechanism.md) |
| 21 | 5 | Thm 5.2.4 | Newton's Constant From Chiral Parameters | [Phase5/Theorem-5.2.4](Phase5/Theorem-5.2.4-Newtons-Constant-Chiral-Parameters.md) (3-file) |
| 22 | 5 | Prop 5.2.4a | Induced Gravity From Chiral One-Loop | [Phase5/Proposition-5.2.4a](Phase5/Proposition-5.2.4a-Induced-Gravity-From-Chiral-One-Loop.md) |
| 23 | 5 | Prop 5.2.4b | Spin-2 From Stress-Energy Conservation | [Phase5/Proposition-5.2.4b](Phase5/Proposition-5.2.4b-Spin-2-From-Stress-Energy-Conservation.md) |
| 24 | 5 | Prop 5.2.4c | Tensor Rank From Derivative Structure | [Phase5/Proposition-5.2.4c](Phase5/Proposition-5.2.4c-Tensor-Rank-From-Derivative-Structure.md) |
| 25 | 5 | Prop 5.2.4d | Geometric Higher-Spin Exclusion | [Phase5/Proposition-5.2.4d](Phase5/Proposition-5.2.4d-Geometric-Higher-Spin-Exclusion.md) |
| 26 | 5 | Thm 5.2.5 | Bekenstein-Hawking Coefficient | [Phase5/Theorem-5.2.5](Phase5/Theorem-5.2.5-Bekenstein-Hawking-Coefficient.md) (3-file) |
| 27 | 5 | Drv 5.2.5a | Surface Gravity | [Phase5/Derivation-5.2.5a](Phase5/Derivation-5.2.5a-Surface-Gravity.md) |
| 28 | 5 | Drv 5.2.5b | Hawking Temperature | [Phase5/Derivation-5.2.5b](Phase5/Derivation-5.2.5b-Hawking-Temperature.md) |
| 29 | 5 | Drv 5.2.5c | First Law and Entropy | [Phase5/Derivation-5.2.5c](Phase5/Derivation-5.2.5c-First-Law-and-Entropy.md) |
| 29a | 5 | Prop 5.2.5e | Holographic Self-Encoding Scale Invariance | [Phase5/Proposition-5.2.5e](Phase5/Proposition-5.2.5e-Holographic-Self-Encoding-Scale-Invariance.md) |
| 30 | 5 | Thm 5.2.6 | Planck Mass Emergence | [Phase5/Theorem-5.2.6](Phase5/Theorem-5.2.6-Planck-Mass-Emergence.md) (3-file) |
| 31 | 5 | Thm 5.2.7 | Diffeomorphism Emergence | [Phase5/Theorem-5.2.7](Phase5/Theorem-5.2.7-Diffeomorphism-Emergence.md) |
| 32 | 5 | Thm 5.3.1 | Torsion From Chiral Current | [Phase5/Theorem-5.3.1](Phase5/Theorem-5.3.1-Torsion-From-Chiral-Current.md) |
| 33 | 5 | Thm 5.3.2 | Spin-Orbit Coupling | [Phase5/Theorem-5.3.2](Phase5/Theorem-5.3.2-Spin-Orbit-Coupling.md) (3-file) |
| 34 | 5 | Lem 5.4.1a | Maximum Curvature Bound | [Phase5/Lemma-5.4.1a](Phase5/Lemma-5.4.1a-Maximum-Curvature-Bound.md) |
| 35 | 5 | Thm 5.4.1 | Singularity Resolution Emergent Gravity | [Phase5/Theorem-5.4.1](Phase5/Theorem-5.4.1-Singularity-Resolution-Emergent-Gravity.md) (3-file) |
| 36 | -1 | Prop 0.0.30 | Holographic Saturation From Thermodynamic Equilibrium | [foundations/Proposition-0.0.30](foundations/Proposition-0.0.30-Holographic-Saturation-From-Thermodynamic-Equilibrium.md) |
| 37 | -1 | Prop 0.0.17v | Holographic Scale From Self-Consistency | [foundations/Proposition-0.0.17v](foundations/Proposition-0.0.17v-Holographic-Scale-From-Self-Consistency.md) |
| 38 | -1 | Prop 0.0.17u | Cosmological Initial Conditions | [foundations/Proposition-0.0.17u](foundations/Proposition-0.0.17u-Cosmological-Initial-Conditions-From-Pre-Geometry.md) |
| 39 | 0 | Thm 0.3.1 | W-Direction Correspondence | [Phase0/Theorem-0.3.1](Phase0/Theorem-0.3.1-W-Direction-Correspondence.md) |

### Internal dependency chain
```
Thm 5.1.1 (Stress-energy T_μν)
     ↓
Thm 5.1.2 (Vacuum energy) → Prop 5.1.2a-b (Cosmological densities)
     ↓
Thm 5.2.1 (Emergent metric g_μν)
     ↓
┌────┼──────────────────┬──────────────────┐
↓    ↓                  ↓                  ↓
5.2.3 (Einstein eqs)  5.2.4 (G_N)       5.2.7 (Diffeos)
  ↓                      ↓
5.2.5 (BH entropy)    5.2.6 (M_Planck)
  ↓
5.3.1-2 (Torsion, spin-orbit)
  ↓
Lem 5.4.1a (Max curvature R_max = 8/a²) ← Thm 0.0.6, Prop 0.0.17r
  ↓
Thm 5.4.1 (Singularity resolution) ← 5.1.1, 5.2.1, 5.3.1, Prop 5.2.1b
```

### Cross-group imports
- **← G1:** D=4 structure, stella geometry
- **← G3:** Internal time λ, pre-geometric energy E[χ], Wick rotation
- **← G5:** Massive fields (stress-energy source)
- **← G6:** √σ for scale hierarchy (Prop 0.0.17t)

### Cross-group exports
- **→ G10:** Gravitational sector UV completeness (Thm 7.3.1)
- **→ G11:** Fixed-point uniqueness feedback
- **→ G12:** G_N prediction, cosmological constant, BH entropy, Lorentz violation pattern

### Coherence checklist
- [ ] T_μν (Thm 5.1.1) is symmetric, conserved (∇_μ T^μν = 0), and reduces to E[χ] for static configs
- [ ] Einstein equations derived thermodynamically (Thm 5.2.3) match fixed-point derivation (Prop 5.2.1b)
- [ ] G_N from chiral parameters (Thm 5.2.4) agrees with G_N from topology (Prop 0.0.17ab)
- [ ] Planck mass (Thm 5.2.6) is consistent with hierarchy (Prop 0.0.17t) and dimensional transmutation (Prop 0.0.17q in G6)
- [ ] Vacuum energy cancellation mechanism is the same at all scales (UP7)
- [ ] Metric signature (−+++) is consistent everywhere; Euclidean (+++) only in Wick-rotated context
- [ ] Cosmological densities (Prop 5.1.2b) match Planck 2018 data
- [ ] Singularity resolution (Thm 5.4.1) uses R_max = 8/a² ≈ 1.58/ℓ_P² from Lem 5.4.1a (properly normalized FCC Laplacian)

---

## G9: Electroweak Sector

**Core question:** Can SU(2)×U(1), the Higgs potential, and EW parameters be derived from the stella octangula geometry?

**Unification points touched:** UP3 (Chirality), UP5 (Mass Generation), UP7 (Vacuum Energy)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | -1 | Prop 0.0.22 | SU(2) Substructure From Stella | [foundations/Proposition-0.0.22](foundations/Proposition-0.0.22-SU2-Substructure-From-Stella-Octangula.md) |
| 2 | -1 | Prop 0.0.23 | Hypercharge From Geometric Embedding | [foundations/Proposition-0.0.23](foundations/Proposition-0.0.23-Hypercharge-From-Geometric-Embedding.md) |
| 3 | -1 | Prop 0.0.18 | Electroweak Scale From χ Field | [foundations/Proposition-0.0.18](foundations/Proposition-0.0.18-Electroweak-Scale-From-Chi-Field.md) |
| 4 | -1 | Prop 0.0.19 | Electroweak Topological Index | [foundations/Proposition-0.0.19](foundations/Proposition-0.0.19-Electroweak-Topological-Index.md) |
| 5 | -1 | Prop 0.0.20 | Electroweak Scale From Central Charge Flow | [foundations/Proposition-0.0.20](foundations/Proposition-0.0.20-Electroweak-Scale-From-Central-Charge-Flow.md) |
| 6 | -1 | Prop 0.0.21 | Unified Electroweak Scale Derivation | [foundations/Proposition-0.0.21](foundations/Proposition-0.0.21-Unified-Electroweak-Scale-Derivation.md) |
| 7 | -1 | Prop 0.0.24 | SU(2) Gauge Coupling From Unification | [foundations/Proposition-0.0.24](foundations/Proposition-0.0.24-SU2-Gauge-Coupling-From-Unification.md) |
| 8 | -1 | Prop 0.0.24a | Electroweak Precision Oblique Parameters | [foundations/Proposition-0.0.24a](foundations/Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md) |
| 9 | -1 | Prop 0.0.25 | α_GUT Threshold Formula | [foundations/Proposition-0.0.25](foundations/Proposition-0.0.25-Alpha-GUT-Threshold-Formula.md) |
| 10 | -1 | Prop 0.0.26 | Electroweak Cutoff Derivation | [foundations/Proposition-0.0.26](foundations/Proposition-0.0.26-Electroweak-Cutoff-Derivation.md) |
| 11 | -1 | Prop 0.0.27 | Higgs Mass From Geometry | [foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry](foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md) |
| 12 | -1 | Prop 0.0.27a | Quartic Normalization From Equipartition | [foundations/Proposition-0.0.27a](foundations/Proposition-0.0.27a-Quartic-Normalization-From-Equipartition.md) |
| 13 | -1 | Prop 0.0.37 | Complete Higgs Potential & Trilinear Coupling | [foundations/Proposition-0.0.37](foundations/Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md) |
| 14 | 6 | Thm 6.6.1 | Electroweak Scattering | [Phase6/Theorem-6.6.1](Phase6/Theorem-6.6.1-Electroweak-Scattering.md) |
| 15 | 6 | Thm 6.7.1 | EW Gauge Fields From 24-Cell | [Phase6/Theorem-6.7.1](Phase6/Theorem-6.7.1-Electroweak-Gauge-Fields-From-24-Cell.md) |
| 16 | 6 | Thm 6.7.2 | EW Symmetry Breaking Dynamics | [Phase6/Theorem-6.7.2](Phase6/Theorem-6.7.2-Electroweak-Symmetry-Breaking-Dynamics.md) |
| 17 | 3 | Thm 3.2.1 | Low-Energy Equivalence | [Phase3/Theorem-3.2.1](Phase3/Theorem-3.2.1-Low-Energy-Equivalence.md) (3-file) |
| 18 | 3 | Thm 3.2.2 | High-Energy Deviations | [Phase3/Theorem-3.2.2](Phase3/Theorem-3.2.2-High-Energy-Deviations.md) |

### Internal dependency chain
```
Prop 0.0.22 (SU(2) from stella) + Prop 0.0.23 (U(1)_Y from embedding)
     ↓
Prop 0.0.18-21 (EW scale derivations — 4 independent routes)
     ↓
Prop 0.0.24 (g₂ coupling) + Prop 0.0.25 (α_GUT threshold)
     ↓
Prop 0.0.27 (m_H) + Prop 0.0.37 (Full Higgs potential)
     ↓
Thm 6.7.1-2 (EW gauge fields, EWSB dynamics)
     ↓
Thm 3.2.1 (SM equivalence at low E)
```

### Cross-group imports
- **← G1:** Stella octangula substructure (T₊/T₋ → SU(2))
- **← G4:** Chirality selection (left-handedness)
- **← G5:** Phase-gradient ↔ Higgs equivalence (Thm 3.2.1)
- **← G6:** QCD scale (for unification running)

### Cross-group exports
- **→ G12:** Higgs mass, EW precision, W/Z masses, high-energy deviations

### Coherence checklist
- [ ] SU(2) embedding (Prop 0.0.22) is consistent with the SU(3) of G1/G2
- [ ] Four EW scale derivations (Props 0.0.18-21) give the SAME numerical value
- [ ] Higgs mass (Prop 0.0.27) uses same quartic as complete potential (Prop 0.0.37)
- [ ] Oblique parameters (Prop 0.0.24a) are within experimental bounds
- [ ] 24-cell structure (Thm 6.7.1) is geometrically related to stella octangula
- [ ] EW chirality (left-handed SU(2)) connects to the same chirality mechanism as G4

---

## G10: Renormalization & Yang-Mills

**Core question:** Is the CG framework mathematically rigorous? Does it satisfy the Osterwalder-Schrader axioms and have a mass gap?

**Unification points touched:** UP4 (Instanton Physics), UP5 (Mass Generation)

### Proofs (dependency order)

**Subgroup G10a: Power counting & S-matrix**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | 7 | Thm 7.1.1 | Power Counting | [Phase7/Theorem-7.1.1](Phase7/Theorem-7.1.1-Power-Counting.md) (3-file) |
| 2 | 7 | Thm 7.2.1 | S-Matrix Unitarity | [Phase7/Theorem-7.2.1](Phase7/Theorem-7.2.1-S-Matrix-Unitarity.md) |
| 3 | 7 | Thm 7.3.1 | UV Completeness Emergent Gravity | [Phase7/Theorem-7.3.1](Phase7/Theorem-7.3.1-UV-Completeness-Emergent-Gravity.md) (3-file) |

**Subgroup G10b: FCC lattice foundations**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 4 | 7 | Thm 7.4.1 | Reflection Positivity FCC | [Phase7/Theorem-7.4.1](Phase7/Theorem-7.4.1-Reflection-Positivity-FCC.md) (3-file) |
| 5 | 7 | Thm 7.4.2 | Mass Gap Thermodynamic Limit FCC | [Phase7/Theorem-7.4.2](Phase7/Theorem-7.4.2-Mass-Gap-Thermodynamic-Limit-FCC.md) (3-file) |
| 6 | 7 | Prop 7.4.3 | FCC Lattice Perturbation Theory | [Phase7/Proposition-7.4.3](Phase7/Proposition-7.4.3-FCC-Lattice-Perturbation-Theory.md) (3-file) |
| 7 | 7 | Prop 7.4.4 | Scaling Window FCC | [Phase7/Proposition-7.4.4](Phase7/Proposition-7.4.4-Scaling-Window-FCC.md) (3-file) |
| 8 | 7 | Prop 7.4.4a | Exact Wilson Loop FCC | [Phase7/Proposition-7.4.4a](Phase7/Proposition-7.4.4a-Exact-Wilson-Loop-FCC.md) |
| 9 | 7 | Thm 7.4.5 | Continuum Mass Gap FCC | [Phase7/Theorem-7.4.5](Phase7/Theorem-7.4.5-Continuum-Mass-Gap-FCC.md) (3-file) |
| 10 | 7 | Thm 7.4.6 | OS Axioms CG Yang-Mills | [Phase7/Theorem-7.4.6](Phase7/Theorem-7.4.6-OS-Axioms-CG-Yang-Mills.md) (3-file) |
| 11 | 7 | Thm 7.4.7 | CG Yang-Mills Mass Gap | [Phase7/Theorem-7.4.7](Phase7/Theorem-7.4.7-CG-Yang-Mills-Mass-Gap.md) (3-file) |

**Subgroup G10c: Universality & continuum limit**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 12 | 7 | Prop 7.5.1 | Symanzik Effective Theory FCC | [Phase7/Proposition-7.5.1](Phase7/Proposition-7.5.1-Symanzik-Effective-Theory-FCC.md) (3-file) |
| 13 | 7 | Thm 7.5.2 | Perturbative Universality FCC | [Phase7/Theorem-7.5.2](Phase7/Theorem-7.5.2-Perturbative-Universality-FCC.md) (3-file) |
| 14 | 7 | Thm 7.5.3 | Bulk Transition Termination FCC | [Phase7/Theorem-7.5.3](Phase7/Theorem-7.5.3-Bulk-Transition-Termination-FCC.md) (3-file) |
| 15 | 7 | Thm 7.5.4 | Non-Perturbative Universality FCC | [Phase7/Theorem-7.5.4](Phase7/Theorem-7.5.4-Non-Perturbative-Universality-FCC.md) (3-file) |

**Subgroup G10d: Multi-scale RG & constructive mass gap**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 16 | 7 | Prop 7.6.1 | FCC Averaging Kernel | [Phase7/Proposition-7.6.1](Phase7/Proposition-7.6.1-FCC-Averaging-Kernel.md) (3-file) |
| 17 | 7 | Prop 7.6.2 | FCC Propagator Bounds | [Phase7/Proposition-7.6.2](Phase7/Proposition-7.6.2-FCC-Propagator-Bounds.md) (3-file) |
| 18 | 7 | Prop 7.6.3 | Regular Configurations Variational Problem | [Phase7/Proposition-7.6.3](Phase7/Proposition-7.6.3-Regular-Configurations-Variational-Problem.md) (3-file) |
| 19 | 7 | Prop 7.6.4 | Large Field Estimates | [Phase7/Proposition-7.6.4](Phase7/Proposition-7.6.4-Large-Field-Estimates.md) (3-file) |
| 20 | 7 | Thm 7.6.5 | Small Field UV Stability | [Phase7/Theorem-7.6.5](Phase7/Theorem-7.6.5-Small-Field-UV-Stability.md) (3-file) |
| 21 | 7 | Prop 7.6.6 | Correlation Decay Weak Coupling D=4 | [Phase7/Proposition-7.6.6](Phase7/Proposition-7.6.6-Correlation-Decay-Weak-Coupling-D4.md) (3-file) |
| 22 | 7 | Thm 7.6.7 | Infrared Coercivity Exact Mass Gap | [Phase7/Theorem-7.6.7](Phase7/Theorem-7.6.7-Infrared-Coercivity-Exact-Mass-Gap.md) (3-file) |
| 23 | 7 | Thm 7.6.8 | Effective Action Convergence Multi-Scale RG D=4 | [Phase7/Theorem-7.6.8](Phase7/Theorem-7.6.8-Effective-Action-Convergence-Multi-Scale-RG-D4.md) (3-file) |
| 24 | 7 | Prop 7.6.9 | Scaling Window Mass Ratio Stabilization D=4 | [Phase7/Proposition-7.6.9](Phase7/Proposition-7.6.9-Scaling-Window-Mass-Ratio-Stabilization-D4.md) (3-file) |

**Subgroup G10e: Capstone mass gap proof**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 25 | 7 | Thm 7.6.10 | Constructive SU(3) Yang-Mills Mass Gap D=4 | [Phase7/Theorem-7.6.10](Phase7/Theorem-7.6.10-Constructive-SU3-Yang-Mills-Mass-Gap-D4.md) (3-file) |
| 26 | 7 | Thm 7.7.1 | Unconditional OS/FOS Axioms SU(3) Yang-Mills | [Phase7/Theorem-7.7.1](Phase7/Theorem-7.7.1-Unconditional-OS-FOS-Axioms-SU3-Yang-Mills.md) |
| 27 | 7 | Thm 7.7.2 | Wightman Reconstruction Mass Gap | [Phase7/Theorem-7.7.2](Phase7/Theorem-7.7.2-Wightman-Reconstruction-Mass-Gap-SU3-Yang-Mills.md) |
| 28 | 7 | Thm 7.7.3 | Quantitative Mass Gap Lower Bound | [Phase7/Theorem-7.7.3](Phase7/Theorem-7.7.3-Quantitative-Mass-Gap-Lower-Bound-SU3-Yang-Mills.md) |
| 29 | 7 | Thm 7.7.4 | Yang-Mills Mass Gap General Compact Simple G | [Phase7/Theorem-7.7.4](Phase7/Theorem-7.7.4-Yang-Mills-Mass-Gap-General-Compact-Simple-G.md) |
| 30 | 7 | Thm 7.7.5 | Yang-Mills Mass Gap Complete Proof | [Phase7/Theorem-7.7.5](Phase7/Theorem-7.7.5-Yang-Mills-Mass-Gap-Complete-Proof.md) (3-file) |
| 31 | 7 | Prop 7.8.1 | Exceptional Group Glueball Predictions | [Phase7/Proposition-7.8.1](Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions.md) (3-file) |
| 32 | 7 | Prop 7.8.2 | Framework-Internal Glueball Mass Ratio | [Phase7/Proposition-7.8.2](Phase7/Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio.md) (3-file) |
| 33 | 7 | Prop 7.8.3 | Bethe-Salpeter Glueball Mass Ratio | [Phase7/Proposition-7.8.3](Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md) (3-file) |
| 34 | 7 | Prop 7.8.4 | V-Scheme BLM Glueball Mass Ratio | [Phase7/Proposition-7.8.4](Phase7/Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio.md) (3-file) |
| 35 | 7 | Prop 7.8.5 | Explicit Crossover Mass Gap Computation | [Phase7/Proposition-7.8.5](Phase7/Proposition-7.8.5-Explicit-Crossover-Mass-Gap-Computation.md) (3-file) |
| 36 | 7 | Prop 7.8.6 | Full Two-Gluon Glueball Spectrum | [Phase7/Proposition-7.8.6](Phase7/Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum.md) (3-file) |
| 37 | 7 | Prop 7.8.7 | Three-Gluon Glueball Spectrum | [Phase7/Proposition-7.8.7](Phase7/Proposition-7.8.7-Three-Gluon-Glueball-Spectrum.md) (3-file) · [Lean 4](../../lean/ChiralGeometrogenesis/Phase7/Proposition_7_8_7.lean) |

**Subgroup G10h: Dynamical fermion extension**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 38 | 7 | Prop 7.9.1 | Mass Gap Persistence with Dynamical Fermions | [Phase7/Proposition-7.9.1](Phase7/Proposition-7.9.1-Mass-Gap-Dynamical-Fermions.md) (3-file) |

### Internal dependency chain
```
G10a: Thm 7.1.1 → 7.2.1 → 7.3.1 (power counting → unitarity → UV completeness)

G10b: Thm 7.4.1 → 7.4.2 → Prop 7.4.3 → Prop 7.4.4 → Thm 7.4.5 → 7.4.6 → 7.4.7
      (reflection positivity → mass gap → perturbation theory → scaling → continuum → OS → mass gap)

G10c: Prop 7.5.1 → Thm 7.5.2 → 7.5.3 → 7.5.4
      (Symanzik → perturbative universality → bulk transition → non-perturbative universality)

G10d: Prop 7.6.1 → 7.6.2 → 7.6.3 → 7.6.4 → Thm 7.6.5 → Prop 7.6.6 → Thm 7.6.7 → 7.6.8 → Prop 7.6.9
      (kernel → propagator → regular configs → large field → UV stability → decay → IR coercivity → convergence → scaling)

G10e: Thm 7.6.10 → 7.7.1 → 7.7.2 → 7.7.3 → 7.7.4 → 7.7.5
      (constructive SU(3) gap → OS axioms → Wightman → quantitative bound → general G → complete)

G10f: Prop 7.8.1 → Prop 7.8.2 → Prop 7.8.3 → Prop 7.8.4 → Prop 7.8.6 → Prop 7.8.7
      (exceptional glueballs → framework-internal R_cont → Bethe-Salpeter cross-check → V-scheme BLM refinement → full two-gluon spectrum → three-gluon C=-1 spectrum)

G10g: Prop 7.6.6 → Prop 7.8.5 → Thm 7.7.3
      (abstract μ_min existence → explicit μ_min(ε*) computation → framework-internal quantitative mass gap bound)

G10h: Thm 7.7.3 + Thm 7.3.2 + Thm 7.4.1 → Prop 7.9.1
      (pure-gauge mass gap + β-functions(N_f) + FCC RP → mass gap with dynamical fermions)
```

### Cross-group imports
- **← G2:** Asymptotic freedom (Thm 7.3.2-3), CG Lagrangian (Thm 2.5.1)
- **← G6:** String tension σ (for mass gap numerical comparison)
- **← G7:** Unitarity foundation
- **← G8:** Wick rotation validity (Thm 5.2.0)

### Cross-group exports
- **→ G12:** Mass gap predictions, glueball spectrum (Prop 7.8.1, 7.8.2, 7.8.3, 7.8.4, 7.8.5, 7.8.6, 7.8.7)
- **→ G11:** Mathematical consistency confirmation

### Coherence checklist
- [ ] FCC lattice in G10b matches FCC from Thm 0.0.6 (G1) — same vertex structure
- [ ] Lattice spacing in G10b-d matches Prop 0.0.17r (G6)
- [ ] Reflection positivity (Thm 7.4.1) is on FCC, not hypercubic — differences acknowledged
- [ ] Mass gap lower bound (Thm 7.7.3) is consistent with √σ = 440 MeV from G6
- [ ] OS axioms (Thm 7.7.1) correctly use Wick-rotated correlators from Thm 5.2.0 (G8)
- [ ] Subgroups G10b-d form a genuinely linear dependency chain — no hidden circular dependencies
- [ ] Glueball predictions (Prop 7.8.1) use same mass gap as Thm 7.7.3
- [ ] Framework-internal $R_\text{cont}$ (Prop 7.8.2) uses Casimir scaling consistent with Prop 7.8.1
- [ ] Bethe-Salpeter estimate (Prop 7.8.3) combined with Prop 7.8.2 yields $c_\text{FI} = 6.76 \pm 0.45$ consistent with Thm 7.7.3
- [ ] V-scheme BLM refinement (Prop 7.8.4) uses $\alpha_V = 0.373 \pm 0.010$ consistent with lattice determinations and yields $c_\text{FI} = 6.87 \pm 0.14$ (supersedes Prop 7.8.3 coupling)
- [ ] Explicit crossover mass gap (Prop 7.8.5) uses $\varepsilon_* \approx 2.30$ consistent with $C_8/C_3 = 9/4$ from Thm 7.5.3, and $\mu_\text{min}(\varepsilon_*) > 0$ feeds into Thm 7.7.3
- [ ] Full two-gluon glueball spectrum (Prop 7.8.6) uses $\alpha_V = 0.373 \pm 0.010$ from Prop 7.8.4, Salpeter formula from Prop 7.8.3, and Casimir invariants from Prop 0.0.38; all 7 $J^{PC}$ states within $1\sigma$ of lattice data
- [ ] Three-gluon glueball spectrum (Prop 7.8.7) uses $\alpha_V = 0.373 \pm 0.010$ from Prop 7.8.4, 6D hyperradial extension of Prop 7.8.6, pure Casimir scaling $\sigma_\text{adj} = 9/4\,\sigma_\text{fund}$; all 7 $C = -1$ $J^{PC}$ states within $0.4\sigma$ of lattice data
- [ ] Dynamical fermion extension (Prop 7.9.1) uses $\kappa_c = 1/12$ consistent with 6 FCC direction pairs from Thm 7.4.1, and recovers $c(0) = 6.78$ from Thm 7.7.3

---

## G11: Bootstrap & Uniqueness

**Core question:** Is this the UNIQUE self-consistent physical theory on ∂S, or could other frameworks satisfy the same constraints?

**Unification points touched:** All (bootstrap must be consistent with everything)

### Proofs (dependency order)

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | -1 | Thm 0.0.18 | Signature Equations | [foundations/Theorem-0.0.18](foundations/Theorem-0.0.18-Signature-Equations.md) |
| 2 | -1 | Thm 0.0.19 | Quantitative Self-Reference Uniqueness | [foundations/Theorem-0.0.19](foundations/Theorem-0.0.19-Quantitative-Self-Reference-Uniqueness.md) |
| 3 | -1 | Prop 0.0.XXa | First Stable Principle | [foundations/Proposition-0.0.XXa](foundations/Proposition-0.0.XXa-First-Stable-Principle.md) |
| 4 | -1 | Prop 0.0.XXb | Bootstrap Computability | [foundations/Proposition-0.0.XXb](foundations/Proposition-0.0.XXb-Bootstrap-Computability.md) |
| 5 | -1 | Thm 0.0.XXc | Gödel Bootstrap Separation | [foundations/Theorem-0.0.XXc](foundations/Theorem-0.0.XXc-Godel-Bootstrap-Separation.md) (3-file) |
| 6 | -1 | Prop 0.0.XXd | Computational Universality of CG Primitives | [foundations/Proposition-0.0.XXd](foundations/Proposition-0.0.XXd-Computational-Universality-CG-Primitives.md) · [Lean 4](../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XXd.lean) |
| 6a | -1 | Prop 0.0.XXe | Continuum Limit of Self-Replicating Fields | [foundations/Proposition-0.0.XXe](foundations/Proposition-0.0.XXe-Continuum-Self-Replicating-Fields.md) |
| 6b | sup | Lem 0.0.XXe-BC | Bilayer Coupling κ = 1/2 | [supporting/Lemma-0.0.XXe-BC](supporting/Lemma-0.0.XXe-Bilayer-Coupling-Geometric-Derivation.md) · [Lean 4](../../lean/ChiralGeometrogenesis/PureMath/Polyhedra/BilayerCoupling.lean) |
| 6c | sup | Lem 0.0.XXe-NP | Nucleation Probability → 1 | [supporting/Lemma-0.0.XXe-NP](supporting/Lemma-0.0.XXe-Nucleation-Probability-Proof.md) |
| 6d | -1 | Prop 0.0.XXf | Computational Classification of Stella Dynamics | [foundations/Proposition-0.0.XXf](foundations/Proposition-0.0.XXf-Computational-Classification-Stella-Dynamics.md) · [Lean 4](../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XXf.lean) |
| 6e | -1 | Prop 0.0.XXg | Q₃ Spectral Structure on the Stella Octangula | [foundations/Proposition-0.0.XXg](foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md) · [Derivation](foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Derivation.md) · [Applications](foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Applications.md) |
| 7 | -1 | Prop 0.0.28 | Theory Space Fixed Point | [foundations/Proposition-0.0.28](foundations/Proposition-0.0.28-Theory-Space-Fixed-Point.md) |
| 8 | -1 | Thm 0.0.29 | Lawvere Bootstrap Uniqueness | [foundations/Theorem-0.0.29](foundations/Theorem-0.0.29-Lawvere-Bootstrap-Uniqueness.md) |
| 9 | -1 | Thm 0.0.31 | Unconditional Uniqueness CG Fixed Point | [foundations/Theorem-0.0.31](foundations/Theorem-0.0.31-Unconditional-Uniqueness-CG-Fixed-Point.md) |
| 10 | -1 | Thm 0.0.33 | Information Geometry Duality | [foundations/Theorem-0.0.33](foundations/Theorem-0.0.33-Information-Geometry-Duality.md) |
| 11 | -1 | Prop 0.0.17y | Bootstrap Fixed Point Uniqueness | [foundations/Proposition-0.0.17y](foundations/Proposition-0.0.17y-Bootstrap-Fixed-Point-Uniqueness.md) |
| 12 | -1 | Prop 0.0.17z | Non-Perturbative Corrections To Bootstrap | [foundations/Proposition-0.0.17z](foundations/Proposition-0.0.17z-Non-Perturbative-Corrections-To-Bootstrap.md) |
| 13 | -1 | Thm 0.0.41 | Dimensional Incompleteness | [foundations/Theorem-0.0.41](foundations/Theorem-0.0.41-Dimensional-Incompleteness.md) |
| 14 | -1 | Prop 0.0.41a | CG Dimensional Optimality | [foundations/Proposition-0.0.41a](foundations/Proposition-0.0.41a-CG-Dimensional-Optimality.md) |

### Internal dependency chain
```
Thm 0.0.18 (Signature eqs) → Thm 0.0.19 (Self-reference uniqueness)
                                    ↓
                              Prop 0.0.28 (Theory space fixed point)
                                    ↓
                    ┌───────────────┼───────────────┐
                    ↓               ↓               ↓
              Thm 0.0.29      Thm 0.0.31      Thm 0.0.XXc
           (Lawvere)       (Unconditional)   (Gödel separation)
                    ↓                               ↓
              Prop 0.0.17y-z              Prop 0.0.XXd
           (Bootstrap self-consistency)  (Computational universality)
                    ↓                    ↑           ↓
              Thm 0.0.41 (Dimensional Incompleteness)
                    ↓
              Prop 0.0.41a (CG Dimensional Optimality)

                                    Prop 0.0.XXb   Prop 0.0.XXe
                                   (Computability) (Continuum limit)
                                                     ↑       ↓
                                              Lem 0.0.XXe-BC (κ=1/2)
                                              Lem 0.0.XXe-NP (nucleation)
                                                             ↓
                                                      Prop 0.0.XXf
                                                 (Computational classification)
                                                             ↓
                                                      Prop 0.0.XXg
                                                 (Spectral prime encoding)
```

### Cross-group imports
- **← G1:** Stella geometry as the unique arena
- **← G6:** QCD parameters for bootstrap numerical check
- **← G8:** Gravitational parameters for self-consistency loop
- **← G10:** Mathematical rigor (mass gap existence) needed for fixed-point claims

### Cross-group exports
- **→ All groups:** If uniqueness holds, all other groups are necessary consequences (not arbitrary choices)

### Coherence checklist
- [ ] Fixed-point uniqueness (Prop 0.0.28, Thm 0.0.31) does not assume what it derives
- [ ] Gödel separation (Thm 0.0.XXc) honestly addresses limits of self-reference
- [ ] Bootstrap-predicted R_stella = 0.454 fm is correctly distinguished from observed 0.44847 fm
- [ ] Lawvere categorical framework (Thm 0.0.29) is compatible with information-geometric framework (Thm 0.0.33)
- [ ] Non-perturbative corrections (Prop 0.0.17z) do not introduce new free parameters

---

## G12: Predictions & Falsifiability

**Core question:** What observable consequences does the framework predict that distinguish it from the Standard Model?

**Master reference:** [Predictions-Master-Reference.md](reference/Predictions-Master-Reference.md) — Unified index of all 25 testable predictions (4 tiers, experimental timeline, falsification criteria, unique CG signatures)

**Unification points touched:** All (predictions test every aspect)

### Proofs (dependency order)

**Subgroup G12a: Scattering & Feynman rules**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 1 | 6 | Thm 6.1.1 | Complete Feynman Rules | [Phase6/Theorem-6.1.1](Phase6/Theorem-6.1.1-Complete-Feynman-Rules.md) |
| 2 | 6 | Thm 6.2.1 | Tree-Level Scattering Amplitudes | [Phase6/Theorem-6.2.1](Phase6/Theorem-6.2.1-Tree-Level-Scattering-Amplitudes.md) |
| 3 | 6 | Thm 6.2.2 | Helicity Amplitudes | [Phase6/Theorem-6.2.2](Phase6/Theorem-6.2.2-Helicity-Amplitudes-Spinor-Helicity-Formalism.md) |
| 4 | 6 | Prop 6.3.1 | One-Loop QCD Corrections | [Phase6/Proposition-6.3.1](Phase6/Proposition-6.3.1-One-Loop-QCD-Corrections.md) |
| 5 | 6 | Prop 6.3.2 | Decay Widths | [Phase6/Proposition-6.3.2](Phase6/Proposition-6.3.2-Decay-Widths.md) |
| 6 | 6 | Prop 6.3.3 | Higgs Diphoton Decay | [Phase6/Proposition-6.3.3](Phase6/Proposition-6.3.3-Higgs-Diphoton-Decay.md) |
| 7 | 6 | Prop 6.3.4 | Higgs Z-Gamma Decay | [Phase6/Proposition-6.3.4](Phase6/Proposition-6.3.4-Higgs-Z-Gamma-Decay.md) |
| 8 | 6 | Prop 6.4.1 | Hadronization Framework | [Phase6/Proposition-6.4.1](Phase6/Proposition-6.4.1-Hadronization-Framework.md) |
| 9 | 6 | Prop 6.5.1 | LHC Cross-Section Predictions | [Phase6/Proposition-6.5.1](Phase6/Proposition-6.5.1-LHC-Cross-Section-Predictions.md) |

**Subgroup G12b: Fermion masses & mixing**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 10 | -1 | Prop 0.0.17n | P4 Fermion Mass Comparison | [foundations/Proposition-0.0.17n](foundations/Proposition-0.0.17n-P4-Fermion-Mass-Comparison.md) |
| 11 | 3 | Ext 3.1.2b | Complete Wolfenstein Parameters | [Phase3/Extension-3.1.2b](Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md) |
| 12 | 3 | Ext 3.1.2d | Complete PMNS Parameters | [Phase3/Extension-3.1.2d](Phase3/Extension-3.1.2d-Complete-PMNS-Parameters.md) |
| 13 | 8 | Drv 8.4.2 | θ₁₃ First Principles | [Phase8/Derivation-8.4.2](Phase8/Derivation-8.4.2-Theta13-First-Principles.md) |
| 14 | 8 | Drv 8.4.3 | Euler Characteristic Signature | [Phase8/Derivation-8.4.3](Phase8/Derivation-8.4.3-Euler-Characteristic-Signature.md) |
| 15 | 8 | Prop 8.4.4 | Atmospheric Angle Correction | [Phase8/Proposition-8.4.4](Phase8/Proposition-8.4.4-Atmospheric-Angle-Correction.md) |
| 16 | 8 | Drv 8.1.3 | Three-Generation Necessity | [Phase8/Derivation-8.1.3](Phase8/Derivation-8.1.3-Three-Generation-Necessity.md) |
| 17 | 8 | Prf 8.1.3b | Topological Generation Count | [Phase8/Proof-8.1.3b](Phase8/Proof-8.1.3b-Topological-Generation-Count.md) |

**Subgroup G12c: Cosmological & exotic predictions**

| # | Phase | Number | Title | File |
|---|-------|--------|-------|------|
| 18 | -1 | Prop 0.0.17u | Cosmological Initial Conditions | [foundations/Proposition-0.0.17u](foundations/Proposition-0.0.17u-Cosmological-Initial-Conditions-From-Pre-Geometry.md) |
| 19 | 8 | Pred 8.2.1 | QGP Phase Coherence | [Phase8/Prediction-8.2.1](Phase8/Prediction-8.2.1-QGP-Phase-Coherence.md) (+ Derivation, Applications) |
| 20 | 8 | Pred 8.2.3 | Pre-Geometric Relics | [Phase8/Prediction-8.2.3](Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md) (3-file) |
| 21 | 4 | Def 4.3.1 | W-Sector Field Theory | [Phase4/Definition-4.3.1](Phase4/Definition-4.3.1-W-Sector-Field-Theory.md) |
| 22 | 4 | Thm 4.3.2 | W-Soliton Existence and Properties | [Phase4/Theorem-4.3.2](Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md) |
| 23 | 4 | Prop 4.3.3 | W-Soliton Cosmological Abundance | [Phase4/Proposition-4.3.3](Phase4/Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md) |
| 24 | 4 | Prop 4.3.4 | W-Soliton Structure Formation | [Phase4/Proposition-4.3.4](Phase4/Proposition-4.3.4-W-Soliton-Structure-Formation.md) |
| 25 | 8 | Pred 8.2.4 | W-Sector Gravitational Waves | [Phase8/Prediction-8.2.4](Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md) |
| 26 | 8 | Pred 8.3.1 | W-Condensate Dark Matter | [Phase8/Prediction-8.3.1](Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md) |
| 27 | 8 | Pred 8.4.1 | Proton Decay From Geometric GUT | [Phase8/Prediction-8.4.1](Phase8/Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md) |
| 28 | 8 | Prop 8.5.1 | Lattice QCD Heavy-Ion Predictions | [Phase8/Proposition-8.5.1](Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md) (3-file) |
| 29 | 7 | Prop 7.8.1 | Exceptional Group Glueball Predictions | [Phase7/Proposition-7.8.1](Phase7/Proposition-7.8.1-Exceptional-Group-Glueball-Predictions.md) (3-file) |
| 30 | 7 | Prop 7.8.2 | Framework-Internal Glueball Mass Ratio | [Phase7/Proposition-7.8.2](Phase7/Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio.md) (3-file) |
| 31 | 7 | Prop 7.8.3 | Bethe-Salpeter Glueball Mass Ratio | [Phase7/Proposition-7.8.3](Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md) (3-file) |
| 32 | -1 | Thm 0.0.14 | Novel Lorentz Violation Pattern | [foundations/Theorem-0.0.14](foundations/Theorem-0.0.14-Novel-Lorentz-Violation-Pattern.md) |

### Cross-group imports
- **← G5:** Fermion masses, CKM/PMNS parameters
- **← G6:** All QCD scale parameters
- **← G8:** G_N, cosmological constant, Lorentz violation bounds
- **← G9:** Higgs mass, EW parameters, high-energy deviations
- **← G10:** Mass gap, glueball spectrum

### Cross-group exports
- **→ None** (G12 is the terminal group — predictions flow out to experiment)

### Coherence checklist
- [ ] All numerical predictions use R_stella = 0.44847 fm (observed), not bootstrap value
- [ ] Fermion masses (Prop 0.0.17n) and mixing angles (Ext 3.1.2b-d) use consistent input parameters
- [ ] QGP predictions (Pred 8.2.1, Prop 8.5.1) use same thermodynamic framework as G3
- [ ] Lorentz violation pattern (Thm 0.0.14) is below current experimental bounds (Thm 0.0.7)
- [ ] Scattering amplitudes (Thm 6.2.1-2) reproduce SM results at low energy (Thm 3.2.1 equivalence)
- [ ] Three-generation necessity (Drv 8.1.3) is consistent with mass hierarchy (Thm 3.1.2 in G5)
- [ ] W-sector field theory (Def 4.3.1) uses same stella geometry and pressure functions as Phase 0 definitions
- [ ] W-soliton mass (Thm 4.3.2, $M_W = 1620$ GeV) is consistent with relic abundance (Prop 4.3.3, $\Omega_W h^2 \approx 0.12$)
- [ ] W-soliton structure formation (Prop 4.3.4) is compatible with CDM constraints (Bullet Cluster, BAO, Lyman-$\alpha$)
- [ ] W-sector GW signal (Pred 8.2.4, mHz) is distinct from pre-geometric relics (Pred 8.2.3, nHz) — different mechanism, different frequency
- [ ] Dark matter candidate (Pred 8.3.1, Def 4.3.1) does not contradict direct detection bounds
- [ ] Proton decay lifetime (Pred 8.4.1) uses authoritative α_GUT = 1/24.4 from Prop 0.0.25 (not Prop 2.4.2 §8.3 value)
- [ ] Glueball predictions (Prop 7.8.1, 7.8.2, 7.8.3, 7.8.4, 7.8.6, 7.8.7) are testable on lattice
- [ ] Framework-internal $R_\text{cont}$ (Prop 7.8.2), Bethe-Salpeter estimate (Prop 7.8.3), V-scheme refinement (Prop 7.8.4), full two-gluon spectrum (Prop 7.8.6), and three-gluon spectrum (Prop 7.8.7) are mutually consistent and agree with lattice data

---

## Appendix A: Proofs That Appear in Multiple Groups

Some proofs naturally belong to more than one thematic group. These are critical intersection points where fragmentation is most likely.

| Proof | Primary Group | Also in | Risk |
|-------|--------------|---------|------|
| Thm 1.1.1 (SU(3)↔Stella) | G1 | G2 | Low — foundational identity |
| Thm 2.5.1 (CG Lagrangian) | G2 | G5 | **High** — Lagrangian must encode all sectors consistently |
| Thm 3.2.1 (Low-E Equivalence) | G5 | G9, G12 | **High** — SM equivalence claim must hold everywhere |
| Prop 0.0.17n (Fermion Masses) | G6 | G12 | Medium — parameter values flow to predictions |
| Thm 5.2.0 (Wick Rotation) | G3 | G8, G10 | **High** — used in metric emergence AND lattice proofs |
| Props 0.0.17y-z (Bootstrap) | G6 | G11 | **High** — self-consistency constraint |
| Prop 0.0.27 (Higgs Mass) | G9 | G12 | Medium — prediction depends on derivation correctness |
| Def 4.3.1 (W-Sector Field Theory) | G5 | G12 | **High** — W condensate VEV and portal coupling must be consistent across DM predictions |
| Prop 4.3.3 (W-Soliton Abundance) | G4 | G12 | Medium — ADM mechanism uses same chirality bias as baryogenesis |
| Thm 7.3.2 (Asymptotic Freedom) | G2 | G10 | **High** — gauge + renormalization must agree |

---

## Appendix B: Unification Points ↔ Groups Mapping

| Unification Point | Primary Groups | What to Check |
|-------------------|---------------|---------------|
| UP1: Time & Evolution | G3 | λ vs t vs τ_E consistent everywhere |
| UP2: Energy & Stress-Energy | G3, G6, G8 | E[χ] → T_μν → ρ_vac reduction chain |
| UP3: Chirality Selection | G4, G9 | Same mechanism at QCD and EW scales |
| UP4: Instanton Physics | G2, G4, G5 | Same density profile, same coefficient |
| UP5: Mass Generation | G5, G9 | Phase-gradient ↔ Higgs proven equivalent |
| UP6: Metric/Gravity Emergence | G8 | Stress-energy, thermodynamic, Goldstone — one mechanism |
| UP7: Vacuum Energy Cancellation | G8, G9 | Phase cancellation at ALL scales |

---

## Appendix C: Suggested Review Order

For a complete coherence audit, review groups in this order (respecting dependencies):

1. **G1** (Geometric Foundation) — the base everything rests on
2. **G7** (Quantum Foundations) — establishes interpretive framework
3. **G3** (Time & Entropy) — the pre-geometric dynamics
4. **G6** (QCD Scale Derivation) — the parameter pipeline
5. **G2** (Gauge Theory & Confinement) — the SU(3) dynamics
6. **G4** (Chirality & CP Violation) — discrete symmetry structure
7. **G5** (Mass Generation) — the central physical mechanism
8. **G9** (Electroweak Sector) — extending beyond QCD
9. **G8** (Emergent Gravity) — the big unification claim
10. **G10** (Renormalization & Yang-Mills) — mathematical rigor check
11. **G11** (Bootstrap & Uniqueness) — the self-consistency argument
12. **G12** (Predictions & Falsifiability) — the experimental interface

---

*This document is maintained alongside PROOF-INDEX.md. When new proofs are added, assign them to the appropriate group(s) here.*

---

## Appendix D: Publication Paper Boundaries

Each paper maps to one or more thematic groups and has a clear, self-contained narrative arc. Papers are ordered so each depends only on preceding papers (or established physics).

### Paper Series Overview

| Paper | Title (working) | G-Groups | Core Narrative | Target Length |
|-------|----------------|----------|----------------|---------------|
| **Paper 1** | Geometric Foundations of SU(3) | G1 | From 3 axioms + established physics → SU(3) gauge theory on FCC lattice | 25–30 pp |
| **Paper 2** | Gauge Dynamics and Confinement | G2, G6 | SU(3) structure → confinement, asymptotic freedom, QCD scale derivation | 25–30 pp |
| **Paper 3** | Quantum Structure and Mass Generation | G7, G3, G5 | Quantum foundations → time emergence → phase-gradient mass generation → Lagrangian | 25–30 pp |
| **Paper 4** | Standard Model Structure from Geometry | G4, G9 | Chirality selection → electroweak sector → CP violation → strong CP resolution | 20–25 pp |
| **Paper 5** | Emergent Gravity and Cosmology | G8 | Einstein equations from pre-geometric fixed-point structure → cosmological predictions | 20–25 pp |
| **Paper 6** | Predictions, Verification, and Falsifiability | G12, G10, G11 | Scattering, fermion masses, mixing, dark matter, glueballs, Lean proofs, bootstrap | 25–30 pp |

### Paper Dependency Graph

```
Paper 1 (Geometric Foundations)
  │
  ├──→ Paper 2 (Gauge Dynamics & QCD Scale)
  │      │
  │      ├──→ Paper 3 (Quantum Structure & Mass)
  │      │      │
  │      │      └──→ Paper 4 (Standard Model Structure)
  │      │             │
  │      │             └──→ Paper 5 (Emergent Gravity)
  │      │                    │
  │      └────────────────────┴──→ Paper 6 (Predictions & Verification)
  │
  └──→ Paper 6 also imports directly from Papers 1–5
```

### Paper 1: Geometric Foundations of SU(3)

**Groups:** G1
**Audit status:** COMPLETE — Coherence (87/87), Validity (60/60), Adversarial (34S/6D/0C/0B = 90%)
**Paper status:** DRAFT COMPLETE — `papers/paper-1-foundations/main.tex` (16 pages two-column REVTeX, 22 references, 6 PDF figures + 3 TikZ diagrams)

**Content (as extracted into standalone paper):**
1. Sec I: Introduction — 5 falsification conditions (lead), 8-input table (3 irreducible), derivation chain, roadmap
2. Sec II: Definitions and Framework — GR1–GR3, pre-geometric substrate, SU(3) weight system
3. Sec III: D = 4 from observer existence (Thm 0.0.1)
4. Sec IV: Three paths to SU(3) — A (topological), B (info-theoretic), C (categorical), D (convergence)
5. Sec V: Stella octangula uniqueness (Thm 0.0.3) + metric from Killing form (Thm 0.0.2)
6. Sec VI: FCC lattice as unique spatial extension (Thm 0.0.6)
7. Sec VII: Continuum limit recovering SU(3) gauge theory (Prop 0.0.6b) + Lorentz violation bounds
8. Sec VIII: SM gauge group from polytope embedding chain (structural/kinematic only; dynamics deferred to Paper 2)
9. Sec IX: Discussion — summary, honest boundaries, comparison with LQG/CDT/strings/NCG, preemptive objections, falsification revisited
10. App A: Lean 4 excerpts, App B: Multi-agent audit summary (187 checks), App C: Notation

**Source:** Extracted from unified `papers/paper-chiral-geometrogenesis/CHIRAL_GEOMETROGENESIS.tex` Secs 2–8, with Sec 6 split (kinematic → Paper 1, dynamical → Paper 2)
**Supplementary:** Three audit reports (187 checks, 0 unresolved) + Lean 4 formalizations + figure generation scripts in `figures/scripts/`

### Paper 2: Gauge Dynamics and Confinement

**Groups:** G2, G6
**Audit status:** NOT STARTED

**Content:**
1. SU(3) ↔ Stella isomorphism (bridge from Paper 1)
2. Confinement geometry and Wilson loop area law
3. CG Lagrangian derivation
4. Dynamical confinement mechanism
5. Asymptotic freedom and beta function structure
6. QCD scale derivation chain: R_stella → √σ → f_π → Λ
7. Strong coupling from gauge unification

**Current `main.tex` sections:** Parts of Secs 5 (SM Gauge Structure), 27 (QCD Scale)

### Paper 3: Quantum Structure and Mass Generation

**Groups:** G7, G3, G5
**Audit status:** NOT STARTED

**Content:**
1. Fisher metric and Chentsov uniqueness → field existence
2. Information-geometric unification of space and time
3. Born rule from ergodic flow
4. Internal time emergence and entropy production
5. Phase-gradient mass generation mechanism
6. Complete CG Lagrangian and mass hierarchy
7. Wolfenstein parameter and generation structure

**Current `main.tex` sections:** Secs 9–12 (Interpretational Principles through Complete Lagrangian)

### Paper 4: Standard Model Structure from Geometry

**Groups:** G4, G9
**Audit status:** NOT STARTED

**Content:**
1. Topological chirality: why the weak force is left-handed
2. 24-cell geometry and D₄ root system → SU(2)×U(1)
3. Electroweak symmetry breaking from geometry
4. Strong CP problem: Z₃ resolution
5. Baryogenesis via chiral bias
6. W-condensate dark matter mechanism

**Current `main.tex` sections:** Secs 13–16, 22–26 (Strong CP through Dark Matter, EW Sector)

### Paper 5: Emergent Gravity and Cosmology

**Groups:** G8
**Audit status:** NOT STARTED

**Content:**
1. Einstein's equations from fixed-point structure
2. Spin-2 uniqueness from framework principles
3. Newton's gravitational constant from topology
4. Planck mass from QCD scale
5. Bekenstein-Hawking entropy from framework
6. Einstein-Cartan torsion extension
7. Cosmological predictions (spectral index, tensor-to-scalar)

**Current `main.tex` sections:** Secs 17–19 (Einstein Equations through Mass Scales)

### Paper 6: Predictions, Verification, and Falsifiability

**Groups:** G12, G10, G11
**Audit status:** NOT STARTED

**Content:**
1. Feynman rules and scattering amplitudes from geometry
2. Fermion mass predictions and comparison with PDG
3. CKM/PMNS mixing matrix predictions
4. Glueball spectrum predictions
5. QGP phase coherence (near-term testable)
6. Renormalization group consistency and mass gap
7. Bootstrap uniqueness and self-consistency
8. Machine-verified proofs (Lean 4)
9. Complete falsification conditions

**Current `main.tex` sections:** Secs 20–21, 27–34 (Scattering through Verification)

### Mapping: Current `main.tex` → Paper Series

| Current Section | Paper | Notes |
|----------------|-------|-------|
| Sec 1 (Introduction) | Each paper gets its own introduction | |
| Sec 2 (Definitions) | Paper 1 | |
| Sec 3 (Observer-Compatible D) | Paper 1 | |
| Sec 4 (Euclidean Metric) | Paper 1 | |
| Sec 5 (Stella Uniqueness) | Paper 1 | |
| Sec 6 (SM Gauge Structure) | Papers 1 + 2 | Split: SU(3) paths → P1, gauge dynamics → P2 |
| Sec 7 (Spatial Extension) | Paper 1 | |
| Sec 8 (Continuum Limit) | Paper 1 | |
| Sec 9 (Interpretational Principles) | Paper 3 | |
| Sec 10 (Quantum Structure) | Paper 3 | |
| Sec 11 (Mass Generation) | Paper 3 | |
| Sec 12 (Complete Lagrangian) | Paper 3 | |
| Sec 13 (Strong CP) | Paper 4 | |
| Sec 14 (Time's Arrow) | Paper 3 | |
| Sec 15 (Baryogenesis) | Paper 4 | |
| Sec 16 (W-Condensate DM) | Paper 4 | |
| Sec 17 (Chirality) | Paper 4 | |
| Sec 18 (Einstein's Equations) | Paper 5 | |
| Sec 19 (Mass Scales) | Paper 5 | |
| Secs 20–21 (Feynman Rules, Amplitudes) | Paper 6 | |
| Secs 22–26 (EW Sector) | Paper 4 | |
| Secs 27–30 (QCD Scale, Masses, Mixing, Cosmology) | Papers 2 + 6 | QCD scale → P2, predictions → P6 |
| Secs 31–34 (Lean, Consistency, Signatures) | Paper 6 | |

---

## Appendix E: Three-Layer Audit Protocol

The G1 audit established a three-layer verification process. All subsequent G-groups should follow the same protocol, adapted per [Adversarial Stress-Test Audit, Appendix D](reviews/G1/G1-Adversarial-Stress-Test-Audit.md#appendix-d-reusability-guide-for-g2g12).

### The Three Layers

| Layer | Name | Core Question | Posture | Output | G1 Result |
|-------|------|--------------|---------|--------|-----------|
| **Layer 1** | Coherence Audit | Do the files agree with each other? | Defensive | PASS / FAIL per check | 87/87 PASS |
| **Layer 2** | Validity Audit | Are the files *correct*? | Defensive | SOUND / QUALIFIED / WEAK / INVALID | 60/60 (26S, 32Q, 0W, 0I) |
| **Layer 3** | Adversarial Stress-Test | Can the files be *broken*? | Offensive | SURVIVED / DENTED / CRACKED / BROKEN | 40/40 (34S, 6D, 0C, 0B) |

### Layer 1: Coherence Audit

**Purpose:** Verify internal consistency across all proofs within the group.

**10 Standard Modules:**

| Module | Focus | What It Checks |
|--------|-------|---------------|
| M1 | Geometric/Structural Identity | Core objects have consistent properties across all files |
| M2 | Primary Derivation Paths | Multiple paths to key results agree |
| M3 | External vs Internal Consistency | External inputs match internal re-derivations |
| M4 | Key Correspondence Structures | Claimed isomorphisms/mappings are consistent |
| M5 | Spatial/Extension Structures | Extended objects (lattices, manifolds) are consistent |
| M6 | Phase 0 / Foundational Objects | Base-layer definitions are consistent with their use |
| M7 | Notation and Convention Consistency | Symbols, markers, and conventions are uniform |
| M8 | Dependency Chain Verification | Theorem DAG is acyclic; all prereqs satisfied |
| M9 | Claims vs Evidence | Status markers match actual proof content |
| M10 | Numerical Values | All shared numerical values are consistent across files |

**Adapt per group:** Replace M1's "stella geometry" with the group's core objects. Replace M4's "vertex-weight correspondence" with the group's key mappings. M7–M10 are universal.

**Threshold:** All checks must PASS (with NOTES acceptable). Any FAIL must be resolved before proceeding.

**Template:** [G1-Geometric-Foundation-Coherence-Audit.md](reviews/G1/G1-Geometric-Foundation-Coherence-Audit.md)

### Layer 2: Validity Audit

**Purpose:** Verify external correctness — are the proofs *true*, not merely consistent?

**8 Standard Modules:**

| Module | Focus | What It Catches |
|--------|-------|----------------|
| V1 | Assumption Inventory | Undeclared assumptions; classify each as (E)stablished, (F)ramework, (H)ypothesis |
| V2 | Derivation Step Verification | Each load-bearing step checked against cited theorem's actual hypotheses |
| V3 | Semantic Circularity Detection | Different proofs assuming the same thing under different names |
| V4 | Alternative Explanations | Loopholes in uniqueness/necessity claims |
| V5 | Domain-of-Validity Verification | Established results applied within their proven domain |
| V6 | Selection vs Derivation Honesty | True logical character matches presentation (derivation vs selection vs consistency check) |
| V7 | Falsifiability & Empirical Contact | Which claims are predictions vs retrodictions; can it be falsified? |
| V8 | Known Counterarguments & Literature | Published criticisms and alternative approaches addressed |

**Execution order:** V1 + V3 first (reveals true structure) → V2 + V5 (catches math errors) → V6 (catches framing errors) → V4 (stress-tests uniqueness) → V7 + V8 (external perspective).

**Severity scale:** CRITICAL > MAJOR > MODERATE > MINOR > NOTE

**Threshold:** No INVALID findings. All SMUGGLED assumptions must be declared. All WEAK findings must be addressed (strengthen or restrict scope). QUALIFIED findings are acceptable if conditions are stated.

**Template:** [G1-Geometric-Foundation-Validity-Audit.md](reviews/G1/G1-Geometric-Foundation-Validity-Audit.md)
**Findings template:** [G1-Validity-Audit-Final-Synthesis.md](reviews/G1/G1-Validity-Audit-Final-Synthesis.md)

### Layer 3: Adversarial Stress-Test

**Purpose:** Actively attack the framework's conclusions — build counterexamples, construct alternative frameworks, remove assumptions, stress boundaries.

**6 Standard Modules:**

| Module | Attack Type | Severity Class | What It Proves If Survived |
|--------|------------|---------------|---------------------------|
| A1 | Counterexample Construction | EXISTENTIAL | Alternatives don't exist |
| A2 | Alternative Framework Construction | EXISTENTIAL | Framework is necessary, not just sufficient |
| A3 | Independent Rederivation | STRUCTURAL | No hidden assumptions in proofs |
| A4 | Assumption Removal Cascade | STRUCTURAL | Fragility map; identifies redundant inputs |
| A5 | Boundary Stress-Testing | STRUCTURAL | Conclusions are topologically robust, not fine-tuned |
| A6 | Numerical Stress-Test | COSMETIC | Numbers are derivable identities, not coincidences |

**Execution order (3 phases):**
1. **Phase 1 — Structural:** A4 (removal cascade) + A2 (alternative frameworks) — reveals load-bearing inputs
2. **Phase 2 — Physics:** A1 (counterexamples) + A3 (rederivation) — the hardest tests
3. **Phase 3 — Fragility:** A5 (boundary stress) + A6 (numerical) — quantitative precision

**Phase gates:**
- After Phase 1: If any A2 check is BROKEN → HALT (uniqueness compromised)
- After Phase 2: If any A1 check is BROKEN → HALT (counterexample exists)
- After Phase 3: Compute resilience score

**Resilience score:** Score = (SURVIVED × 3 + DENTED × 1) / (Total × 3) × 100%
- \>80% = Adversarially Robust
- 60–80% = Conditionally Robust
- <60% = Structurally Vulnerable

**Template:** [G1-Adversarial-Stress-Test-Audit.md](reviews/G1/G1-Adversarial-Stress-Test-Audit.md)
**Findings template:** [G1-Adversarial-Stress-Test-Findings.md](reviews/G1/G1-Adversarial-Stress-Test-Findings.md)

### Adapting for Each Group

What changes per group (from [Adversarial Audit, Appendix D](reviews/G1/G1-Adversarial-Stress-Test-Audit.md#appendix-d-reusability-guide-for-g2g12)):

| Component | What to Substitute |
|-----------|-------------------|
| Master file list | The group's proofs from its section above |
| Independent inputs | The group's axioms (may inherit from G1 + add new) |
| Load-bearing steps | The group's critical derivation steps (from its V2) |
| Uniqueness claims | The group's uniqueness/necessity claims |
| Numerical chains | The group's numerical predictions |
| Counterexamples | Group-specific alternatives |

What stays the same: module structure, result classifications, execution protocol, resilience map template, cascade mapping protocol.

### Group-Specific Adaptation Notes

| Group | Key Adaptation Focus |
|-------|---------------------|
| **G2** | A1: Build SU(2) gauge theory with same structure; A2: alternative gauge structures (non-minimal coupling) |
| **G3** | A1: alternative time emergence mechanisms; A5: time parameter sensitivity |
| **G4** | A1: alternative chirality selection; A2: different CP violation mechanisms |
| **G5** | A1: build Nambu-Jona-Lasinio comparison; A6: fermion mass numerical chains |
| **G6** | A6: dominant module — all QCD parameters independently recomputed; A5: 10% R_stella variation |
| **G7** | A1: alternative Born rule derivations; A4: which quantum principles are independent |
| **G8** | A1: alternative gravity emergence (thermodynamic vs geometric); A2: compare with Verlinde/Jacobson |
| **G9** | A1: alternative EW symmetry breaking; A6: Higgs mass, W/Z mass predictions |
| **G10** | A3: independent beta-function rederivation; A5: UV completion sensitivity |
| **G11** | A2: dominant module — alternative bootstrap constructions; A4: self-consistency loop fragility |
| **G12** | A6: dominant module — all numerical predictions stress-tested; A1: alternative explanations for each prediction |

### Audit Progress Tracker

| Group | Layer 1 (Coherence) | Layer 2 (Validity) | Layer 3 (Adversarial) | Paper | Status |
|-------|:---:|:---:|:---:|:---:|:---:|
| G1 | 143/178 (5 FAIL) | 297/319 (12 FAIL) | 40/40 (90%) ✅ | Paper 1 | **DRAFT COMPLETE** |
| G2 | — | — | — | Paper 2 | Not started |
| G3 | — | — | — | Paper 3 | Not started |
| G4 | — | — | — | Paper 4 | Not started |
| G5 | — | — | — | Paper 3 | Not started |
| G6 | — | — | — | Paper 2 | Not started |
| G7 | — | — | — | Paper 3 | Not started |
| G8 | — | — | — | Paper 5 | Not started |
| G9 | — | — | — | Paper 4 | Not started |
| G10 | — | — | — | Paper 6 | Not started |
| G11 | — | — | — | Paper 6 | Not started |
| G12 | — | — | — | Paper 6 | Not started |

### File Naming Convention for Audit Documents

```
reviews/
├── G1/
│   ├── G1-Geometric-Foundation-Coherence-Audit.md     ← Layer 1 plan
│   ├── G1-Geometric-Foundation-Validity-Audit.md      ← Layer 2 plan
│   ├── G1-Validity-Audit-Module-V[1-8]-Findings.md    ← Layer 2 per-module findings
│   ├── G1-Validity-Audit-Final-Synthesis.md           ← Layer 2 synthesis
│   ├── G1-Adversarial-Stress-Test-Audit.md            ← Layer 3 plan
│   └── G1-Adversarial-Stress-Test-Findings.md         ← Layer 3 findings
│
├── G2/
│   ├── G2-Gauge-Confinement-Coherence-Audit.md        ← (next)
│   ├── G2-Gauge-Confinement-Validity-Audit.md
│   └── G2-...
│
└── (pattern: G[N]/G[N]-[Short-Name]-[Layer]-[Type].md)
```

### Readiness Criteria

A thematic group is **ready for its paper** when:

1. **Layer 1 complete:** All coherence checks PASS (NOTES acceptable)
2. **Layer 2 complete:** No INVALID findings; all SMUGGLED assumptions declared; all WEAK findings addressed
3. **Layer 3 complete:** Resilience score > 80% (Adversarially Robust); no BROKEN findings
4. **All recommendations resolved:** Every finding from all three layers has been addressed in the proof files
5. **Lean 4 formalization:** Load-bearing theorems have machine-verified proofs (recommended, not blocking)
