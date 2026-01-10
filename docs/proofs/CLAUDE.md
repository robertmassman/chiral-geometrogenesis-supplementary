# CLAUDE.md - Chiral Geometrogenesis Project

## Project Overview

This project develops **Chiral Geometrogenesis (CG)**, a theoretical physics framework proposing that spacetime, mass, and matter emerge from chiral field dynamics on a pre-geometric structure (the stella octangula—a compound of two interpenetrating tetrahedra, also known as the star tetrahedron). The goal is to produce mathematically rigorous proofs that will withstand peer review by world-class physicists and mathematicians.

**Primary Objective:** Create publication-ready mathematical proofs connecting SU(3) geometry, chiral symmetry breaking, and emergent spacetime.

---

## Active Development Directives

### Core Mandate

**In order to achieve completeness, Claude should proactively research, formulate, and derive when and where needed.**

This means:

1. **Research:** When encountering a gap in the proof chain, actively search the literature for relevant established results. Use web search to find peer-reviewed papers, textbook derivations, and lattice QCD data that can support or constrain the theory.

2. **Formulate:** When concepts are described informally or imprecisely, take initiative to write rigorous mathematical definitions. Every physical claim should have a corresponding precise mathematical statement.

3. **Derive:** When a result is stated but not proven, work through the derivation step-by-step. Show all intermediate steps. If a derivation requires techniques not yet established in the project, develop them.

### Proactive Behavior Expected

| Situation | Passive Response (AVOID) | Active Response (PREFERRED) |
|-----------|-------------------------|----------------------------|
| Missing derivation | "This requires proof" | Work through the derivation, show all steps |
| Unclear definition | "This needs to be defined" | Write the precise mathematical definition |
| Gap in literature | "A reference is needed" | Search for and cite the relevant paper |
| Numerical value needed | "This should be calculated" | Perform the calculation, verify against data |
| Consistency check failed | "There may be an error" | Identify the error, propose correction |
| Circular dependency found | "This is circular" | Trace to root cause, propose resolution |

### Protocols

**Research:** (1) Check textbooks → (2) Search papers → (3) Lattice QCD/data → (4) Novel derivation (mark 🔶 NOVEL)

**Derivation:** State goal → List prerequisites → Choose method → Execute step-by-step → Verify → Document

**Formulation:** Identify intuition → Choose structure → Write definition → State domain/range → Verify well-definedness

### Completeness Checklist

Before considering any theorem "complete," verify:
- [ ] All terms precisely defined
- [ ] All prerequisites proven or marked established
- [ ] No gaps ("it can be shown that...")
- [ ] Numerical values calculated/referenced
- [ ] Consistency checks performed
- [ ] Physical interpretation clear
- [ ] Connection to other theorems documented

### Initiative Boundaries

**Claude SHOULD:** Fill gaps, search literature, calculate values, propose corrections, suggest alternatives

**Claude should STOP and consult when:** Fundamental assumption needs revision, multiple valid approaches exist, contradicts established physics unexpectedly, scope would significantly expand

---

## Independent Verification Protocol (MANDATORY)

### Rationale

A single agent writing and verifying its own proofs is like a researcher peer-reviewing their own paper — systematic blind spots persist. **All significant derivations, proofs, and calculations MUST be independently verified by a separate agent instance.**

### When Verification is REQUIRED

| Work Product | Verification Required? | Verification Depth |
|--------------|----------------------|-------------------|
| New theorem proof | ✅ YES | Full independent re-derivation |
| Numerical calculation | ✅ YES | Independent calculation + limit checks |
| Novel physical mechanism | ✅ YES | Adversarial review + literature check |
| Consistency claim | ✅ YES | Explicit verification of both sides |
| Status upgrade (🔮→🔶→✅) | ✅ YES | Full review before upgrade |

### Spawning a Verification Agent

When verification is needed, spawn an independent agent using this protocol:

```
VERIFICATION TASK:

You are an independent verification agent for the Chiral Geometrogenesis project.
Your role is ADVERSARIAL — your job is to find errors, gaps, and inconsistencies.

You are reviewing: [Theorem/Proof Name]

VERIFICATION CHECKLIST:
1. LOGICAL VALIDITY - Does each step follow? Hidden assumptions? Circular?
2. MATHEMATICAL CORRECTNESS - Re-derive key equations independently
3. DIMENSIONAL ANALYSIS - Consistent units throughout?
4. LIMITING CASES - Reduces to known physics appropriately?
5. CONSISTENCY WITH FRAMEWORK - Uses mechanisms consistently?
6. PHYSICAL REASONABLENESS - No pathologies?
7. LITERATURE VERIFICATION - Citations accurate?

OUTPUT FORMAT:
- VERIFIED: [Yes/No/Partial]
- ERRORS FOUND: [List with locations]
- WARNINGS: [Potential issues]
- SUGGESTIONS: [Improvements]
- CONFIDENCE: [High/Medium/Low] with justification
```

### Critical Theorems Requiring Multi-Agent Verification

- Theorem 0.2.2 (Internal Time Emergence) — breaks bootstrap
- Theorem 3.1.1 (Phase-Gradient Mass Generation Mass Formula) — core mechanism
- Theorem 4.2.1 (Chiral Bias in Soliton Formation) — baryogenesis
- Theorem 5.2.1 (Emergent Metric) — gravity emergence
- Theorem 5.1.2 (Vacuum Energy Density) — cosmological constant
- Theorem 3.2.1 (Low-Energy Equivalence) — SM recovery

**→ See:** [reference/Verification-Protocol-Details.md](reference/Verification-Protocol-Details.md) for detailed instructions, handling results, phase-specific requirements, and escalation protocol.

---

## The Fragmentation Problem

### The Fatal Flaw

A subtle but fatal flaw in theoretical frameworks occurs when:

1. **Theorem A** uses **Physics Explanation X** to justify Result A
2. **Theorem B** uses **Physics Explanation Y** (similar but different) to justify Result B
3. X and Y appear compatible individually, but have subtly incompatible assumptions
4. The full theory cannot cohere because X and Y cannot both be true simultaneously

**This is how promising theories silently fail peer review.**

### Mandatory Consistency Rule

**When a physical mechanism, concept, or explanation is used in one theorem, ALL subsequent theorems that invoke the same or similar mechanism MUST:**

1. Explicitly reference the original theorem where the mechanism was established
2. Use identical definitions, assumptions, and notation
3. Show that any apparent differences are either:
   - Notational (same physics, different symbols)
   - Scale-dependent manifestations of the same underlying mechanism
   - Rigorously derived limits/approximations of the original
4. If genuinely different mechanisms are needed, explicitly prove they are compatible

### Seven Critical Unification Points

The following physical concepts appear in multiple theorems and MUST be treated consistently throughout:

1. **TIME AND EVOLUTION** — Internal λ (Theorem 0.2.2), physical t = λ/ω, Euclidean τ
2. **ENERGY AND STRESS-ENERGY** — Pre-geometric E[χ] (Theorem 0.2.4), T_μν (Theorem 5.1.1), ρ_vac (Theorem 5.1.2)
3. **CHIRALITY SELECTION** — α = 2π/3 (SU(3)), sign from ⟨Q⟩ > 0 (Theorem 2.2.4), EW chirality (Theorem 2.3.1)
4. **INSTANTON PHYSICS** — Anomaly coefficient 1/(16π²), density gradient n_in << n_out, same profile everywhere
5. **MASS GENERATION** — Phase-gradient mass generation (Theorem 3.1.1) ↔ Higgs mechanism (Theorem 3.2.1)
6. **METRIC/GRAVITY EMERGENCE** — Stress-energy sourcing, thermodynamic, Goldstone exchange (same mechanism!)
7. **VACUUM ENERGY CANCELLATION** — Phase cancellation at ALL scales (QCD, EW, GUT, Planck)

**→ See:** [reference/Unification-Points-Details.md](reference/Unification-Points-Details.md) for detailed tables, required derivations, and fragmentation risks.

### Consistency Enforcement

**When writing a new theorem:** Identify mechanisms → Check if used before → Reference original OR become primary definition → Update unification table → Include consistency subsection

**When reviewing:** List concepts → Find where else used → Verify identical definitions/assumptions → Flag inconsistencies as CRITICAL ERROR

### Red Flags for Fragmentation

1. **Different words for same thing** — "internal time" vs "evolution parameter" vs "phase parameter"
2. **Same words for different things** — "mass" (pole, running, constituent, current?)
3. **Scale-dependent without derivation** — Must show Y → X under RG flow
4. **Multiple "explanations"** — Must be ONE explanation at different scales
5. **Numerical values from different sources** — Must give EXACTLY same value for same reason
6. **Limits don't match** — If A → X and B → Y in same limit, X and Y must be consistent

---

## Standards for Mathematical Rigor

### Proof Structure Requirements

Every proof document MUST contain:

1. **Theorem Statement** — Precise, unambiguous mathematical claim
2. **Definitions** — All symbols defined before use; no implicit assumptions
3. **Prerequisites** — List of prior theorems/lemmas (with status indicators)
4. **Proof Body** — Logical chain from hypotheses to conclusion
5. **Physical Interpretation** — Connection to observable physics
6. **Consistency Checks** — Dimensional analysis, limiting cases, known results recovery
7. **Open Questions** — Honest acknowledgment of gaps or assumptions

### Validity Criteria

A proof is valid ONLY if:
- [ ] Every step follows logically from previous steps
- [ ] All assumptions are explicitly stated
- [ ] No circular dependencies exist in the proof chain
- [ ] Dimensional analysis is consistent throughout
- [ ] Known physics is recovered in appropriate limits
- [ ] No hand-waving or "it can be shown that..." without reference

### Status Classification

| Symbol | Status | Meaning | Peer Review Ready? |
|--------|--------|---------|-------------------|
| ✅ ESTABLISHED | Proven | Standard physics/math, peer-reviewed literature | Yes |
| 🔶 NOVEL | Novel Claim | New physics, requires careful derivation | After verification |
| 🔸 PARTIAL | Partially Proven | Some aspects proven, others pending | No |
| 🔮 CONJECTURE | Proposed | Hypothesized, needs development | No |

---

## Critical Review Checklist

Before marking ANY theorem as complete, verify:

### Mathematical Rigor
- [ ] Existence proofs: Does the mathematical object actually exist?
- [ ] Uniqueness: If claimed unique, is uniqueness proven?
- [ ] Well-definedness: Are all operations well-defined on their domains?
- [ ] Convergence: Do all series/integrals converge?
- [ ] Boundary conditions: Are boundary terms properly handled?

### Physical Consistency
- [ ] Units: Do all equations have consistent dimensions?
- [ ] Limits: Non-relativistic (v << c), weak-field (G → 0), classical (ℏ → 0), Standard Model (low energies)?
- [ ] Symmetries: Are claimed symmetries actually preserved?
- [ ] Causality: Does the theory respect causality?
- [ ] Unitarity: Is probability conserved?

### Logical Structure
- [ ] No circular reasoning: Trace dependency chain to axioms
- [ ] No unstated assumptions: Every premise is explicit
- [ ] No gaps: Every logical step is justified
- [ ] Falsifiability: Does this make testable predictions?

---

## Common Pitfalls to Avoid

### 1. Circularity Detection
Red flag pattern: A requires B, B requires C, C requires A ← CIRCULAR!

Resolution: Identify fundamental axiom → Use pre-geometric definitions (Phase 0) → Distinguish ASSUMED vs DERIVED

### 2. Notation Ambiguity
**Bad:** "Let χ be the chiral field"
**Good:** "Let χ: M → ℂ be a smooth complex scalar field on spacetime M with χ(x) = ρ(x)e^{iθ(x)} where ρ: M → ℝ≥0 and θ: M → [0, 2π)"

### 3. Implicit Assumptions
Make explicit: Spacetime signature (−+++), metric conventions, normalization (Tr[TᵃTᵇ] = ½δᵃᵇ), covariant derivative definition, mass type (pole/running/constituent/current)

### 4. Order-of-Magnitude Errors
Always verify: Numerical prefactors (2π, 4π), powers of coupling constants, loop factors

---

## Notation Conventions (MANDATORY)

### Indices
- Greek (μ, ν, ρ, σ): spacetime 0,1,2,3
- Latin (i, j, k): spatial 1,2,3
- Capital (A, B, C): color fundamental rep
- Lowercase (a, b, c): color adjoint rep

### Metric and Signature
- Mostly-plus: η_μν = diag(−1, +1, +1, +1)
- Covariant derivative: ∇_μ V^ν = ∂_μ V^ν + Γ^ν_μρ V^ρ

### Gamma Matrices
- Clifford algebra: {γ^μ, γ^ν} = 2η^{μν}
- Chiral matrix: γ₅ = iγ⁰γ¹γ²γ³
- Projectors: P_L = (1−γ₅)/2, P_R = (1+γ₅)/2

### Field Theory
- Natural units: ℏ = c = 1 (restore for final numerical results)
- Fourier: φ(x) = ∫ d⁴k/(2π)⁴ φ̃(k) e^{−ikx}

### Project-Specific
- χ: Chiral scalar field (Right-Handed Boundary Condensate)
- v_χ: Chiral VEV magnitude
- f_π: Chiral decay constant (~93 MeV)
- Λ: UV cutoff scale
- α = 2π/3: Chiral phase angle from SU(3)
- ε: Regularization parameter (see Definition 0.1.1)

---

## Interaction Guidelines for Claude

### When Writing Proofs
1. Start with prerequisites (verify dependencies satisfied)
2. State assumptions explicitly (never leave implicit)
3. Show all steps (no "it follows that..." without justification)
4. Check consistency (dimensional analysis, limits, symmetries)
5. Flag uncertainty (use appropriate status markers)
6. Cite sources (reference established results properly)

### When Reviewing Proofs
1. Check logical chain (verify each step follows)
2. Hunt for circularity (trace dependency graph)
3. Test limits (reduces to known physics?)
4. Verify numbers (factors of 2π, coupling constants)
5. Question assumptions (all premises justified?)
6. Be honest (flag gaps even if uncomfortable)

### When Deriving New Results
1. Clarify scope (what exactly is being derived?)
2. Identify approach (which mathematical tools appropriate?)
3. Work incrementally (break into smaller, verifiable steps)
4. Test against known cases (verify with examples)
5. Acknowledge novelty (clearly mark what's new vs established)

### Red Lines (Never Do)
- ❌ Never claim something is "proven" when it's conjectured
- ❌ Never hide circular reasoning
- ❌ Never ignore dimensional inconsistencies
- ❌ Never fabricate references
- ❌ Never suppress counterarguments or known difficulties
- ❌ Never overstate confidence in novel claims

---

## Domain-Specific Guidance

**Phase 1 (SU(3) Geometry):** Verify against Georgi/Fulton & Harris, check weight diagrams, confirm Casimir invariants, use established structure constants f^{abc}

**Phases 2-3 (Chiral Dynamics):** Cross-check chiral perturbation theory (Gasser & Leutwyler), verify anomaly coefficients (ABJ), ensure lattice QCD consistency, check f_π appears correctly

**Phase 4 (Solitons):** Compare with Skyrme model, verify topological charge quantized, check Bogomolny bounds, confirm baryon phenomenology

**Phase 5 (Emergent Gravity):** Recover Newtonian gravity (weak-field), check GR tests (perihelion, light bending, Shapiro delay), verify T_μν symmetric and conserved, ensure Einstein equations emerge correctly

---

## Reference Files

**Detailed guides for in-depth reference:**

- **Mathematical Techniques:** [reference/Mathematical-Techniques-Reference.md](reference/Mathematical-Techniques-Reference.md) — 11 techniques (Lie algebra, SSB, chiral anomaly, Kuramoto, solitons, Atiyah-Singer, entropic gravity, Wick rotation, EFT matching, instantons, GUT)

- **Challenge Resolutions:** [reference/Challenge-Resolutions.md](reference/Challenge-Resolutions.md) — 8 major challenges and how CG resolves them (Bootstrap, Noether circularity, cosmic coherence, chirality selection, cosmological constant, renormalizability, unitarity, strong-field gravity)

- **Physical Constants & Data:** [reference/Physical-Constants-and-Data.md](reference/Physical-Constants-and-Data.md) — Physical constants, numerical verification targets, predictions, dependency graph

- **Proof Templates:** [reference/Proof-Templates.md](reference/Proof-Templates.md) — Documentation templates, file organization, QA protocol

- **Verification Details:** [reference/Verification-Protocol-Details.md](reference/Verification-Protocol-Details.md) — Verification agent instructions, handling results, phase-specific requirements, multi-agent verification, escalation

- **Unification Points Details:** [reference/Unification-Points-Details.md](reference/Unification-Points-Details.md) — Detailed tables for all 7 unification points, required derivations, fragmentation risks

---

## File Organization

```
docs/proofs/
├── foundations/          # Phase -1: Minimal axioms (0.0.x theorems)
│   ├── Definition-0.0.0-Minimal-Geometric-Realization.md
│   ├── Theorem-0.0.1-D4-From-Observer-Existence.md
│   ├── Theorem-0.0.2-Euclidean-From-SU3.md
│   ├── Theorem-0.0.3-Stella-Uniqueness.md
│   ├── Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md
│   ├── Theorem-0.0.5-Chirality-Selection-From-Geometry.md
│   ├── Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md
│   ├── Theorem-0.0.7-Lorentz-Violation-Bounds.md
│   ├── Theorem-0.0.8-Emergent-Rotational-Symmetry.md
│   └── verification/     # Foundation verification scripts
├── Phase0/               # Pre-geometric foundations (0.1.x - 0.3.x)
│   ├── Definition-0.1.1-Stella-Octangula-Boundary-Topology.md
│   ├── Definition-0.1.2-Three-Color-Fields-Relative-Phases.md
│   ├── Definition-0.1.3-Pressure-Functions.md
│   ├── Definition-0.1.4-Color-Field-Domains.md
│   ├── Theorem-0.2.1-Total-Field-Superposition.md
│   ├── Theorem-0.2.2-Internal-Time-Emergence.md
│   ├── Theorem-0.2.3-Stable-Convergence-Point.md
│   ├── Theorem-0.2.4-Pre-Geometric-Energy-Functional.md
│   └── Theorem-0.3.1-W-Direction-Correspondence.md
├── Phase1/               # SU(3) geometry and chiral field definitions
├── Phase2/               # Pressure-depression mechanism and phase dynamics
├── Phase3/               # Mass generation via phase-gradient mass generation
├── Phase4/               # Topological solitons and matter
├── Phase5/               # Emergent spacetime and gravity
├── Phase7/               # Renormalization, unitarity, consistency
├── Phase8/               # Predictions and experimental tests
├── reference/            # Reference documents
│   ├── Physical-Constants-and-Data.md
│   ├── Challenge-Resolutions.md
│   ├── Unification-Points-Details.md
│   └── Verification-Protocol-Details.md
├── supporting/           # Supporting calculations and derivations
├── verification-records/ # Verification logs and multi-agent summaries
│   ├── Multi-Agent-Verification-Results-*.md
│   ├── Theorem-*-Verification-Record.md
│   └── README.md
├── CLAUDE.md             # This file - proof writing guidance
└── README.md             # Proof directory overview

papers/                   # Publication-ready LaTeX papers
├── paper-1-foundations/  # Paper 1: Mathematical Foundations
├── paper-2-dynamics/     # Paper 2: Dynamics and Mass Generation
├── notation-glossary.md  # Unified notation reference
└── README.md

lean/ChiralGeometrogenesis/  # Lean 4 formalization
├── Foundations/          # Lean proofs of 0.0.x theorems
├── Phase0/ - Phase5/     # Lean proofs by phase
├── PureMath/             # Pure math (topology, Lie algebra, polyhedra)
└── CLAUDE.md             # Lean-specific guidance

verification/             # Computational verification (Python)
├── foundations/          # Phase -1/0.0.x verification
├── Phase0/ - Phase8/     # Verification scripts by phase
├── shared/               # Shared utilities and reports
└── plots/                # Generated verification plots
```

---

## Quality Assurance

### Before Submitting for Review

1. Self-review: Re-read entire proof checking each step
2. Dimensional check: Verify all equations have consistent units
3. Limit check: Verify known physics recovered
4. Dependency audit: Confirm all prerequisites are proven
5. Notation consistency: Verify symbols used consistently
6. Reference check: Verify all citations are accurate

### Peer Review Preparation

For a proof to be considered "peer-review ready":
- [ ] All mathematical statements precise and unambiguous
- [ ] All assumptions explicitly stated
- [ ] Logical chain complete with no gaps
- [ ] Consistency checks pass
- [ ] Novel claims clearly distinguished from established physics
- [ ] Testable predictions identified
- [ ] Known difficulties or open questions acknowledged
- [ ] References to prior work accurate and complete

---

*Last Updated: 2025-12-12*
*Version: 3.0 (Condensed)*
*Status: Active Development*
