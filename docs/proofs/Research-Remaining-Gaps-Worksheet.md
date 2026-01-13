# Research Worksheet: Addressing Remaining Major Gaps

## Status: 🔶 ACTIVE RESEARCH AGENDA

**Created:** 2026-01-06
**Purpose:** Systematic plan to address the remaining major gaps in Chiral Geometrogenesis after the completion of Propositions 0.0.5a (Strong CP) and 5.2.1b (Einstein equations).

---

## Executive Summary

With the Strong CP problem and non-thermodynamic Einstein derivation now resolved, CG has established:
- ✅ 4D spacetime (Theorem 0.0.1)
- ✅ SU(3) color from geometry (Theorem 0.0.15)
- ✅ Left-handed chirality (Theorem 0.0.5)
- ✅ θ = 0 exactly (Proposition 0.0.5a) — **NEW**
- ✅ Einstein equations directly (Proposition 5.2.1b) — **NEW**
- ✅ Newton's constant G (Proposition 5.2.4a)
- ✅ Cosmological constant (Theorem 5.1.2)
- ✅ Fermion mass hierarchy (Theorem 3.1.1-3.1.2)

**Remaining major gaps:**

| Gap | Priority | Difficulty | Estimated Effort |
|-----|----------|------------|------------------|
| 1. Electroweak sector (SU(2)×U(1)) | 🔴 HIGH | Hard | Major |
| 2. Higgs physics | 🔴 HIGH | Hard | Major |
| 3. PMNS matrix & neutrino physics | 🟡 MEDIUM | Medium | Moderate |
| 4. Dark matter integration | 🟡 MEDIUM | Medium | Moderate |
| 5. Gravity quantization | 🟢 LOWER | Very Hard | Long-term |
| 6. QCD dynamics (kinematic→dynamical) | 🟢 LOWER | Very Hard | Long-term |

---

## Gap 1: Electroweak Sector (SU(2)×U(1))

### 1.1 Current Status

**What exists:**
- ✅ Theorem 0.0.4: GUT structure stella → 16-cell → 24-cell → D₄ → SO(10) → SU(5) ⊃ SU(3)×SU(2)×U(1)
- ✅ Theorem 4.2.3: First-order electroweak phase transition (VERIFIED, Lean formalized)
- ✅ Prediction: GW background Ω_GW h² ~ 10⁻¹⁰ at f ~ 1-10 mHz (LISA detectable)

**What's missing:**
- ❌ Explicit SU(2)×U(1) gauge fields from geometry
- ❌ W and Z boson masses from first principles
- ❌ Weinberg angle θ_W derivation
- ❌ Electroweak precision tests (S, T, U parameters)
- ❌ Sphaleron physics and baryon number violation rate

### 1.2 Proposed Approach

**Strategy A: Complete the GUT Breaking Chain**

The SU(5) embedding (Theorem 0.0.4) gives SU(3)×SU(2)×U(1) as a subgroup. Need to:

1. **Derive the breaking pattern geometrically**
   - Show how stella octangula geometry selects SU(3)×SU(2)×U(1) from SU(5)
   - The stella has natural SU(3) (color vertices) and residual SU(2)×U(1) structure
   - Key: The W vertex (fourth state) may play role in symmetry breaking

2. **Calculate gauge coupling ratios**
   - At GUT scale: g₃ = g₂ = √(5/3) g₁
   - Run down to electroweak scale using β-functions
   - Check: sin²θ_W = 3/8 at GUT scale → 0.231 at M_Z

3. **Derive W and Z masses**
   - M_W = (1/2) g₂ v_H where v_H = 246 GeV
   - M_Z = M_W / cos θ_W
   - **Challenge:** Need to derive v_H from CG geometry (see Gap 2)

**Strategy B: Direct SU(2) from Stella Geometry**

Alternative approach using stella octangula directly:

1. **Stella has natural SU(2) substructure**
   - Two interpenetrating tetrahedra ↔ SU(2) doublet structure?
   - The tetrahedron vertices form a 4-element set → quaternions → SU(2)

2. **U(1)_Y from overall phase**
   - Hypercharge Y = B - L + ... (requires lepton number assignment)
   - May emerge from the rotation parameter λ (internal time)

### 1.3 Specific Tasks

| Task | Description | Prerequisite | Output |
|------|-------------|--------------|--------|
| 1.1 | Derive SU(2) gauge fields from stella geometry | Theorem 0.0.4 | Proposition |
| 1.2 | Derive U(1)_Y hypercharge assignment | Task 1.1 | Proposition |
| 1.3 | Calculate sin²θ_W at M_Z scale | Tasks 1.1, 1.2 | Prediction |
| 1.4 | Derive M_W from geometry + Higgs VEV | Tasks 1.1-1.3, Gap 2 | Theorem |
| 1.5 | Derive M_Z and check ρ = M_W²/(M_Z² cos²θ_W) = 1 | Task 1.4 | Verification |
| 1.6 | Calculate S, T oblique parameters | Tasks 1.4-1.5 | Predictions |
| 1.7 | Sphaleron rate from CG topology | Tasks 1.1-1.2 | Proposition |

### 1.4 Key Questions to Resolve

1. **Does the W vertex participate in SU(2)?**
   - Current: W vertex hosts dark matter (χ_W condensate)
   - Question: Is there a relationship between W_vertex and W_boson?

2. **How does π₃(SU(2)) = ℤ manifest?**
   - For SU(3): Instantons give chirality selection (Theorem 0.0.5)
   - For SU(2): Should give weak isospin solitons (sphalerons?)

3. **What breaks SU(2)×U(1) → U(1)_EM?**
   - Standard: Higgs mechanism
   - CG: Must derive Higgs from χ field structure (Gap 2)

### 1.5 References to Consult

- [Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md](foundations/Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md)
- [Theorem-4.2.3-First-Order-Phase-Transition.md](Phase4/Theorem-4.2.3-First-Order-Phase-Transition.md)
- Georgi & Glashow (1974) — SU(5) GUT
- Weinberg (1967) — Electroweak unification

---

## Gap 2: Higgs Physics

### 2.1 Current Status

**What exists:**
- ✅ Higgs mass m_h = 125 GeV (mentioned as matching observation)
- ✅ First-order EWPT mechanism (Theorem 4.2.3)
- ✅ Higgs portal coupling λ_HΦ ≈ 0.036 (for dark matter)

**What's missing:**
- ❌ Derivation of Higgs potential V(Φ) from geometry
- ❌ Derivation of Higgs VEV v = 246 GeV
- ❌ Higgs self-coupling λ prediction
- ❌ Higgs decay widths from CG

### 2.2 Proposed Approach

**Strategy: Higgs as χ Field Component**

The χ field has color structure (R, G, B vertices). The Higgs should emerge as:

1. **Color-singlet component of χ**
   - χ_R + χ_G + χ_B transforms as color singlet
   - This combination could BE the Higgs doublet (after SU(2) assignment)

2. **Potential from self-interaction**
   - The stella octangula geometry creates effective potential
   - At stable center: V(0) = 0 (cancellation)
   - Away from center: V(|Φ|) = -μ²|Φ|² + λ|Φ|⁴

3. **VEV from geometric scale**
   - v = f_χ × (geometric factor)
   - f_χ appears in Newton's constant: G = 1/(8πf_χ²)
   - Challenge: Extract v = 246 GeV

### 2.3 Specific Tasks

| Task | Description | Prerequisite | Output |
|------|-------------|--------------|--------|
| 2.1 | Identify Higgs within χ field decomposition | Theorem 0.2.1 | Definition |
| 2.2 | Derive Higgs potential V(Φ) from stella geometry | Task 2.1 | Proposition |
| 2.3 | Calculate μ² and λ parameters | Task 2.2 | Predictions |
| 2.4 | Derive VEV v = 246 GeV | Tasks 2.2-2.3 | Theorem |
| 2.5 | Predict Higgs self-coupling λ₃ | Task 2.4 | Prediction 8.x.x |
| 2.6 | Calculate h → γγ, h → Zγ from CG | Tasks 2.1-2.5, Gap 1 | Predictions |

### 2.4 Key Questions to Resolve

1. **Is the Higgs fundamental or composite in CG?**
   - If χ is fundamental, Higgs as χ component is "fundamental"
   - But χ emerges from geometry, so ultimately composite

2. **What sets the electroweak scale v = 246 GeV?**
   - Must connect to f_χ (Planck-scale quantity)
   - Hierarchy problem: Why v << M_Planck?
   - CG answer should come from geometric suppression

3. **Does CG predict Higgs portal physics?**
   - Dark matter couples via λ_HΦ ≈ 0.036
   - What other portals exist?

### 2.5 Connection to Other Gaps

- **Gap 1 (Electroweak):** Need Higgs to break SU(2)×U(1) → U(1)_EM
- **Gap 3 (Neutrinos):** Higgs gives Dirac masses; Majorana needs more
- **Gap 4 (Dark matter):** Higgs portal is main coupling to visible sector

---

## Gap 3: PMNS Matrix and Neutrino Physics

### 3.1 Current Status

**What exists:**
- ✅ CKM matrix fully derived (Prediction 8.1.1, Extension 3.1.2b)
- ✅ All 4 Wolfenstein parameters from geometry
- ✅ Right-handed neutrinos are sterile (Corollary 3.1.3)
- ✅ Three generations necessary (Prediction 8.1.3, 4 independent proofs)

**What's missing:**
- ❌ PMNS matrix elements from geometry
- ❌ Neutrino mass squared differences Δm²_ij
- ❌ CP violation phase δ_CP (leptonic)
- ❌ Majorana vs Dirac nature determination

### 3.2 Proposed Approach

**Strategy: Parallel CKM Derivation for Leptons**

The CKM derivation uses:
- Quark localization on stella octangula vertices
- Overlap integrals between generations
- S₄ symmetry breaking pattern

Apply same logic to leptons:

1. **Lepton localization**
   - Where do e, μ, τ live on stella?
   - Where do ν_e, ν_μ, ν_τ live?

2. **PMNS from overlap integrals**
   - U_PMNS = V_ℓ† V_ν
   - V_ℓ, V_ν from geometric overlaps

3. **Tribimaximal as zeroth order**
   - The stella has natural √3, √2 factors
   - Tribimaximal: sin²θ₁₂ = 1/3, sin²θ₂₃ = 1/2, θ₁₃ = 0
   - Corrections from higher-order geometry

### 3.3 Specific Tasks

| Task | Description | Prerequisite | Output |
|------|-------------|--------------|--------|
| 3.1 | Assign lepton generations to stella positions | Theorem 3.1.2 | Definition |
| 3.2 | Calculate lepton mixing angles from overlaps | Task 3.1 | Proposition |
| 3.3 | Derive θ₁₃ ≈ 8.5° correction | Task 3.2 | Prediction |
| 3.4 | Calculate Δm²₂₁ and Δm²₃₁ | Tasks 3.1-3.2, Theorem 3.1.1 | Predictions |
| 3.5 | Predict leptonic CP phase δ_CP | Tasks 3.2-3.3 | Prediction |
| 3.6 | Determine Majorana vs Dirac nature | Corollary 3.1.3 | Theorem |

### 3.4 Key Questions to Resolve

1. **Why are neutrino masses so small?**
   - CKM: m_t/m_u ~ 10⁵ (large hierarchy)
   - PMNS: m_ν/m_e ~ 10⁻⁶ (even smaller)
   - Seesaw mechanism from CG?

2. **Is there a geometric reason for large mixing?**
   - CKM angles are small (V_cb ~ 0.04)
   - PMNS angles are large (θ₂₃ ~ 45°)
   - Different localization pattern for neutrinos?

3. **What determines Majorana phases?**
   - Two additional CP phases in PMNS (Majorana)
   - Geometric origin from stella?

### 3.5 References

- [Extension-3.1.2b-CKM-From-Geometry.md](Phase3/Extension-3.1.2b-CKM-From-Geometry.md)
- [Prediction-8.1.3-Three-Generation-Necessity.md](Phase8/Prediction-8.1.3-Three-Generation-Necessity.md)
- Harrison, Perkins, Scott (2002) — Tribimaximal mixing

---

## Gap 4: Dark Matter Integration

### 4.1 Current Status

**What exists:**
- ✅ W-condensate dark matter (Dark-Matter-Extension-W-Condensate.md)
- ✅ Mass M_W ≈ 1.7 TeV from Skyrme formula
- ✅ Asymmetric dark matter production resolves thermal tension
- ✅ Direct detection σ_SI ≈ 1.6×10⁻⁴⁷ cm² (DARWIN testable)
- ✅ Ω_W h² = 0.12 from geometric ADM mechanism

**What's missing:**
- ❌ Integration into main framework (currently "extension")
- ❌ Derivation of v_W = v_H/√3 from first principles
- ❌ Cosmological structure formation analysis
- ❌ Alternative DM candidates within CG (T₂ solitons?)

### 4.2 Proposed Approach

**Strategy: Promote Extension to Derivation**

1. **Derive W vertex properties from axioms**
   - The fourth vertex is geometrically determined
   - Phase φ_W = π follows from maximally antipodal position
   - Show this is REQUIRED, not just consistent

2. **Calculate v_W rigorously**
   - Current: v_W = v_H/√3 ≈ 142 GeV (stated)
   - Need: Derive from χ field dynamics
   - Key: SU(3) singlet projection gives √3 factor

3. **Analyze cosmological constraints**
   - Power spectrum compatible with CDM?
   - Self-interaction limits (σ/m < 1 cm²/g from Bullet Cluster)
   - Warm vs cold determination

### 4.3 Specific Tasks

| Task | Description | Prerequisite | Output |
|------|-------------|--------------|--------|
| 4.1 | Derive W vertex existence from stella axioms | Definition 0.0.0 | Theorem |
| 4.2 | Derive φ_W = π from geometry | Task 4.1 | Proposition |
| 4.3 | Derive v_W = v_H/√3 rigorously | Task 4.2, Gap 2 | Proposition |
| 4.4 | Calculate self-interaction cross-section | Task 4.3 | Prediction |
| 4.5 | Analyze structure formation compatibility | Task 4.4 | Verification |
| 4.6 | Identify alternative DM candidates | Tasks 4.1-4.3 | Research |

### 4.4 Key Questions to Resolve

1. **Is W-condensate the ONLY dark matter?**
   - Or could there be additional stable particles?
   - T₂ (second tetrahedron) solitons?

2. **What about axion DM?**
   - Proposition 0.0.5a removes need for axion (Strong CP)
   - But axions could exist for other reasons
   - Does CG predict axion-like particles?

3. **How does W-DM interact gravitationally?**
   - Same G as visible matter (universal coupling)
   - But emergence process might differ

### 4.5 References

- [Dark-Matter-Extension-W-Condensate.md](supporting/Dark-Matter-Extension-W-Condensate.md)
- [Proposition-5.2.4a-Induced-Gravity-From-Chiral-One-Loop.md](Phase5/Proposition-5.2.4a-Induced-Gravity-From-Chiral-One-Loop.md)

---

## Gap 5: Gravity Quantization

### 5.1 Current Status

**What exists:**
- ✅ Classical Einstein equations derived (Proposition 5.2.1b)
- ✅ Newton's constant from χ loop (Proposition 5.2.4a)
- ✅ Cosmological constant solved (Theorem 5.1.2)

**What's missing:**
- ❌ Quantum corrections to Einstein equations
- ❌ Black hole entropy from CG
- ❌ Graviton as emergent degree of freedom
- ❌ UV completion of quantum gravity

### 5.2 Proposed Approach

**Strategy: Emergent Gravity is Automatically Finite**

1. **No UV divergences expected**
   - Gravity emerges from χ field (already renormalized, Phase 7)
   - No separate graviton propagator to regulate
   - UV completion is the χ theory itself

2. **Black hole entropy from χ modes**
   - Horizon area counts χ field degrees of freedom
   - S_BH = A/(4G) should emerge from χ state counting
   - Connection to Z₃ boundary states (Lemma 5.2.3b.2)

3. **Graviton as collective mode**
   - Metric fluctuation h_μν = g_μν - η_μν
   - Propagator emerges from χ correlator
   - Spin-2 from stress-energy conservation

### 5.3 Specific Tasks (Long-term)

| Task | Description | Prerequisite | Output |
|------|-------------|--------------|--------|
| 5.1 | Analyze quantum corrections to G_μν | Phase 7, Prop 5.2.1b | Research |
| 5.2 | Derive black hole entropy from χ states | Task 5.1, Lemma 5.2.3b.2 | Theorem |
| 5.3 | Identify graviton in χ spectrum | Tasks 5.1-5.2 | Proposition |
| 5.4 | Show UV finiteness of emergent gravity | Phase 7 | Theorem |
| 5.5 | Calculate quantum gravitational corrections | Tasks 5.1-5.4 | Predictions |

### 5.4 Key Questions to Resolve

1. **Is CG gravity fundamentally classical?**
   - If metric emerges from expectation values, fluctuations are χ fluctuations
   - "Quantum gravity" might be misnomer in CG

2. **How does CG handle singularities?**
   - Black hole singularities
   - Big Bang singularity
   - χ field might regulate these

3. **What is the Planck scale in CG?**
   - M_Planck = 1/√G from Newton's constant
   - But f_χ might be the fundamental scale

4. **Does CG provide a UV-complete theory of quantum gravity?** ✅ VERIFIED (2026-01-12)
   - **Resolution:** Theorem 7.3.1 establishes **conditional UV completeness** through four mechanisms:
     1. Emergence resolution (no fundamental graviton → no graviton loops)
     2. χ-field as UV regulator (controlled EFT below Λ ≈ 8-15 TeV)
     3. Holographic self-consistency (Planck scale derived to 91%)
     4. Index-theoretic control (UV coupling = 64 from topology)
   - **Key result:** All gravitational observables are χ-field correlations
   - **Conditional:** Assumes emergent gravity has no independent UV divergences
   - **Multi-Agent Verification:** Math ✅, Physics ✅, Literature ✅, Numerical ✅
   - **Verification Report:** [Theorem-7.3.1-Multi-Agent-Verification-2026-01-12.md](verification-records/Theorem-7.3.1-Multi-Agent-Verification-2026-01-12.md)
   - **See:** [Theorem-7.3.1-UV-Completeness-Emergent-Gravity.md](Phase7/Theorem-7.3.1-UV-Completeness-Emergent-Gravity.md)

---

## Priority Matrix and Timeline

### Immediate Priorities (Next Phase)

```
┌─────────────────────────────────────────────────────────┐
│  HIGH IMPACT + TRACTABLE                                │
│                                                         │
│  1. Higgs VEV derivation (Gap 2.4)                     │
│     - Unlocks electroweak sector                       │
│     - Single key calculation                           │
│                                                         │
│  2. SU(2) gauge fields from geometry (Gap 1.1)         │
│     - Uses existing GUT structure                      │
│     - Parallel to SU(3) derivation                     │
│                                                         │
│  3. W vertex derivation (Gap 4.1-4.2)                  │
│     - Promotes extension to theorem                    │
│     - Already have the answer, need rigor              │
└─────────────────────────────────────────────────────────┘
```

### Medium-term Goals

| Goal | Dependencies | Target |
|------|--------------|--------|
| Complete electroweak sector | Gaps 1, 2 | Phase 6 creation |
| PMNS matrix | Gap 3 | Extension to 3.1.2b |
| Dark matter theorem | Gap 4 | Promote to main proof |

### Long-term Research

- Quantum gravity aspects (Gap 5)
- GUT unification details
- Proton decay predictions

---

## Organizational Recommendations

### 1. Create Phase 6: Electroweak Phenomenology

**Proposed contents:**
- Theorem 6.1.1: SU(2)×U(1) Gauge Structure
- Theorem 6.1.2: Weinberg Angle
- Theorem 6.2.1: W Boson Mass
- Theorem 6.2.2: Z Boson Mass and Width
- Theorem 6.3.1: Electroweak Precision (S, T, U)
- Proposition 6.4.1: Sphaleron Rate

### 2. Restructure Dark Matter

**Move from extension to main proof:**
- Rename: `Dark-Matter-Extension-W-Condensate.md` → `Theorem-4.3.1-W-Condensate-Dark-Matter.md`
- Move to Phase 4 (Topological Solitons and Matter)
- Add rigorous derivation sections

### 3. Create Unified Predictions Document

**Consolidate all predictions:**
- Testable at current experiments (LHC, LISA, nEDM)
- Testable at future experiments (FCC, DARWIN, CMB-S4)
- Falsifiable signatures unique to CG

---

## Gap 6: QCD Dynamics (Kinematic → Dynamical)

### 6.1 Current Status

**What exists (kinematic):**
- ✅ SU(3) weight structure from stella (Theorem 0.0.15)
- ✅ Color neutrality as geometric closure (Theorem 1.1.3)
- ✅ Z₃ center symmetry criterion for confinement (Theorem 0.0.3)
- ✅ String tension σ = 0.19 GeV² from Casimir energy (Proposition 0.0.17j) — 99.7% match
- ✅ Pressure confinement mechanism (Theorem 2.1.2) — Lattice verified
- ✅ Bag equilibrium given B (Theorem 2.1.1)

**What's missing (dynamical):**
- ❌ Wilson loop area law ⟨W(C)⟩ ~ exp(−σ·Area) from geometry
- ❌ Bag constant B ≈ (145 MeV)⁴ from first principles
- ❌ Asymptotic freedom (running of αₛ) — used, not derived
- ❌ Glueball spectrum from geometry

### 6.2 Important Distinction

The stella-SU(3) correspondence is **kinematic** (encoding symmetry structure), not **dynamical** (deriving QCD field equations). This is an acknowledged scope boundary:

> *"The correspondence satisfies precisely defined conditions for weight correspondence, Weyl symmetry preservation, and charge conjugation compatibility... We emphasize a crucial distinction: while the framework derives GR and QM, the stella-SU(3) correspondence itself is kinematic, not dynamical."* — Unified paper abstract

This is analogous to:
- Representation theory tells you what states exist, not transition rates
- Group theory gives selection rules, not matrix elements
- Geometry encodes symmetry, not dynamics

### 6.3 What WOULD Be Required

| Gap | What's Needed | Difficulty | Comment |
|-----|---------------|------------|---------|
| **Wilson loop area law** | Derive ⟨W(C)⟩ ~ exp(−σA) from stella | ⭐⭐⭐⭐⭐ | Would require geometric lattice QCD |
| **Bag constant B** | Derive B = (145 MeV)⁴ from vacuum structure | ⭐⭐⭐⭐ | Open problem even in standard QCD |
| **Asymptotic freedom** | Derive β-function from geometry | ⭐⭐⭐⭐⭐ | Nobel Prize level (Gross-Wilczek-Politzer) |
| **Confinement proof** | Prove linear potential V(r) ~ σr | ⭐⭐⭐⭐⭐ | Millennium Prize problem |

### 6.4 Partial Progress Already Made

Despite being "kinematic", significant dynamical-adjacent results exist:

1. **String tension derived (Prop 0.0.17j):**
   - σ = (ℏc/R_stella)² = 0.19 GeV²
   - This matches Cornell potential to 99.7%
   - Derived from Casimir vacuum energy, not fitted

2. **Pressure gradient verified (Thm 2.1.2):**
   - Chiral field creates confining pressure
   - Independently verified by Iritani et al. (2015) lattice QCD

3. **Effective string tension (Thm 4.1.4):**
   - σ_eff ≈ 0.236 GeV² from soliton dynamics
   - 30% above Cornell (different regime)

### 6.5 Honest Assessment

**What CG actually provides for QCD:**
- Geometric encoding of color quantum numbers
- Visualization of confinement selection rules  
- Derived string tension (major partial result)
- Consistent framework for hadron structure

**What CG does NOT provide:**
- Replacement for QCD field theory
- Derivation of non-abelian dynamics from geometry
- Proof of confinement from first principles

**Recommended stance:** The kinematic/dynamical boundary is a legitimate scope limit. CG derives the symmetry structure; QCD provides the dynamics. They are complementary, not competing.

### 6.6 Future Directions (Long-term)

If these gaps were to be addressed:

| Approach | Description | Feasibility |
|----------|-------------|-------------|
| **Geometric Wilson loops** | Define Wilson loops on honeycomb lattice | Research project |
| **Emergent gluons** | Derive gluon fields as collective modes of χ | Very speculative |
| **Running from topology** | β-function from instanton counting | Possible avenue |
| **Bag from boundary** | B from stella surface energy | Partially tractable |

These are **long-term research directions**, not gaps blocking the current paper.

---

## Summary Table

| Gap | Key Task | Blocks | Blocked By | Est. Difficulty |
|-----|----------|--------|------------|-----------------|
| **1. EW Sector** | Derive SU(2) from geometry | Gap 2, many predictions | Theorem 0.0.4 | ⭐⭐⭐⭐ |
| **2. Higgs** | Derive v = 246 GeV | Gap 1 (masses) | χ field structure | ⭐⭐⭐ |
| **3. Neutrinos** | PMNS from geometry | — | Gap 1 (partially) | ⭐⭐⭐ |
| **4. Dark Matter** | Promote to theorem | — | Gap 2 (v_W = v_H/√3) | ⭐⭐ |
| **5. Quantum Gravity** | UV finiteness | — | Phase 7 | ⭐⭐⭐⭐⭐ |
| **6. QCD Dynamics** | Kinematic → Dynamical | — | Fundamental research | ⭐⭐⭐⭐⭐ |

**Recommended attack order:** 2 → 4 → 1 → 3 → 5

The Higgs (Gap 2) and W-vertex (Gap 4) are most tractable and unblock the others.

---

## Appendix: Cross-Reference to Existing Documents

### Foundations
- [Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md](foundations/Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md)
- [Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md](foundations/Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md)

### Phase 3 (Masses)
- [Theorem-3.1.1-Chiral-Drag-Mass-Formula.md](Phase3/Theorem-3.1.1-Chiral-Drag-Mass-Formula.md)
- [Extension-3.1.2b-CKM-From-Geometry.md](Phase3/Extension-3.1.2b-CKM-From-Geometry.md)

### Phase 4 (Solitons)
- [Theorem-4.2.3-First-Order-Phase-Transition.md](Phase4/Theorem-4.2.3-First-Order-Phase-Transition.md)

### Phase 5 (Gravity)
- [Proposition-5.2.1b-Einstein-Equations-From-Fixed-Point-Uniqueness.md](Phase5/Proposition-5.2.1b-Einstein-Equations-From-Fixed-Point-Uniqueness.md)
- [Theorem-5.1.2-Vacuum-Energy-Density.md](Phase5/Theorem-5.1.2-Vacuum-Energy-Density.md)

### Supporting
- [Dark-Matter-Extension-W-Condensate.md](supporting/Dark-Matter-Extension-W-Condensate.md)

---

*Worksheet created: 2026-01-06*
*Status: Active research agenda*
*Next review: After completing Gap 2 (Higgs VEV derivation)*
