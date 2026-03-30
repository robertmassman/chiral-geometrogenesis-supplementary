# Module V7: Falsifiability & Empirical Contact — COMPLETE (×4 Independent Verification)

> **Audit:** G1 Geometric Foundation Validity Audit
> **Module:** V7 (Falsifiability & Empirical Contact)
> **Date:** 2026-03-15 (original through ×3); 2026-03-15 (fourth round — post-resolution verification)
> **Status:** All 26 G1 files examined; predictions classified, falsifiability assessed; resolution fixes V3.6/V3.9/V4.2/V4.14/V4.15 verified
> **Auditor:** Claude (Validity Audit — V7 Fourth Round, Opus 4.6)
> **Companion:** [G1-Geometric-Foundation-Validity-Audit.md](G1-Geometric-Foundation-Validity-Audit.md) §V7
> **Cross-references:** [V1 Findings](G1-Validity-Audit-Module-V1-Findings.md), [V3 Findings](G1-Validity-Audit-Module-V3-Findings.md), [V6 Findings](G1-Validity-Audit-Module-V6-Findings.md), [Resolution Report](G1-Geometric-Foundation-Validity-Resolution-Report.md)

---

## Overview

**Goal:** Determine which claims in G1 are genuine predictions vs retrodictions, identify concrete falsification criteria, and assess the group's empirical contact with observable physics.

**Method:** For each of the 26 G1 files: (1) classify every empirically-relevant claim as PREDICTION, RETRODICTION, or FRAMEWORK-INTERNAL, (2) identify what experimental result would falsify it, (3) assess whether falsification is practically achievable, (4) determine whether G1 as a whole makes contact with experiment or merely enables downstream contact.

**Files examined:** All 26 G1 proof files — F01 (Def 0.0.0), F02 (Thm 0.0.1), F03 (Thm 0.0.2), F04 (Thm 0.0.2b), F05 (Lem 0.0.2a), F06 (Prop 0.0.40), F07 (Thm 0.0.0a), F08 (Prop 0.0.XX), F09 (Thm 0.0.3), F10 (Thm 0.0.3b), F11 (Prop 0.0.16a), F12 (Thm 0.0.16), F13 (Thm 0.0.6), F14 (Prop 0.0.6b), F15 (Thm 0.0.9), F16 (Thm 0.0.15), F17 (Thm 0.0.12), F18 (Thm 0.0.13), F19 (Def 0.1.1), F20 (Def 0.1.2), F21 (Def 0.1.3), F22 (Prop 0.1.3a), F23 (Def 0.1.4), F24 (Thm 0.1.0), F25 (Thm 1.1.1), F26 (Def 1.1.4)

**Fourth-round method:** Verified all 26 checks against six resolution report fixes (commits 551830a6, a96a4b46, e92a29f4, f1356c04, f27e5452). Three parallel sub-agents independently re-read all 26 proof files to extract falsifiability claims. Results cross-checked against prior three rounds. 1 verdict change this round.

**Classification Key — Empirical Categories:**

| Category | Definition |
|----------|------------|
| **PREDICTION** | Novel claim about observables not used as input; falsifiable in principle |
| **RETRODICTION** | Claim that reproduces already-known physics; explanatory but not predictive |
| **FRAMEWORK-INTERNAL** | Mathematical/structural claim with no direct empirical content |
| **ENABLING** | Makes no predictions itself but is load-bearing for downstream predictions |

**Classification Key — Finding Ratings:**

| Rating | Meaning |
|--------|---------|
| **SOUND** | Falsifiability status is honestly presented; empirical contact accurately characterized |
| **QUALIFIED** | Falsifiability exists but is overstated, understated, or practically inaccessible |
| **WEAK** | Claimed prediction is actually a retrodiction, or falsifiability is illusory |
| **INVALID** | Falsifiability claim is fundamentally misleading |
| **SMUGGLED** | Empirical input is used but not declared, making a "derivation" actually a retrodiction |

---

## V7 Summary

| Metric | Round ×3 | This round (×4) |
|--------|----------|-----------------|
| Total checks | 26 | 26 |
| SOUND | 15 | 16 |
| QUALIFIED | 10 | 9 |
| WEAK | 0 | 0 |
| INVALID | 0 | 0 |
| SMUGGLED | 1 | 1 |

| Empirical Category | Count |
|--------------------|-------|
| Genuine PREDICTION | 2 |
| Conditional PREDICTION (framework-dependent) | 4 |
| RETRODICTION | 8 |
| FRAMEWORK-INTERNAL (no empirical content) | 7 |
| ENABLING (load-bearing for downstream predictions) | 5 |

**Fourth-round changes:**

1. **V7.8 (Prop 0.0.XX): QUALIFIED → SOUND.** Resolution commit a96a4b46 (V4.14) aligned the status line to read "RETRODICTION FROM DISTINGUISHABILITY" and added prominent "Important Limitation" box with A-IF dependency. The prior residual issue (status line suggesting derivation) is now resolved. The file is the gold standard for epistemic transparency in G1.

2. **V7.1 (Def 0.0.0): SOUND confirmed.** Resolution commit 551830a6 (V4.15) added V4.15 Transparency Note making axiom package's role as selection device explicit. This strengthens the existing SOUND verdict — no change needed.

3. **V7.4 (Thm 0.0.2b), V7.5 (Lem 0.0.2a), V7.6 (Prop 0.0.40), V7.13 (Thm 0.0.6): unchanged.** V3.9 common axiom dependency notes prevent false independence inflation across four dimensionality proofs. This is a cross-file finding affecting Part II synthesis, not individual check verdicts.

4. **V7.7 (Thm 0.0.0a): SOUND confirmed.** V4.2 scope clarification narrows necessity claim to pre-geometric emergence. Existing SOUND verdict already accounted for resolved S8/S9/S28.

5. **V7.9, V7.10 (Thm 0.0.3, 0.0.3b): SOUND confirmed.** V4.15 scope notes added. Already SOUND.

**Overall verdict:** G1 contains **zero directly testable predictions** of new observables. Its empirical contact is entirely **indirect**, mediated through downstream propositions (0.0.17j–n, Phase 8 predictions). The two claims closest to genuine predictions — Theorem 0.0.2b (D = N+1 for confining SU(N)) and Proposition 0.0.6b (lattice spacing a ≈ 2.25 ℓ_P) — are either untestable with current technology or require hypothetical new physics to test. The group's primary empirical value is **retrodictive**: it explains why D = 4, why SU(3), why Euclidean geometry, and why the stella octangula, but all of these are known facts being reconstructed, not predicted. One SMUGGLED finding: Prop 0.0.6b imports a lattice spacing prediction from Prop 0.0.17r (outside G1) without clear provenance, and presents the Coleman (1985) θ = 0 result as a framework derivation. No INVALID findings.

**Fourth-round key insight (V3.9 impact):** The four dimensionality proofs (Thm 0.0.2b, Lem 0.0.2a, Prop 0.0.40, Thm 0.0.6) now explicitly acknowledge they share the same core axiom (Definition 0.0.0's geometric realization postulate F1). This prevents any reader from counting them as "multiple independent confirmations" of D = 3 / d_embed = N. If F1 fails, all four collapse simultaneously. This is the most significant epistemic clarification from the resolution fixes for V7 purposes.

---

## Part I: Check-by-Check Falsifiability Assessment

### V7.1 — Def 0.0.0: Minimal Geometric Realization

**Empirical category:** FRAMEWORK-INTERNAL (axiomatization)
**Result: SOUND**

This is an axiomatic definition (GR1–GR3, MIN1–MIN3). Definitions are neither true nor false — they define the framework's scope. The document is transparent about this: axioms are labeled as framework choices throughout.

**Resolution verification (V4.15, commit 551830a6):** V4.15 Transparency Note (§1.1) now explicitly states that GR1–GR3 + MIN1–MIN3 "collectively function as a selection device" and that "alternative axiom sets could select different objects." Three concrete alternatives are analyzed (adjoint rep, non-minimal, simplicial). This exemplary transparency strengthens the existing SOUND verdict.

**Falsifiability:** Not applicable to definitions. However, the *package* of axioms can be assessed by whether the framework they enable produces correct predictions. If downstream predictions fail systematically, these axioms would be implicated.

**What would falsify the framework choice?** Discovery that a non-polyhedral pre-geometric substrate can produce emergent spacetime without presupposing manifold structure (contradicting Theorem 0.0.0a's necessity argument).

**Key observation:** Framework axiom F1 (geometric realization postulate) is the load-bearing unfalsifiable premise. It is described as "Maximally destructive — collapses 17/23 G1 files" if removed. No experimental result could directly falsify F1 as currently stated, because it is a claim about which mathematical structure to *use* for describing pre-geometric physics. This is acknowledged but not prominently foregrounded in every file that depends on it.

**Evidence:** `docs/proofs/foundations/Definition-0.0.0-Minimal-Geometric-Realization.md` — axioms clearly labeled as framework choices; V4.15 Transparency Note at §1.1.

---

### V7.2 — Thm 0.0.1: D=4 From Observer Existence

**Empirical category:** RETRODICTION (explains known D = 4)
**Result: QUALIFIED**

**What it claims:** D = 4 is uniquely selected by observer existence requirements (atomic stability, orbital stability, signal propagation).

**Retrodiction vs prediction assessment:**
- **Retrodictive:** We already know D = 4. The theorem explains *why* D = 4 using established physics (Ehrenfest 1917, Bertrand's theorem, Huygens' principle, virial theorem).
- **Not predictive:** No new observable is predicted. The theorem cannot be tested by discovering D ≠ 4.
- **Explanatory value:** Genuine — provides 7+ independent physical constraints all pointing to D = 4.
- **CDT framing issue (persists):** Stream B cites CDT results (d_H = 4.01 ± 0.05) as "independent corroboration" — but CDT is a computational model, not experimental data. Presenting simulation results alongside observational constraints (P1–P4) conflates different epistemic categories.
- **Status marker issue:** The status "✅ ESTABLISHED — D = 4 UNIQUELY SELECTED BY OBSERVER EXISTENCE AND DYNAMICAL MECHANISMS" bundles anthropic arguments (P1–P4) with dynamical computations (CDT). These are epistemically different: one is a selection criterion assuming observers exist, the other is a lattice quantum gravity calculation.

**Falsifiability:**
- Falsified if stable atoms exist in D ≠ 4 (requires new physics or mathematical discovery)
- Falsified if observers can exist without carbon-based chemistry (philosophical, not experimental)
- **Practical falsifiability: NONE** — we cannot experimentally access D ≠ 4

**Why QUALIFIED:** The proof correctly acknowledges its anthropic/contingent nature (§0). However, the title "D=4 From Observer Existence" frames this as a *derivation* when it is more accurately an *anthropic selection argument*. The CDT conflation and status marker bundling are minor presentation risks.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.1-D4-From-Observer-Existence.md`

---

### V7.3 — Thm 0.0.2: Euclidean ℝ³ From SU(3)

**Empirical category:** RETRODICTION (explains known Euclidean geometry)
**Result: QUALIFIED**

**What it claims:** The Euclidean metric on ℝ³ is uniquely determined by SU(3) weight space via the Killing form.

**Retrodiction vs prediction assessment:**
- **Retrodictive:** Euclidean geometry of physical space is already known. The theorem explains it through SU(3) representation theory.
- **Novel element:** The claim that Euclidean geometry is *forced* by SU(3) (not merely compatible) is a framework-specific strengthening.
- **Language issue (persists):** Three instances of "uniquely compatible" at lines 84, 451, 865 lack framework scope qualifier (flagged in V6.3, still present).

**Falsifiability:**
- Falsified if weight space were non-Euclidean — but this contradicts standard Lie theory, so this "falsification" is mathematically impossible given the premises
- Falsified if physical space were non-Euclidean at fundamental scales — requires probing Planck-scale geometry
- **Practical falsifiability: NONE at current experimental reach**

**Why QUALIFIED:** The uniqueness claim (§4.3) is rigorous given four premises (S₃ symmetry, isotropy, positive-definiteness, smoothness), but these are framework-specific choices (flagged in V1.3 as S6, S7). The falsifiability depends on whether these premises are physically necessary — an open question the proof doesn't address.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.2-Euclidean-From-SU3.md`

---

### V7.4 — Thm 0.0.2b: Dimension-Color Correspondence (D = N+1)

**Empirical category:** CONDITIONAL PREDICTION
**Result: SOUND**

**What it claims:** For any confining SU(N), spacetime dimension D = N + 1.

**Retrodiction vs prediction assessment:**
- **Retrodictive for our universe:** SU(3) → D = 4, which is known
- **Genuinely predictive in scope:** For hypothetical confining SU(N≠3), predicts D = N + 1
- **Strongest predictive claim in G1**

**Falsifiability:**
- Falsified if a confining SU(N) gauge theory were discovered/constructed with D ≠ N + 1
- Falsified if lattice studies of SU(4) in 5D showed no confinement or different dimensional scaling
- **Practical falsifiability: LOW** — requires either new physics beyond the Standard Model or sophisticated lattice simulations of higher-N theories in various dimensions

**Resolution verification (V3.9, commit f1356c04):** V3.9 Common Axiom Dependency note now explicitly acknowledges that this result shares the geometric realization axiom (F1) with Lem 0.0.2a, Prop 0.0.40, and Thm 0.0.6. These are "valid consequences of a single common axiom, not convergent evidence from independent sources." P5 (Dimension Exhaustiveness) declared as explicit framework axiom in §3. §9 self-critique lists three potential challenges. This exemplary self-assessment converts the dimension exhaustiveness gap from SMUGGLED to QUALIFIED.

**Why SOUND:** The document honestly presents SU(3) → D = 4 as a retrodiction while noting the formula's broader predictive scope. The conditional nature (applies only to confining SU(N) in the geometric realization framework) is stated. P5 now explicitly declared. V3.9 note prevents false independence claims.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md`

---

### V7.5 — Lem 0.0.2a: Confinement Dimension Constraint

**Empirical category:** FRAMEWORK-INTERNAL
**Result: SOUND**

**What it claims:** For SU(N) geometric realization, D_space ≥ N − 1.

**Falsifiability:** Framework-internal mathematical bound. Not independently testable — it constrains the framework's own definitions (Weyl group faithful action on geometric realization). Cannot be falsified by experiment, only by finding a mathematical error. The document correctly scopes this at §5.2 with a clear list of what is NOT claimed.

**Resolution verification (V3.9, commit f1356c04):** V3.9 Common Axiom Dependency note added, correctly documenting shared dependence on F1. No impact on verdict.

**Evidence:** `docs/proofs/foundations/Lemma-0.0.2a-Confinement-Dimension.md`

---

### V7.6 — Prop 0.0.40: Embedding Dimension From Confinement

**Empirical category:** CONDITIONAL PREDICTION
**Result: QUALIFIED**

**What it claims:** d_embed = rank(G) + 1 for confining SU(N). For SU(3): d_embed = 3.

**Retrodiction vs prediction assessment:**
- **Retrodictive:** d_embed = 3 (spatial dimensions) is already known
- **Novel:** Upgrades Physical Hypothesis 0.0.0f from assumed to derived (now "reduced" per V3.6 fix)
- **Conditional prediction:** For other confining SU(N), predicts d_embed = N

**Falsifiability:**
- **Challenge from 2+1D SU(3):** Lattice QCD shows SU(3) confines in 2+1 dimensions. §8.5 carefully scopes this as applying to "geometric realization" (not lattice formulation), with an explicit true/false table distinguishing what the proposition does and does not claim. This is the best epistemic disclosure in any G1 file.
- **Step C4 (lines 165–172):** "We invoke the geometric realization principle that each independent coupling constant contributes **at most one** embedding dimension beyond weight space. This is **not derived from established physics — it is an irreducible axiom** of the geometric realization framework." This epistemic honesty is exemplary.
- **Practical falsifiability: LOW**

**Resolution verification (V3.6, commit f27e5452; V3.9, commit f1356c04):** V3.6 reframed from "derives" to "reduces" 0.0.0f. V3.9 notes common axiom dependency. Both strengthen epistemic transparency. The fundamental issue — scope restriction reduces empirical force — persists.

**Why QUALIFIED:** The 2+1D lattice QCD tension is acknowledged (§8.5) but the resolution via scope restriction reduces the claim's empirical content. A prediction that only applies within its own framework's definitions is less falsifiable than one with framework-independent consequences.

**Evidence:** `docs/proofs/foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md` §8.5, §5 Step C4

---

### V7.7 — Thm 0.0.0a: Polyhedral Necessity

**Empirical category:** FRAMEWORK-INTERNAL
**Result: SOUND**

**What it claims:** Pre-geometric substrates for emergent spacetime must be polyhedral (continuous manifolds presuppose what they seek to explain).

**Resolution verification (V4.2, commit e92a29f4):** Three previously smuggled findings now addressed:
- S8 (philosophical emergence): Methodological note acknowledging non-circular emergence is a design choice, not universal requirement
- S9 (unfair lattice comparison): Lattice comparison reframed as "difference of degree rather than kind"
- S28 (overstated title): Title qualified as "Polyhedral Necessity for Emergent Spacetime"; §5.2 explicitly lists what is NOT claimed

V4.2 further narrowed scope to "pre-geometric emergence" specifically, distinguishing from general gauge theory formulation. This is appropriately calibrated.

**Minor presentation risk:** The status header "NECESSITY THEOREM" is stronger than the body text, which qualifies it as "necessity among known frameworks." A reader of only the header could overinterpret this. Not severe enough to downgrade.

**Falsifiability:** This is a metamathematical argument about framework structure. Not empirically falsifiable. Could be challenged by constructing a non-polyhedral, non-manifold pre-geometric substrate that produces emergent spacetime — but this is a theoretical challenge, not experimental.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.0a-Polyhedral-Necessity.md` — §5.2 What We Do NOT Claim

---

### V7.8 — Prop 0.0.XX: SU(3) From Distinguishability

**Empirical category:** RETRODICTION (explicitly presented as such)
**Result: ~~QUALIFIED~~ → SOUND** (V4.14 resolution verified — commit a96a4b46)

**What it claims:** SU(3) is uniquely selected by information-theoretic distinguishability + D = 4.

**Retrodiction vs prediction assessment:**
- **Retrodictive:** SU(3) is the known QCD gauge group since ~1973
- **Explicitly labeled as retrodiction** throughout the document (post-V4.14)
- **Critical dependency:** The lower bound N ≥ 3 depends on Assumption A-IF (quantum interference form of probability), which is framework-specific input, not derived

**Resolution verification (V4.14, commit a96a4b46):**
- **Status line (line 3):** Now reads "🔶 NOVEL — SU(3) RETRODICTION FROM DISTINGUISHABILITY + QUANTUM INTERFERENCE (A-IF) + COLOR NEUTRALITY" — the word "RETRODICTION" is explicitly present in the status line, resolving the prior round's residual framing concern
- **Lines 6–8:** "Important Limitation" box: explicitly states A-IF dependency for N ≥ 3 lower bound and that this is "a novel *explanation* of a known fact, not a prediction"
- **Line 62:** Epistemic status paragraph: "This is a **retrodiction** — a novel explanatory pathway to a known result (SU(3) as the color gauge group). The conclusion is not falsifiable via this route."
- **Lines 627–628:** Honest input count: "4 framework-specific assumptions (A-IF, color neutrality, A-CS, A-SN)"

**This file has the best epistemic labeling in the entire G1 set.** Every overclaiming concern from rounds 1–3 has been addressed. The explicit use of "retrodiction" in the status line (not just body text) is the key improvement in this round.

**Falsifiability:**
- Falsified if A-IF fails — but A-IF is a postulate, so this is circular
- Falsified if another gauge group were fundamental — but we already know SU(3) is correct
- **Practical falsifiability: NONE** — the claim reconstructs known physics using a framework-specific axiom

**Why SOUND (upgraded from QUALIFIED):** The status line now explicitly includes "RETRODICTION," resolving the prior round's residual issue where the status line suggested derivation. Combined with the "Important Limitation" box, epistemic status paragraph, and honest input count, this file provides a complete and honest assessment of its empirical character. No residual overclaiming.

**Evidence:** `docs/proofs/foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md` — status line (line 3), lines 6–8, 62, 627–628

---

### V7.9 — Thm 0.0.3: Stella Uniqueness

**Empirical category:** FRAMEWORK-INTERNAL (uniqueness proof)
**Result: SOUND**

**What it claims:** The stella octangula is the unique minimal polyhedral realization of SU(3) satisfying GR1–GR3.

**Falsifiability:** Mathematical uniqueness proof within the framework. Falsified only by finding another polyhedron satisfying GR1–GR3 with ≤ 8 vertices — a mathematical question, not experimental. The exhaustive enumeration makes this robust.

**Resolution verification (V4.15, commit 551830a6):** V4.15 Scope Note (§0.3) now states that uniqueness is conditional on the GR1–GR3 + MIN1–MIN3 axiom package, and that "alternative axiom sets could select different objects." §2.3 "Important Clarification" box explicitly states conditionality on Physical Hypothesis 0.0.0f. Both correctly calibrate the scope.

**Indirect empirical contact:** If the stella geometry leads to incorrect downstream predictions, the uniqueness claim would survive but the framework's relevance would not.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.3-Stella-Uniqueness.md`

---

### V7.10 — Thm 0.0.3b: Geometric Realization Completeness

**Empirical category:** FRAMEWORK-INTERNAL
**Result: SOUND**

**What it claims:** Stella uniqueness extends beyond standard polyhedra to all topological spaces satisfying GR1–GR3.

**Falsifiability:** Mathematical classification result. No empirical content. Strengthens Theorem 0.0.3 but adds no new physics.

**Resolution verification (V4.15, commit 551830a6):** V4.15 Scope Note in §1 Statement now explicitly conditions the completeness result on the axiom package. §9.3 derivation chain diagram reads "Complex observers can exist → D=4 → SU(3) → Stella" — this implies a top-down derivation of known physics. While each arrow is labeled with a theorem number, the visual impression could mislead readers into treating this chain as genuinely predictive rather than reconstructive. Body text partially addresses this.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md`

---

### V7.11 — Prop 0.0.16a: A₃ From Physical Requirements

**Empirical category:** RETRODICTION
**Result: QUALIFIED**

**What it claims:** Among all rank-3 root lattices, A₃ (FCC) is uniquely forced by confinement + stella uniqueness + space-filling + phase coherence.

**Retrodiction vs prediction assessment:**
- **Retrodictive:** FCC lattice structure has been known since the 19th century
- **Novel:** The derivation that A₃ is *forced* (not chosen) is new
- **No new predictions:** The FCC lattice itself is ancient knowledge being re-derived
- **Simply-laced requirement:** The elimination of C₃ via "anisotropic coupling incompatible with uniform SU(3) phase coherence" is physically motivated but uses the empirical fact of a single QCD string tension without explicit citation

**Falsifiability:**
- Falsified if B₃ or C₃ could support stella-like structures — ruled out by root length uniformity argument
- **Practical falsifiability: NONE** — the FCC lattice is already known to be correct

**Why QUALIFIED:** The derivation is rigorous and novel, but framing it as "forced" and "uniquely determined" can mislead readers into thinking a prediction is being made. It is explaining why an already-known structure appears, not predicting a new one.

**Evidence:** `docs/proofs/foundations/Proposition-0.0.16a-A3-From-Physical-Requirements.md`

---

### V7.12 — Thm 0.0.16: Adjacency From SU(3)

**Empirical category:** RETRODICTION
**Result: QUALIFIED**

**What it claims:** FCC lattice properties (12-regularity, O_h symmetry, no intra-rep triangles) emerge from SU(3) representation theory.

**Retrodiction assessment:** All properties are well-known. The novel contribution is the *motivation* from gauge theory, not the properties themselves.

**Language discrepancy (persists — severity MODERATE):** §0 executive summary correctly uses "consistent with and motivated by" language. However, the peer review note (line 5) says "A0 is now FULLY DERIVED" and §7.2 table / §8 summary box repeat this — a significantly stronger claim than consistency. Showing that SU(3) representation theory is *consistent with* the FCC adjacency structure is not the same as *deriving* FCC from SU(3). The FCC lattice has 12 nearest neighbors for reasons of Euclidean geometry, not because SU(3) forces 12 neighbors. The 6+6 decomposition into intra/inter-representation edges is a post-hoc interpretation, not a unique prediction.

**Falsifiability:** Falsified if **3**⊗**3** contained a singlet — but this contradicts established representation theory. Not experimentally falsifiable.

**Why QUALIFIED:** The inconsistency between §0 ("consistent with and motivated by") and the peer review note/§7.2/§8 ("FULLY DERIVED") is a significant language issue. The document's own executive summary uses the correct weaker language, but the machine-readable summary tables and peer review header overstate.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.16-Adjacency-From-SU3.md` — §0 vs line 5 / §7.2 / §8

---

### V7.13 — Thm 0.0.6: Spatial Extension From Octet Truss

**Empirical category:** RETRODICTION
**Result: QUALIFIED**

**What it claims:** The tetrahedral-octahedral honeycomb (octet truss) is the unique space-filling extension of stella units into 3D space, with FCC vertex positions and phase coherence.

**Retrodiction assessment:** The octet truss is a known mathematical structure (Fuller, 1950s). The novel claim is that phase coherence forces FCC over HCP stacking. The Z₃ stacking argument (FCC period-3 vs HCP period-2, with gcd(2,3) = 1 preventing Z₃ realization on ABAB stacking) is mathematically elegant and sound.

**Honest self-assessment:** §0.1–0.2 commendably acknowledges that "pre-geometric integer coordinates already encode spatial structure" is "partially misleading." Three physical hypotheses (PH-0.0.6a, PH-0.0.6b, PH-0.0.6c) are now explicitly declared as formerly smuggled assumptions.

**Resolution verification (V3.9, commit f1356c04):** V3.9 Common Axiom Dependency note explicitly documents shared dependence on F1 (geometric realization). Prevents false independence from Lem 0.0.2a, Prop 0.0.40, Thm 0.0.2b.

**Language issue:** Corollary 0.0.6.1 states "Extended spatial dimensions do not need to be postulated — they emerge" but the emergence is conditional on PH-0.0.6a–c, which are themselves hypotheses. The corollary should acknowledge this conditionality.

**Falsifiability:**
- Falsified if HCP stacking preserved phase coherence — but Lemma 0.0.6a rules this out via vertex-transitivity
- **Practical falsifiability: NONE** — the honeycomb structure is already known

**Why QUALIFIED:** The phase coherence requirement is a novel framework-specific contribution, but the conclusion (FCC tiling) is retrodictive. Corollary overstatement persists.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md`

---

### V7.14 — Prop 0.0.6b: Continuum Limit Procedure

**Empirical category:** CONDITIONAL PREDICTION (contains imported claim)
**Result: SMUGGLED**

**What it claims:** The discrete stella admits a well-defined continuum limit with lattice spacing a ≈ 2.25 ℓ_P and lattice-breaking corrections suppressed by (a/L)^n.

**Prediction assessment:**
- **Genuine prediction:** Lattice spacing a ≈ 2.25 ℓ_P
- **Genuine prediction:** Z₃ center survives all limits as algebraic invariant
- **Genuine prediction:** Lattice artifacts suppressed by ~10⁻²⁰ at nuclear scales

**Falsifiability:**
- Falsified if Planck-scale lattice artifacts were detected in QCD observables — but this requires ~10²⁰× better experimental precision than currently available
- Current astrophysical bounds on Lorentz violation from gamma-ray burst photon arrival times are at ~10⁻²³ level — already more stringent than the (a/L)² ≈ 10⁻⁴⁰ suppression claimed in §2.3
- Falsified if Z₃ were lost in a continuum limit — mathematical, not experimental
- **Practical falsifiability: ESSENTIALLY NONE** — predictions are at the Planck scale

**Why SMUGGLED (two issues):**

1. **Imported lattice spacing:** The lattice spacing prediction (a ≈ 2.25 ℓ_P) is attributed to Proposition 0.0.17r, which is **not in G1**. This imported numerical prediction is presented within G1's continuum limit discussion without clearly flagging that it depends on a separate derivation chain (holographic self-consistency). A reader of G1 alone would not know this prediction's provenance or assumptions.

2. **θ = 0 as framework derivation:** §4.4 "Theorem 4.4.1 (Energy Divergence Selects θ = 0)" presents the strong-CP resolution as if it were a novel framework result. In reality, the argument that θ = 0 minimizes the vacuum energy in the thermodynamic limit given positive topological susceptibility (χ_top > 0) is a restatement of Coleman (1985). The premise χ_top > 0 is an empirical input from lattice QCD, used without explicit (E) classification at the point of invocation. What is novel is the connection to Z₃ superselection, but the core mechanism is standard QFT applied in a new context. Labeling this as "Theorem 4.4.1" with the framework's own numbering system could mislead readers about the provenance.

**Evidence:** `docs/proofs/foundations/Proposition-0.0.6b-Continuum-Limit-Procedure.md` — §2.2 references Prop 0.0.17r; §4.4 Coleman (1985) restatement

---

### V7.15 — Thm 0.0.9: Framework-Internal D=4 Consistency Check

**Empirical category:** FRAMEWORK-INTERNAL (self-consistency)
**Result: QUALIFIED**

**What it claims:** GR1–GR3 imply GR + QM, which in turn selects D = 4 via Theorem 0.0.1, closing the consistency loop.

**Resolution verification (positive):** The title was revised to "Framework-Internal D=4 Consistency Check" (noted in footer: "V6.7 comprehensive language update from 'derivation' to 'consistency check'"). §7.2 correctly presents the loop as "a self-consistency check."

**Overstated empirical contact:** §5.3 claims "The framework reproduces all weak-field GR phenomenology, including: ... gravitational waves with 2 polarizations (confirmed by LIGO)." However, the document shows the *structure* of the spin-2 propagator via Weinberg's theorem (1964), not a full calculation of perihelion precession, light bending, or Shapiro delay. The LIGO mention is a rhetorical flourish — gravitational wave polarization count follows from any massless spin-2 field, not uniquely from this framework. Stating that the framework "reproduces all weak-field GR phenomenology" goes beyond what is actually demonstrated.

**Additional issue:** §6.2 table lists "Born rule: ✅ DERIVED" and "Schrödinger equation: ✅ DERIVED" — these claims reference Theorem 0.0.10, which is a dependent theorem not independently verified in this document. The status of these claims depends on the soundness of Thm 0.0.10.

**Falsifiability:** Not independently falsifiable. Verifies internal self-consistency. If the loop broke (GR1–GR3 did not imply the physics that selects D = 4), this would be an internal flaw, not an experimental falsification.

**Why QUALIFIED:** The title and consistency-check framing are appropriately calibrated after V6 remediation. However, §5.3's claim of reproducing "all weak-field GR phenomenology" overstates the document's actual content, creating an impression of greater empirical contact than warranted.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md` — §5.3 GR claims, §6.2 QM derivation table

---

### V7.16 — Thm 0.0.15: Topological Determination SU(3)

**Empirical category:** RETRODICTION
**Result: SOUND**

**What it claims:** Z₃ phase structure + rank ≤ 2 (from D = 4) uniquely determines SU(3) among all compact simple Lie groups.

**Retrodiction assessment:** SU(3) has been the known QCD gauge group since ~1973. This theorem explains *why* SU(3) within the framework, but does not predict a new observable.

**Falsifiability:**
- Falsified if Z(SU(2)) = Z₃ — contradicts established algebra (Z(SU(2)) = Z₂)
- Falsified if E₆ had rank ≤ 2 — contradicts established algebra (rank 6)
- **Practical falsifiability: NONE** — reconstructs known group theory + known gauge group

**Empirical anchor (indirect):** Predicts exactly 8 gluon degrees of freedom — established by deep inelastic scattering (NNPDF data). This is retrodictive, not predictive.

**Language quality:** The document uses "determination" not "derivation" in the title — a deliberate and appropriate choice. §3.3 V4-R5 physical justification for simplicity is correctly presented as motivation, not proof ("These arguments do not constitute a proof that the confining group must be simple"). The §3.4 rank constraint warning box explicitly states "This is not a general physics principle, but a specific feature of this framework."

**Why SOUND:** The document correctly frames this as a *determination* (explanation) of SU(3), not a prediction. The language is the most carefully calibrated of any retrodiction file in G1.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.15-Topological-Determination-SU3.md`

---

### V7.17 — Thm 0.0.12: Categorical Equivalence

**Empirical category:** FRAMEWORK-INTERNAL (pure mathematics)
**Result: SOUND**

**What it claims:** A₂-Dec (stella-type polyhedral realizations) ≃ W(A₂)-Mod (SU(3) Cartan data structures).

**Falsifiability:** Purely mathematical. No empirical content whatsoever. Cannot be falsified by experiment. §9.1 contains explicit scope caveats noting the equivalence operates only at the level of Cartan data.

**Minor language note:** The phrase "SU(3) IS the stella" (lines 5, 86, 322) is a mathematical tautology within the framework but could mislead readers into thinking this is a physical discovery. §9.1 partially corrects this.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.12-Categorical-Equivalence.md`

---

### V7.18 — Thm 0.0.13: Tannaka Reconstruction SU(3)

**Empirical category:** FRAMEWORK-INTERNAL (consistency check)
**Result: QUALIFIED**

**What it claims:** Full SU(3) is recoverable from stella data via Tannaka-Krein duality.

**Falsifiability:** §0 explicitly frames this as a "consistency result, not a derivation." The theorem confirms stella ↔ SU(3) compatibility but does not predict new physics.

**Language contradiction (confirmed):** §0 (lines 55–101) honestly presents the result as a consistency check with explicit tables showing what the theorem does and does not demonstrate. However, line 410 states "SU(3) gauge symmetry is not postulated but emerges from polyhedral geometry" — which directly contradicts §0's own framing. The theorem's §0 shows SU(3) is SELECTED (via D=4 → SU(3)) and then confirmed consistent; the language "not postulated but emerges" reverses the actual logical flow. Similarly, Corollary 0.0.13.1 uses "SU(3) gauge symmetry is fully reconstructible from the discrete polyhedral data" which overstates given the admitted circularity.

**Why QUALIFIED:** Despite the honest framing in §0, the theorem title "Tannaka Reconstruction SU(3)" and line 410 could suggest SU(3) is being *derived* from geometry alone. The consistency-check nature should be more prominent in the title/status line and the body-level overclaiming at line 410 should be reconciled with §0.

**Evidence:** `docs/proofs/foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md` — §0 says consistency check; line 410 says "emerges"

---

### V7.19 — Def 0.1.1: Stella Octangula Boundary Topology

**Empirical category:** ENABLING (enables downstream predictions)
**Result: SOUND**

**What it claims:** Defines ∂S as the disjoint union of two tetrahedral surfaces with specified topology (χ = 4, 8 vertices, 12 edges, 8 faces).

**Falsifiability:** Axiomatically defined topology. Not falsifiable as a definition. The regularization parameter ε is deferred to Proposition 0.0.17o (matched to lattice QCD flux tube data) — this is retrodictive parameter-fixing, not prediction.

**Parameter matching (noted):** R_stella = 0.44847 fm is identified by dimensional analysis using √σ = 440 MeV (FLAG 2024), and ε ≈ 0.50 is fixed by two methods both using lattice QCD inputs (Cea et al. 2012, 2014). These are matched parameters, not predictions.

**Evidence:** `docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md`

---

### V7.20 — Def 0.1.2: Three Color Fields & Relative Phases

**Empirical category:** ENABLING (encodes SU(3) structure for downstream use)
**Result: SOUND**

**What it claims:** Three complex scalar fields χ_R, χ_G, χ_B with phases {0, 2π/3, 4π/3} on ∂S.

**Falsifiability:** These phases encode Z₃ ⊂ SU(3), which is established physics. The definition recovers known QCD color structure, not predicts it. §0 justification status correctly notes: "these establish that the field structure is consistent with and implied by the framework's axioms, not that it is uniquely necessitated independent of those axioms."

**Evidence:** `docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md`

---

### V7.21 — Def 0.1.3: Pressure Functions

**Empirical category:** ENABLING (provides dynamics for downstream phases)
**Result: SOUND**

**What it claims:** Pressure functions P_c(x) with abstract properties (P1)–(P5) modulate field amplitudes. The specific 1/r² form is a modeling choice (Assumption A-PF).

**Falsifiability:** The abstract axioms (P1)–(P5) are framework definitions. The 1/r² form matches Cornell potential short-range behavior — this is retrodictive consistency, not prediction. Proposition 0.1.3a proves form-independence, so the specific form is replaceable without affecting downstream results.

**Evidence:** `docs/proofs/Phase0/Definition-0.1.3-Pressure-Functions.md`

---

### V7.22 — Prop 0.1.3a: Pressure Function Form-Independence

**Empirical category:** FRAMEWORK-INTERNAL (robustness proof)
**Result: SOUND**

**What it claims:** All downstream G1 predictions are independent of pressure function realization choice.

**Falsifiability:** Not empirically falsifiable. Establishes structural robustness — the theory doesn't depend on an arbitrary modeling choice. This is a mathematical meta-result about the framework, not a physical claim. Lean 4 formalization (0 sorry) and Python verification (7/7 tests) provide mathematical confidence.

**Minor note:** The proposition statement says "identical physics" which should more precisely be "qualitatively identical physics" — §4.6 acknowledges Gaussian vs. power-law tails could affect "transverse flux tube profiles at large distances."

**Evidence:** `docs/proofs/Phase0/Proposition-0.1.3a-Pressure-Function-Form-Independence.md`

---

### V7.23 — Def 0.1.4: Color Field Domains

**Empirical category:** RETRODICTION
**Result: SOUND**

**What it claims:** Voronoi tessellation of color field domains on ∂S, with boundaries perpendicular to SU(3) root vectors.

**Falsifiability:** The boundary-root perpendicularity theorem (§8.2) recovers the standard SU(3) weight diagram structure. This is retrodictive: the SU(3) structure is already known. Depression ratios ≈ 4.0 match lattice QCD dual superconductor profiles (Baker et al. 2019) — also retrodictive. No direct empirical claims or predictions.

**Evidence:** `docs/proofs/Phase0/Definition-0.1.4-Color-Field-Domains.md`

---

### V7.24 — Thm 0.1.0: Field Existence From Distinguishability

**Empirical category:** FRAMEWORK-INTERNAL (axiom reduction)
**Result: QUALIFIED**

**What it claims:** Field existence follows from axiom A0' (information metric) + distinguishability, reducing the independent assumptions needed.

**Falsifiability:** Not empirically falsifiable. This is a logical simplification of the framework's axiom set. Falsified only if the derivation contains a mathematical error.

**Why QUALIFIED:** The theorem's value is axiomatic economy, not empirical contact. But the V6 audit found residual "DERIVED" language (lines 81, 83, 593–609) that overstates the empirical significance of what is actually an internal axiom-reduction result. The acknowledged Chentsov presupposition (§9.1) means this is a conditional derivation, not an unconditional one.

**Evidence:** `docs/proofs/Phase0/Theorem-0.1.0-Field-Existence-From-Distinguishability.md`

---

### V7.25 — Thm 1.1.1: SU(3) ↔ Stella Octangula

**Empirical category:** ENABLING (bridge theorem)
**Result: SOUND**

**What it claims:** Bijection between stella octangula vertices and SU(3) weights; complete SU(3) Lie algebra structure recovered from geometric properties.

**Falsifiability:** Mathematical isomorphism. Not empirically falsifiable — this is the framework's central bridge between geometry and gauge theory. Its empirical relevance is entirely through downstream predictions.

**Note:** The distances in (T₃, Y) Euclidean coordinates show the weight triangle is isosceles (RG=1, GB=BR≈1.118), NOT equilateral — the document correctly addresses this via the Killing form metric distinction (§1.6). No overstatement of empirical content.

**Why SOUND:** The document correctly presents this as an enabling structural result, not a prediction.

**Evidence:** `docs/proofs/Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md`

---

### V7.26 — Def 1.1.4: Stella Diagram Rules

**Empirical category:** FRAMEWORK-INTERNAL (formalism)
**Result: SOUND**

**What it claims:** Diagrammatic calculus for color interactions on the stella octangula. Nine rules encoding kinematic and dynamical constraints.

**Falsifiability:** Notational convention encoding standard SU(3) representation theory. No empirical content beyond known QCD. Rule 3 (chirality R→G→B preferred orientation) is marked provisional — requires Phase 2 justification (Thm 2.2.4, ⟨Q⟩ > 0). Rule 5 (closure/confinement) explicitly distinguishes kinematic from dynamical confinement (lines 176–177).

**Note:** §8 honestly acknowledges the formalism is currently qualitative: "Can stella diagrams be extended to compute scattering amplitudes?" is listed as an open question. This is appropriate epistemic calibration — the rules classify states, they do not yet make quantitative predictions.

**Evidence:** `docs/proofs/Phase1/Definition-1.1.4-Stella-Diagram-Rules.md`

---

## Part II: Cross-File Synthesis

### The Prediction-Retrodiction Boundary in G1

G1 reconstructs the following known facts:

| Known Fact | Reconstructed In | Method |
|------------|-----------------|--------|
| D = 4 spacetime dimensions | Thm 0.0.1 | Anthropic selection argument |
| Euclidean geometry | Thm 0.0.2 | Killing form on SU(3) weight space |
| SU(3) as QCD gauge group | Thms 0.0.15, Prop 0.0.XX | Z₃ + rank constraint; info-theoretic |
| FCC lattice structure | Thm 0.0.6, Prop 0.0.16a, Thm 0.0.16 | Phase coherence + stella extension |
| 3 spatial dimensions | Prop 0.0.40, Thm 0.0.2b | Confinement + rank |
| Z₃ center symmetry | Thm 0.0.15 | Stella geometry |
| Stella octangula geometry | Thm 0.0.3, 0.0.3b | Uniqueness under GR1–GR3 |
| SU(3) weight diagram | Def 0.1.4, Thm 1.1.1 | Vertex ↔ weight bijection |

**Every empirical fact cited in G1 was already known before the framework was constructed.** G1's contribution is explanatory: it provides a unified geometric origin for these facts. This is scientifically valuable — unification is how physics progresses — but it is retrodiction, not prediction.

### The Independence Inflation Problem (V3.9 — Fourth Round Key Finding)

The four dimensionality proofs share a common load-bearing axiom:

| Proof | What It "Derives" | Common Axiom | Unique Addition |
|-------|-------------------|--------------|-----------------|
| Thm 0.0.2b | D = N+1 | F1 (geometric realization) | P5 (dimension exhaustiveness) |
| Lem 0.0.2a | D_space ≥ N−1 | F1 (geometric realization) | Affine independence |
| Prop 0.0.40 | d_embed = rank+1 | F1 (geometric realization) | Step C4 (coupling→dimension) |
| Thm 0.0.6 | ℝ³ from octet truss | F1 (geometric realization) | PH-0.0.6a–c (space-filling) |

**Prior to V3.9 resolution:** These four results could appear as "multiple independent confirmations" of D = 3.

**After V3.9 resolution:** Each file now contains a Common Axiom Dependency note explicitly stating they are "valid consequences of a single common axiom, **not** convergent evidence from independent sources." If F1 fails, all four collapse simultaneously.

**Impact on falsifiability:** The effective number of independent dimensional constraints is **one** (F1), not four. This dramatically reduces the apparent robustness of the D = 3 / D = 4 derivation within G1. The single point of failure (F1) makes the framework more vulnerable but also more honest about its structure.

### G1's Genuine Predictive Content

Only two claims in G1 approach genuine predictions (not reconstructions of known physics):

| Prediction | Source | Testability | Status |
|------------|--------|-------------|--------|
| D = N+1 for any confining SU(N) | Thm 0.0.2b | Requires hypothetical new physics or lattice simulation | Practically untestable |
| Lattice spacing a ≈ 2.25 ℓ_P | Prop 0.0.6b (importing Prop 0.0.17r) | Requires ~10²⁰× better precision | Practically untestable |
| Z₃ survives continuum limit | Prop 0.0.6b | Mathematical, not experimental | Not empirically testable |
| Lattice artifacts suppressed by 10⁻²⁰ at nuclear scales | Prop 0.0.6b | Would require detecting absence of an unobservably small effect | Practically untestable |

Both genuine predictions are **practically unfalsifiable** with current or near-future technology.

### What Would Falsify G1 As a Whole?

Since G1 makes no direct predictions, it can only be falsified **indirectly** through the downstream derivation chain:

```
G1 (Geometric Foundation)
  ↓ enables
R_stella = 0.44847 fm (OBSERVED INPUT — not predicted by G1)
  ↓ via Prop 0.0.17j
√σ = 440 MeV
  ↓ via Prop 0.0.17k
f_π = 88.0 MeV (95.6% of PDG 92.1 MeV)
  ↓ via Prop 0.0.17n
12 fermion masses
  ↓ via Phase 8
Heavy-ion, cosmological, dark matter predictions
```

**Critical observation:** G1 does not predict R_stella. It provides the *framework* within which R_stella is interpreted, but R_stella = 0.44847 fm is an *observed input* (from FLAG 2024: √σ = 440 ± 30 MeV). The framework's predictive power comes from:

1. **Structural predictions (ratios and scaling laws):** f_π/√σ = 1/5 is a genuine prediction of the framework's *structure*, not an input. If this ratio were wrong, G1's interpretation of field dynamics would be implicated.

2. **Mass relations:** The 12 fermion masses are derived from R_stella + framework structure. If systematic deviations appeared, G1's geometric encoding would be challenged.

3. **Phase 8 novel predictions:** QGP coherence length, HBT tails, gravitational wave signals, proton decay lifetime — these are genuinely predictive and would falsify the framework if wrong.

**The honest assessment:** G1 itself is unfalsifiable by experiment. It becomes falsifiable only when combined with downstream propositions that convert geometric structures into numerical predictions.

### The Isolation Problem

If downstream predictions fail, it is difficult to determine whether G1 or the Phase 2–8 derivations are at fault. The modularity of the proof chain means G1's empirical status is always derivative. This is not necessarily a flaw — foundational axiom systems in physics (e.g., the axioms of QFT) are also only testable through their consequences — but it should be acknowledged.

### The Overfitting Risk

A framework that takes one input (R_stella) and produces many outputs is impressive *if* the outputs are correct. But G1's role in this chain is to provide *structural constraints* (SU(3) geometry, stella topology, phase coherence), which are not themselves testable. The testable content lives in Phases 2–8, not G1. If the structural constraints are chosen to reproduce known physics (retrodiction), then the downstream "predictions" are partially contaminated by the choices made at the foundational level.

### The Derivation Chain Impression Problem

Multiple files contain derivation chain diagrams (Thm 0.0.2b §8, Thm 0.0.3b §9.3) that present the path "Observers exist → D=4 → SU(3) → Stella → FCC" as a clean deductive chain with arrows labeled by theorem numbers. The visual impression is of genuine top-down prediction. In reality, each step is conditional on framework-specific hypotheses (P1–P5, A-CS, GR1–GR3, PH-0.0.6a–c) and each conclusion was already known before the framework was constructed. The diagrams do not indicate which arrows represent retrodictions vs. predictions, potentially misleading readers about the framework's predictive reach. The body text at various points acknowledges this, but the diagrams themselves do not.

---

## Part III: Falsification Catalog

### Experimental Results That Would Falsify G1's Framework

| Experimental Finding | What It Falsifies | Severity | Practical Likelihood |
|---------------------|-------------------|----------|---------------------|
| Stable atoms in D ≠ 4 | Thm 0.0.1 | CRITICAL | Impossible (no access to D ≠ 4) |
| SU(3) not the QCD gauge group | Entire framework | CRITICAL | Contradicts 50 years of QCD |
| Non-Euclidean geometry at Planck scale | Thm 0.0.2 | MAJOR | Not testable currently |
| Lattice artifacts at >>ℓ_P scales | Prop 0.0.6b | MAJOR | Not testable currently |
| f_π/√σ ≠ 1/5 at high precision | Framework structure (via Props) | MAJOR | Already ~4.5% deviation |
| Systematic fermion mass failures | Framework structure (via Props) | MAJOR | Currently passing |
| Novel confining SU(N) with D ≠ N+1 | Thm 0.0.2b | MAJOR | Requires new physics |
| QGP coherence ≠ R_stella | Phase 8 (not G1 directly) | MODERATE | Testable at ALICE/STAR |
| Second independent QCD confinement scale | Thm 0.0.2b P1 | MAJOR | Collider/lattice measurement |
| Neutron EDM inconsistent with θ ≈ 0 | Prop 0.0.6b §4.4 | MODERATE | n2EDM targeting ~10⁻²⁷ e·cm |

**Key finding:** No experimental result would *uniquely* falsify G1 without also falsifying the broader framework. G1 is insulated from direct experimental test by its foundational position in the derivation chain.

### Theoretical Results That Would Undermine G1

| Theoretical Development | What It Undermines | Severity |
|------------------------|-------------------|----------|
| Non-polyhedral pre-geometric emergence | Thm 0.0.0a, Def 0.0.0 | CRITICAL |
| Alternative polyhedron satisfying GR1–GR3 | Thm 0.0.3 uniqueness | CRITICAL |
| Non-SU(3) gauge group producing confinement + D=4 | Thm 0.0.15, Prop 0.0.XX | MAJOR |
| Continuum formulation of color confinement without lattice | Thm 0.0.6, Prop 0.0.6b | MODERATE |
| A-IF assumption shown to also select SU(2) | Prop 0.0.XX lower bound | MAJOR |
| Large-N limit tension with AdS/CFT (d_embed → ∞ vs fixed AdS₅) | Prop 0.0.40 §8.3 | MODERATE |

---

## Part IV: Honest Assessment

### Strengths

1. **Retrodictive coherence:** G1 successfully explains 8+ known physical facts from a small axiom set (Def 0.0.0 + Thm 0.0.1). This unification has genuine scientific value.

2. **Internal consistency:** The V1–V6 audits found no INVALID results. The mathematics is correct throughout.

3. **Transparency (substantially improved across four audit rounds):** Most proofs correctly identify their logical character. V7.8 (Prop 0.0.XX) is the gold standard — explicit retrodiction labeling with detailed input accounting and "RETRODICTION" in the status line. Resolution commits (551830a6, a96a4b46, e92a29f4, f1356c04, f27e5452) have addressed V3.6, V3.9, V4.2, V4.14, and V4.15 findings. Prop 0.0.40 §8.5 provides the best epistemic disclosure table in any G1 file. V3.9 common axiom dependency notes prevent false independence inflation across four dimensionality proofs.

4. **Enabling role:** G1 enables the genuinely predictive downstream propositions (Phase 2–8), which is its primary scientific function.

5. **Framework robustness:** Prop 0.1.3a proves form-independence of pressure functions, showing the framework is not fine-tuned to a specific modeling choice.

### Weaknesses

1. **Zero direct predictions:** G1 makes no directly testable prediction of a currently unmeasured observable.

2. **Retrodictions with derivation language (partially resolved):** Prop 0.0.XX has been fully resolved (SOUND). However, Thm 0.0.16 line 5 / §7.2 / §8 still say "FULLY DERIVED" (contradicting its own §0), Thm 0.0.13 line 410 says "emerges" (contradicting its own §0), and Thm 0.0.9 §5.3 claims to "reproduce all weak-field GR phenomenology" beyond what is actually shown.

3. **Practically unfalsifiable predictions:** The two genuine predictions (D = N+1 for SU(N), lattice spacing ~ℓ_P) are beyond any foreseeable experimental reach.

4. **Framework-internal falsification only:** G1's claims can only be challenged by alternative mathematical frameworks, not by experimental data.

5. **One smuggled import:** Prop 0.0.6b imports a numerical prediction from Prop 0.0.17r and presents Coleman (1985) as a framework derivation.

6. **Isolation from falsification:** G1 cannot be independently falsified — only the full framework (G1 + downstream derivations) can be tested. If predictions fail, the failure cannot be localized to G1.

7. **Derivation chain diagrams:** Multiple files present clean deductive chains that do not distinguish prediction arrows from retrodiction arrows, creating an impression of greater predictive content than warranted.

### Recommendations

1. **For peer review:** Add a "Falsifiability and Empirical Status" section to G1's synthesis document, explicitly acknowledging that G1 is a retrodictive foundation whose predictions flow only through downstream propositions.

2. **For Prop 0.0.6b:** Clearly mark the lattice spacing value as imported from Prop 0.0.17r with full dependency chain. Reclassify §4.4 Theorem 4.4.1 as "Application of Coleman (1985) to Z₃ superselection" rather than an independent framework result.

3. **For Thm 0.0.16:** Reconcile §0 ("consistent with and motivated by") with line 5 peer review note / §7.2 / §8 ("FULLY DERIVED").

4. **For Thm 0.0.13:** Reconcile §0 (consistency check) with line 410 ("not postulated but emerges").

5. **For Thm 0.0.9:** Qualify §5.3 to reflect what is actually demonstrated (spin-2 propagator structure via Weinberg's theorem) rather than claiming reproduction of "all weak-field GR phenomenology."

6. **For derivation chain diagrams:** Add a legend distinguishing retrodiction arrows (→ known fact) from prediction arrows (→ novel claim) in all derivation chain diagrams.

7. **For the overall framework:** The strongest path to falsifiability runs through Phase 8 predictions (QGP coherence, gravitational waves, proton decay). G1's value is establishing the geometric foundation for those predictions, not making predictions itself.

---

## JSON Summary

```json
{
  "group": "G1",
  "layer": 2,
  "module": "V7",
  "checks_total": 26,
  "sound": 16,
  "qualified": 9,
  "weak": 0,
  "invalid": 0,
  "smuggled": 1,
  "findings": [
    {
      "check_id": "V7.1",
      "result": "SOUND",
      "description": "Def 0.0.0 — axiomatization correctly framed as framework choice; V4.15 Transparency Note makes axiom package's role as selection device explicit; F1 identified as load-bearing unfalsifiable premise",
      "evidence": "docs/proofs/foundations/Definition-0.0.0-Minimal-Geometric-Realization.md — V4.15 note §1.1",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.2",
      "result": "QUALIFIED",
      "description": "Thm 0.0.1 — retrodiction of D=4 framed as derivation; CDT results conflated with observational constraints; ESTABLISHED status bundles epistemically different argument types",
      "evidence": "docs/proofs/foundations/Theorem-0.0.1-D4-From-Observer-Existence.md — status marker bundles anthropic + dynamical arguments",
      "severity": "MINOR"
    },
    {
      "check_id": "V7.3",
      "result": "QUALIFIED",
      "description": "Thm 0.0.2 — retrodiction of Euclidean geometry; 3 instances of unqualified 'uniquely compatible' persist (lines 84, 451, 865)",
      "evidence": "docs/proofs/foundations/Theorem-0.0.2-Euclidean-From-SU3.md",
      "severity": "MINOR"
    },
    {
      "check_id": "V7.4",
      "result": "SOUND",
      "description": "Thm 0.0.2b — strongest predictive claim in G1; D=N+1 honestly presented as retrodictive for SU(3) but predictive in scope; P5 now explicit; V3.9 common axiom note prevents false independence claims; §9 self-critique exemplary",
      "evidence": "docs/proofs/foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md — V3.9 note",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.5",
      "result": "SOUND",
      "description": "Lem 0.0.2a — framework-internal bound; no empirical claims made; §5.2 scope correctly stated; V3.9 common axiom note added",
      "evidence": "docs/proofs/foundations/Lemma-0.0.2a-Confinement-Dimension.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.6",
      "result": "QUALIFIED",
      "description": "Prop 0.0.40 — d_embed=3 is retrodictive; 2+1D lattice QCD tension resolved via scope restriction; V3.6 reframes as 'reduction' not 'derivation'; V3.9 common axiom note; Step C4 epistemic note exemplary but scope restriction reduces empirical force",
      "evidence": "docs/proofs/foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md §8.5, §5 Step C4",
      "severity": "MODERATE"
    },
    {
      "check_id": "V7.7",
      "result": "SOUND",
      "description": "Thm 0.0.0a — metamathematical necessity argument; S8/S9/S28 resolved; V4.2 narrows scope to pre-geometric emergence; §5.2 lists what is NOT claimed",
      "evidence": "docs/proofs/foundations/Theorem-0.0.0a-Polyhedral-Necessity.md — §5.2, V4.2 scope clarification",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.8",
      "result": "SOUND",
      "description": "Prop 0.0.XX — SU(3) retrodiction now FULLY resolved: status line reads 'RETRODICTION' (commit a96a4b46/V4.14); A-IF dependency prominent in Important Limitation box; epistemic status paragraph at line 62; best epistemic labeling in G1",
      "evidence": "docs/proofs/foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md — status line (line 3), lines 6-8, 62, 627-628",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.9",
      "result": "SOUND",
      "description": "Thm 0.0.3 — uniqueness proof; framework-internal; correctly framed; V4.15 scope note conditions uniqueness on axiom package; §2.3 conditionality on 0.0.0f acknowledged",
      "evidence": "docs/proofs/foundations/Theorem-0.0.3-Stella-Uniqueness.md — V4.15 scope note §0.3",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.10",
      "result": "SOUND",
      "description": "Thm 0.0.3b — mathematical classification; no empirical content; V4.15 scope note in §1; §9.3 derivation chain diagram noted as presentation risk",
      "evidence": "docs/proofs/foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.11",
      "result": "QUALIFIED",
      "description": "Prop 0.0.16a — FCC retrodiction framed with 'forced/uniquely determined' language; novel derivation but known conclusion; simply-laced requirement uses implicit empirical input",
      "evidence": "docs/proofs/foundations/Proposition-0.0.16a-A3-From-Physical-Requirements.md",
      "severity": "MINOR"
    },
    {
      "check_id": "V7.12",
      "result": "QUALIFIED",
      "description": "Thm 0.0.16 — §0 correctly says 'consistent with'; line 5 peer review note and §7.2/§8 say 'FULLY DERIVED' — internal language contradiction overstates empirical status of retrodiction",
      "evidence": "docs/proofs/foundations/Theorem-0.0.16-Adjacency-From-SU3.md — §0 vs line 5/§7.2/§8",
      "severity": "MODERATE"
    },
    {
      "check_id": "V7.13",
      "result": "QUALIFIED",
      "description": "Thm 0.0.6 — octet truss retrodiction; phase coherence novel but conclusion known; V3.9 common axiom dependency note; Corollary 0.0.6.1 overstates emergence given PH-0.0.6a-c conditionality",
      "evidence": "docs/proofs/foundations/Theorem-0.0.6-Spatial-Extension-From-Octet-Truss.md — V3.9 note",
      "severity": "MINOR"
    },
    {
      "check_id": "V7.14",
      "result": "SMUGGLED",
      "description": "Prop 0.0.6b — lattice spacing a~2.25 l_P imported from Prop 0.0.17r (outside G1) without clear provenance; §4.4 θ=0 is Coleman (1985) restatement presented as framework derivation; χ_top>0 empirical input not classified",
      "evidence": "docs/proofs/foundations/Proposition-0.0.6b-Continuum-Limit-Procedure.md — §2.2 Prop 0.0.17r import, §4.4 Coleman restatement",
      "severity": "MODERATE"
    },
    {
      "check_id": "V7.15",
      "result": "QUALIFIED",
      "description": "Thm 0.0.9 — consistency check correctly framed (V6.7 revision); but §5.3 claims 'reproduces all weak-field GR phenomenology' beyond what is demonstrated (only spin-2 propagator structure shown); §6.2 QM derivation claims depend on unverified Thm 0.0.10",
      "evidence": "docs/proofs/foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md — §5.3 GR overclaim, §6.2 dependent claims",
      "severity": "MINOR"
    },
    {
      "check_id": "V7.16",
      "result": "SOUND",
      "description": "Thm 0.0.15 — SU(3) determination is retrodiction; correctly framed as explanation not prediction; 'determination' language deliberately chosen; §3.4 rank constraint scope correctly stated",
      "evidence": "docs/proofs/foundations/Theorem-0.0.15-Topological-Determination-SU3.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.17",
      "result": "SOUND",
      "description": "Thm 0.0.12 — pure mathematical classification; no empirical content; §9.1 scope caveats adequate",
      "evidence": "docs/proofs/foundations/Theorem-0.0.12-Categorical-Equivalence.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.18",
      "result": "QUALIFIED",
      "description": "Thm 0.0.13 — §0 honest consistency framing contradicted by line 410 'not postulated but emerges'; title 'Reconstruction' overstates; admitted circularity not reflected in corollaries",
      "evidence": "docs/proofs/foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md — §0 vs line 410",
      "severity": "MINOR"
    },
    {
      "check_id": "V7.19",
      "result": "SOUND",
      "description": "Def 0.1.1 — enabling definition; no empirical claims; R_stella and ε are matched parameters not predictions",
      "evidence": "docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.20",
      "result": "SOUND",
      "description": "Def 0.1.2 — encodes known SU(3) Z₃ structure; correctly framed as definition consistent with axioms; §0 justification status appropriately qualified",
      "evidence": "docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.21",
      "result": "SOUND",
      "description": "Def 0.1.3 — pressure function form declared as modeling choice (A-PF); abstract axioms load-bearing; honest framing; form-independence proven by Prop 0.1.3a",
      "evidence": "docs/proofs/Phase0/Definition-0.1.3-Pressure-Functions.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.22",
      "result": "SOUND",
      "description": "Prop 0.1.3a — form-independence proof; meta-result about framework robustness; correctly framed; Lean+Python verification",
      "evidence": "docs/proofs/Phase0/Proposition-0.1.3a-Pressure-Function-Form-Independence.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.23",
      "result": "SOUND",
      "description": "Def 0.1.4 — domain structure recovers known SU(3) weight diagram; correctly framed as geometric construction; no direct empirical claims",
      "evidence": "docs/proofs/Phase0/Definition-0.1.4-Color-Field-Domains.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.24",
      "result": "QUALIFIED",
      "description": "Thm 0.1.0 — axiom reduction with residual 'DERIVED' language overstating scope; Chentsov presupposition limits reach",
      "evidence": "docs/proofs/Phase0/Theorem-0.1.0-Field-Existence-From-Distinguishability.md — lines 81, 83, 593-609",
      "severity": "MINOR"
    },
    {
      "check_id": "V7.25",
      "result": "SOUND",
      "description": "Thm 1.1.1 — bridge theorem enabling downstream predictions; correctly framed as structural result; isosceles-vs-equilateral addressed via Killing form",
      "evidence": "docs/proofs/Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md",
      "severity": "NOTE"
    },
    {
      "check_id": "V7.26",
      "result": "SOUND",
      "description": "Def 1.1.4 — diagrammatic formalism; no empirical content; Rule 3 chirality marked provisional; §8 honestly lists open questions; kinematic/dynamic confinement distinction made",
      "evidence": "docs/proofs/Phase1/Definition-1.1.4-Stella-Diagram-Rules.md",
      "severity": "NOTE"
    }
  ],
  "overall_verdict": "G1 contains zero directly testable predictions of new observables. Its empirical contact is entirely indirect, mediated through downstream propositions (0.0.17j-n, Phase 8). Two conditional predictions exist (D=N+1 for confining SU(N); lattice spacing ~l_P) but both are practically unfalsifiable. The group's value is retrodictive: it unifies 8+ known physical facts from a small axiom set. One SMUGGLED import (Prop 0.0.6b: lattice spacing from Prop 0.0.17r + Coleman θ=0 restatement). V7.8 (Prop 0.0.XX) upgraded QUALIFIED→SOUND (V4.14 resolution fully addressed status line). V3.9 common axiom dependency notes prevent false independence inflation across four dimensionality proofs. No INVALID findings. 16/26 SOUND, 9/26 QUALIFIED, 0 WEAK, 1/26 SMUGGLED."
}
```
