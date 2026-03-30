# G1 Geometric Foundation — Coherence Audit: Module M2 Findings

> **Module:** M2 — Primary Derivation Paths — Multiple paths to key results agree
> **Group:** G1 — Geometric Foundation
> **Layer:** 1 (Coherence)
> **Posture:** DEFENSIVE — verify internal consistency
> **Auditor:** Claude Opus 4.6 (autonomous audit agent)
> **Date:** 2026-03-14 (line references re-verified 2026-03-14)
> **Template:** [G1-Geometric-Foundation-Coherence-Audit.md](G1-Geometric-Foundation-Coherence-Audit.md) § Module 2

---

## Scope

Module M2 verifies that the framework's **multiple independent derivation paths** to the same key results — principally SU(3) and D=4 — **actually agree** on the same mathematical object and are **honestly labeled** as to their logical status (derivation vs. selection vs. consistency check).

The critical risks are:
1. Two paths claiming to "derive" SU(3) by different methods but arriving at subtly different mathematical objects
2. A path claiming to "derive" SU(3) when it actually "selects" or "confirms" it (overstating logical status)
3. Circular reasoning: using SU(3) properties to derive SU(3)
4. Shared assumptions (particularly A-CS) not consistently declared across paths
5. The D=4 consistency loop (Thm 0.0.1 → SU(3) → stella → Thm 0.0.9 → D=4) presented as independent derivation rather than self-consistency check

---

## Files Examined

All 26 G1 proof files were available. The files most relevant to M2 are:

| # | File | Abbreviation | Role in M2 |
|---|------|--------------|------------|
| F02 | `foundations/Theorem-0.0.1-D4-From-Observer-Existence.md` | Thm 0.0.1 | External D=4 derivation (P1+P2) |
| F03 | `foundations/Theorem-0.0.2-Euclidean-From-SU3.md` | Thm 0.0.2 | SU(3) → ℝ³; contains §0 logical status clarification |
| F04 | `foundations/Theorem-0.0.2b-Dimension-Color-Correspondence.md` | Thm 0.0.2b | D = N+1 formula; dimensional path to SU(3) |
| F05 | `foundations/Lemma-0.0.2a-Confinement-Dimension.md` | Lem 0.0.2a | D_space ≥ N−1 bound; feeds rank constraint |
| F06 | `foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md` | Prop 0.0.40 | d_embed = N from confinement |
| F07 | `foundations/Proposition-0.0.XX-SU3-From-Distinguishability-Constraints.md` | Prop 0.0.XX | Information-geometric path to SU(3) |
| F08 | `foundations/Theorem-0.0.3-Stella-Uniqueness.md` | Thm 0.0.3 | Stella uniqueness given SU(3) |
| F09 | `foundations/Theorem-0.0.3b-Geometric-Realization-Completeness.md` | Thm 0.0.3b | Extends uniqueness to all topological spaces |
| F10 | `foundations/Theorem-0.0.15-Topological-Determination-SU3.md` | Thm 0.0.15 | Topological path to SU(3) |
| F11 | `foundations/Theorem-0.0.12-Categorical-Equivalence.md` | Thm 0.0.12 | Categorical equivalence SU(3) ↔ stella |
| F12 | `foundations/Theorem-0.0.13-Tannaka-Reconstruction-SU3.md` | Thm 0.0.13 | Tannaka reconstruction (consistency result) |
| F17 | `foundations/Theorem-0.0.9-Framework-Internal-D4-Consistency-Check.md` | Thm 0.0.9 | Internal D=4 consistency check |
| F25 | `Phase1/Theorem-1.1.1-SU3-Stella-Octangula.md` | Thm 1.1.1 | SU(3)–Stella bridge theorem |

---

## Detailed Findings

### M2.1: Dimensional Path D=4 → N=3 → SU(3) Is Explicit and Honest

**Result: PASS**

The dimensional path proceeds: Thm 0.0.1 derives D=4 from observer existence (P1: gravitational stability + P2: atomic stability are load-bearing); Thm 0.0.2b derives D = N+1 as a theorem with explicit hypotheses; the corollary solves N+1=4 → N=3 → SU(3).

| Step | File | Line | Content |
|------|------|------|---------|
| D=4 derived | F02 (Thm 0.0.1) | 23–52 | "P1 and P2 alone uniquely select D=4" |
| D=N+1 formula | F04 (Thm 0.0.2b) | 20–32, 303–304 | Three-term decomposition: (N−1) angular + 1 radial + 1 temporal |
| N=3 chain | F02 | 383 | Corollary 0.0.1a: D=4 implies N=3 |
| SU(3) selected | F02 | 385–388 | "We do NOT derive SU(3) from D=4 alone" (§4 Corollary logical status) |
| Scope limitation | F04 | 33–34, 358–394 | "Applies to confining SU(N). Non-confining groups (U(1), SU(2)) are outside its scope" |

The dimensional path is scrupulously honest: F02 §4 explicitly states SU(3) is SELECTED, not derived. F03 §0 devotes 60 lines (47–106) to clarifying logical status with explicit capitalized labels (DERIVED, OBSERVATION, SELECTED) and a table showing D=N+1 failures for U(1)/SU(2).

---

### M2.2: Topological Path (Thm 0.0.15) Derives SU(3) Without Circular SU(3) Input

**Result: PASS**

Thm 0.0.15 uses a constraint-intersection method over the Cartan classification:

| Constraint | Source | Line | Effect |
|------------|--------|------|--------|
| Z₃ center | Stella 3-fold rotational symmetry | 117–141 | Filters to groups with Z₃ ⊆ Z(G) |
| Rank ≤ 2 | D_space=3 via Lem 0.0.2a/Prop 0.0.40 | 283, 343 | Eliminates SU(6), SU(9), E₆ |
| Compact simple | Assumption A-CS | 52–60 | Excludes product groups, non-compact |

Z₃ is derived from stella geometry independently of SU(3) in a dedicated §3.0 ("Step 0: Z₃ from Stella Octangula Geometry (Independent of SU(3))"). Non-circularity is stated three times: lines 141, 348, 694.

The rank constraint chain is: Lem 0.0.2a (D_space ≥ N−1 from affine independence) → Prop 0.0.40 (d_embed = N from confinement) → in D_space=3, at most 4 affinely independent points → N ≤ 4 → combined with Z₃ → N=3 uniquely.

Elimination table (lines 358–368): SU(6) rank 5 ✗, E₆ rank 6 ✗, SU(3) rank 2 ✓ — only survivor.

---

### M2.3: Information-Geometric Path (Prop 0.0.XX) Is Independent and Non-Circular

**Result: PASS (2 NOTE)**

Prop 0.0.XX derives SU(3) via Fisher metric non-degeneracy without SU(3) in premises:

| Step | Method | Lines |
|------|--------|-------|
| N ≥ 3 | Fisher non-degeneracy (N=1 trivial, N=2 degenerate) | 136, 166, 209 |
| N ≤ 4 | Affine independence in D_space=3 | 330–334 |
| N = 3 | Color neutrality Σ e^{iφ_c} = 0 | 335 |
| SU(3) | Cartan classification: unique rank-2 group with Weyl S₃ | 423–433, 539–553 |

**NOTE 1:** The color neutrality condition `Σ_c e^{iφ_c} = 0` is physically motivated by confinement/equilibrium but could be scrutinized as implicitly QCD-flavored. File is transparent about this.

**NOTE 2:** §0.3 (line 95) honestly states: "This proposition does NOT reduce the input count. It provides an alternative derivation path that replaces geometric inputs (stella geometry) with information-theoretic inputs." This is exemplary honesty.

The file also includes an explicit circular reasoning warning at §2.3 (line 162): "Theorem 0.1.0 derives the interference form but takes SU(3) structure as input; using it here would be circular. Within this proposition, A-IF is an independent framework assumption."

---

### M2.4: Categorical/Tannaka Paths Are Correctly Framed as Consistency Checks

**Result: PASS**

| File | Framing | Key Evidence |
|------|---------|--------------|
| Thm 0.0.12 (F11) | Categorical equivalence | Line 5: "categorically equivalent." Never claims to derive SU(3). |
| Thm 0.0.13 (F12) | Consistency result | Status line 3: "(Consistency Result)". Bold banner lines 8–9. Full §0 (lines 40–102) "What This Theorem Does and Does Not Show." Table lines 76–81: "SU(3) derived purely from stella geometry → FALSE." |

The known B4 overstatement issue in F12 has been fully resolved. Corollary 0.0.13.2 now reads "reconstructible from... confirming consistency" instead of "emerges from geometry, not from postulation."

---

### M2.5: All Paths Yield the Same Mathematical Object — SU(3)

**Result: PASS**

Cross-path characterization comparison:

| Property | Thm 0.0.15 | Prop 0.0.XX | Thm 0.0.2b | Thm 0.0.13 | Thm 1.1.1 |
|----------|-----------|------------|-----------|-----------|----------|
| **Rank** | 2 (line 343) | 2 (§4.4) | N−1=2 (line 45) | 2 (implicit) | 2 (weight space) |
| **Center** | Z₃ exactly (line 246) | Z₃ from Weyl S₃ | — | Z₃ (Deriv §5) | — |
| **Weyl group** | S₃ (§3.0) | S₃ (§4.4: unique rank-2) | S_N (implicit) | S₃ (rep action) | S₃ (equivariant) |
| **Root system** | A₂ (lines 232–242) | A₂ (implicit) | — | A₂ (edge-root) | A₂ (weight map) |
| **Conclusion** | G = SU(3) (line 415) | SU(3) (lines 574–581) | N=3 → SU(3) | SU(3) ≅ Aut⊗(ω) | Weight bijection |

All files that identify a gauge group conclude SU(3) — same rank, same center, same Weyl group, same root system. No file concludes SU(2), SU(4), or any other group.

---

### M2.6: Z₃ Circularity in Topological Path Is Explicitly Addressed

**Result: PASS**

Thm 0.0.15 devotes a dedicated §3.0 (lines 117–141) to deriving Z₃ from pure stella geometry (3-fold rotational symmetry of the interpenetrating tetrahedra) without any reference to SU(3). The non-circularity is declared three times:

1. §3.0 line 141: "The Z₃ structure and phases (0, 2π/3, 4π/3) are derived from the geometric symmetry of the stella octangula. No reference to SU(3) is required. This breaks the apparent circularity: geometry → Z₃ → SU(3)."
2. §3.4.4 line 348: "Non-circular: Z₃ comes from stella geometry (§3.0), not from assuming SU(3)"
3. §9 line 694: "No circularity: Z₃ is established from stella geometry (§3.0) before any reference to SU(3)"

This is thorough handling — the most common circularity objection is preemptively addressed at three levels of the document.

---

### M2.7: D=4 External vs Internal Consistency

**Result: PASS**

The two D=4 results are:

| Result | File | Method | Logical Status |
|--------|------|--------|----------------|
| External D=4 | Thm 0.0.1 (F02) | Observer existence: P1 (gravity) + P2 (atoms) | DERIVATION (selection theorem) |
| Internal D=4 | Thm 0.0.9 (F17) | GR1-GR3 → gauge → Weinberg → GR+QM → D=4 | CONSISTENCY CHECK |

Thm 0.0.9 explicitly addresses circularity in §2.1 (lines 78–127) titled "The Circularity Question." The resolution: GR1-GR3 imply GR+QM (via Weinberg's theorem for spin-2 gravity, discrete weights for QM), which then feeds into the same Ehrenfest-Tegmark arguments as Thm 0.0.1. Lines 374–387 explicitly state: "Logical status: This constitutes a self-consistency check."

The logical loop is:
```
GR1-GR3 → non-abelian gauge + QM → GR + atomic constraints
    ↓
D = 4 (via Theorem 0.0.1's arguments)
    ↓
N = 3 → SU(3) → Stella Octangula
    ↓
[Validates GR1-GR3 structure]
```

Both results give D=4 (trivially identical). The crucial point is that F17 never claims to provide an independent derivation — it explicitly presents the result as showing the framework's assumptions are self-consistent.

---

### M2.8: Assumption A-CS (Compact Simple) Is Consistently Declared Across Paths

**Result: PASS (1 NOTE)**

| Path | File | A-CS Stated? | Line | Classification |
|------|------|-------------|------|----------------|
| Topological | Thm 0.0.15 | ✅ Explicit | 52–60 | (F) Framework-specific |
| Information-geometric | Prop 0.0.XX | ✅ Explicit | 36–42 | (F) Framework-specific |
| Tannaka | Thm 0.0.13 | ✅ Implicit | — | Compact required by Tannaka theorem |
| Dimensional | Thm 0.0.2b | ⚠️ Implicit | 33–34 | Scope: "confining SU(N) only" |

Both primary derivation paths (Thm 0.0.15 and Prop 0.0.XX) declare A-CS explicitly with identical wording and (F) classification. Thm 0.0.13 inherits compactness from the Tannaka–Krein theorem's standard requirements.

**NOTE:** Thm 0.0.2b, Lem 0.0.2a, and Prop 0.0.40 do not explicitly cite A-CS, though their scope is restricted to confining SU(N) which implicitly excludes the same groups. This is a minor gap in documentation, not a substantive inconsistency — the physics is the same, only the explicit labeling is missing.

---

### M2.9: Dependency DAG Is Acyclic and Correctly Ordered

**Result: PASS**

Dependencies flow strictly from lower to higher layers:

| File | Layer | Depends On | Layer of Deps |
|------|-------|-----------|---------------|
| Thm 0.0.15 (F10) | L3 | Def 0.1.2, Thm 0.0.1, Lem 0.0.2a | L1, L5 |
| Thm 0.0.12 (F11) | L3 | Def 0.0.0, Thm 0.0.2, Thm 0.0.3, Thm 1.1.1 | L1, L2, L6 |
| Thm 0.0.13 (F12) | L3 | Same as F11 + Thm 0.0.12 | L1, L2, L3 (intra, acyclic) |

No L1/L2 file declares L3 as a dependency. The intra-L3 dependency F12 → F11 is well-ordered (categorical equivalence feeds Tannaka reconstruction). Thm 0.0.2 (F03) mentions Thm 0.0.12 only as "see also" — not a dependency.

---

## Summary Table

| Check ID | Result | Description | Evidence | Severity |
|----------|--------|-------------|----------|----------|
| M2.1 | PASS | Dimensional path D=4→N=3→SU(3) is explicit and honest | F02:385–388, F04:303–304, F02:383 | — |
| M2.2 | PASS | Topological path derives SU(3) without circular SU(3) input | F10:117–141, 283, 343, 358–368 | — |
| M2.3 | PASS (2 NOTE) | Information-geometric path is independent and non-circular | F07:136, 330–335, 423–433; §0.3 line 95, §2.3 line 162 | — |
| M2.4 | PASS | Categorical/Tannaka paths correctly framed as consistency checks | F11:5; F12:3, 40–102, 76–81 | — |
| M2.5 | PASS | All paths yield same mathematical object (rank 2, Z₃ center, S₃ Weyl, A₂ roots) | Cross-file comparison table above | — |
| M2.6 | PASS | Z₃ circularity explicitly addressed (triple declaration) | F10:141, 348, 694 | — |
| M2.7 | PASS | D=4 external (Thm 0.0.1) and internal (Thm 0.0.9) are consistent | F02:23–52, F17:78–127, 374–387 | — |
| M2.8 | PASS (1 NOTE) | A-CS consistently declared across primary paths | F10:52, F07:36; F04 implicit only | — |
| M2.9 | PASS | Dependency DAG is acyclic and correctly ordered | F10, F11, F12 dependency sections | — |

---

## Overall Assessment

**All 9 checks PASS.** The SU(3) derivation architecture is internally consistent, logically honest, and free of circularity. Three key strengths:

1. **Derivation vs. selection vs. consistency check is explicitly maintained.** The dimensional path SELECTS SU(3), the topological path DETERMINES it from constraints, and the categorical/Tannaka paths CONFIRM it. No path overstates its logical status.

2. **Cross-path agreement is perfect.** All files that identify a gauge group conclude SU(3) with identical characterization (rank 2, dimension 8, center Z₃, Weyl group S₃, root system A₂).

3. **Circularity is actively managed.** Z₃ non-circularity in Thm 0.0.15 is declared three times; the D=4 consistency loop in Thm 0.0.9 is explicitly framed as self-consistency, not independent derivation; Prop 0.0.XX warns against circular use of Thm 0.1.0's interference form.

**3 NOTEs** (minor, non-blocking):
- Color neutrality condition in Prop 0.0.XX could benefit from standalone derivation from distinguishability axiom
- Prop 0.0.XX honestly states it does not reduce the framework's input count
- A-CS is implicit (not explicitly cited) in Thm 0.0.2b, Lem 0.0.2a, and Prop 0.0.40 — recommend adding explicit A-CS footnotes for documentation completeness

---

## JSON Summary

```json
{
  "group": "G1",
  "layer": 1,
  "module": "M2",
  "checks_total": 9,
  "checks_passed": 9,
  "checks_failed": 0,
  "checks_noted": 3,
  "findings": [
    {
      "check_id": "M2.1",
      "result": "PASS",
      "description": "Dimensional path D=4 → N=3 → SU(3) is explicit and honest",
      "evidence": "F02:385-388 'We do NOT derive SU(3) from D=4 alone' (§4 Corollary); F04:303-304 D=N+1 three-term decomposition; F02:383 Corollary 0.0.1a N=3",
      "severity": null
    },
    {
      "check_id": "M2.2",
      "result": "PASS",
      "description": "Topological path (Thm 0.0.15) derives SU(3) from constraint intersection without circular SU(3) input",
      "evidence": "F10:117-141 Z₃ from stella geometry independently; F10:283,343 rank ≤ 2 from Lem 0.0.2a; F10:358-368 elimination table; triple non-circularity declaration at lines 141, 348, 694",
      "severity": null
    },
    {
      "check_id": "M2.3",
      "result": "PASS",
      "description": "Information-geometric path (Prop 0.0.XX) is independent and non-circular; does not reduce input count (honestly stated)",
      "evidence": "F07:136,209 Fisher non-degeneracy N≥3; F07:330-335 affine independence N≤4; F07:423-433 Cartan classification; §0.3 line 95 honest disclaimer; §2.3 line 162 circular reasoning warning",
      "severity": null
    },
    {
      "check_id": "M2.4",
      "result": "PASS",
      "description": "Categorical (Thm 0.0.12) and Tannaka (Thm 0.0.13) paths correctly framed as consistency checks, not derivations",
      "evidence": "F11:5 'categorically equivalent'; F12:3 '(Consistency Result)'; F12:40-102 §0 'What This Theorem Does and Does Not Show'; F12:76-81 table 'SU(3) derived purely from stella geometry → FALSE'",
      "severity": null
    },
    {
      "check_id": "M2.5",
      "result": "PASS",
      "description": "All paths yield same mathematical object: rank 2, center Z₃, Weyl group S₃, root system A₂",
      "evidence": "Cross-file comparison: F10:415 G=SU(3); F07:574-581 Theorem 4.5 SU(3); F04 Corollary N=3; F12:109-116 SU(3)≅Aut⊗(ω); F25:18,260 weight bijection. No file concludes different group.",
      "severity": null
    },
    {
      "check_id": "M2.6",
      "result": "PASS",
      "description": "Z₃ circularity in topological path explicitly addressed with triple declaration",
      "evidence": "F10:117-141 §3.0 dedicated non-circularity section; F10:141 'No reference to SU(3) is required'; F10:348 restated; F10:694 final summary",
      "severity": null
    },
    {
      "check_id": "M2.7",
      "result": "PASS",
      "description": "D=4 external (Thm 0.0.1) and internal (Thm 0.0.9) results are consistent; internal correctly framed as self-consistency check",
      "evidence": "F02:23-52 D=4 from P1+P2; F17:78-127 §2.1 'The Circularity Question'; F17:374-387 'Logical status: self-consistency check'; both give D=4",
      "severity": null
    },
    {
      "check_id": "M2.8",
      "result": "PASS",
      "description": "Assumption A-CS (compact simple) consistently declared across primary derivation paths",
      "evidence": "F10:52-60 explicit (F)-class; F07:36-42 explicit (F)-class; F12 implicit via Tannaka requirements; F04:33-34 implicit via 'confining SU(N) only' scope",
      "severity": null
    },
    {
      "check_id": "M2.9",
      "result": "PASS",
      "description": "Dependency DAG across SU(3) derivation paths is acyclic and correctly ordered",
      "evidence": "F10 depends on L1/L5 only; F11 depends on L1/L2/L6; F12 depends on L1/L2/L3(intra,acyclic); no upward dependencies from L1/L2 to L3",
      "severity": null
    }
  ],
  "overall_result": "PASS"
}
```
