# G1 Geometric Foundation — Coherence Audit: Module M8 Findings

> **Module:** M8 — Dependency Chain Verification
> **Layer:** 1 (Coherence)
> **Posture:** DEFENSIVE — verify internal consistency
> **Scope:** All 26 proof files in thematic group G1 (expanding to ~33 physical files via 3-file structures)
> **Audited:** 2026-03-14 (seventh audit — independent re-verification, supersedes prior M8 reports)
> **Re-verification (v7, 2026-03-14):** Full independent re-verification by separate agent session. All 26 proof files' dependency sections re-read via parallel subagent extraction and direct grep verification. All prior findings confirmed with one refinement: the 5-cycle [3]→[19]→[9]→[6]→[5]→[3] is downgraded from "formal cycle" to "informal transitive path" because the [9]→[6] edge passes through Physical Hypothesis 0.0.0f (⚠️ marker), not a declared dependency on Prop 0.0.40. New finding M8.H added: Phys Hyp 0.0.0f is used as an assumed hypothesis in three files ([5], [9], [16]) with inconsistent treatment in DAG classification.
> **Auditor:** Autonomous agent (Claude Opus 4.6)
> **Cross-reference:** [G1-Geometric-Foundation-Coherence-Audit.md](G1-Geometric-Foundation-Coherence-Audit.md) § Module 8

---

## Audit Methodology

Every G1 proof file was read and its declared "Dependencies" section extracted verbatim. All inline cross-references (e.g., "by Theorem 0.0.1", "from Definition 0.0.0") were catalogued. A complete directed graph was constructed from these declarations. The graph was then checked for:

1. **Cycles** (M8.1) — Does any proof depend, directly or transitively, on itself?
2. **Layer ordering** (M8.2) — Do dependencies respect the 6-layer thematic structure?
3. **Upward dependencies** (M8.3) — Do any L1–L3 files depend on L4–L6?
4. **Completeness** (M8.4) — Is every actually-used result declared as a dependency?
5. **Accuracy** (M8.5) — Is every declared dependency actually used?
6. **Cross-layer minimality** (M8.6) — Are L5 Phase 0 definitions free of L3 dependencies?
7. **Internal D=4 independence** (M8.7) — Does Thm 0.0.9 avoid depending on Thm 0.0.1?

File numbering follows the task specification's 26-item ordering: [1] = Def 0.0.0, [2] = Thm 0.0.1, ..., [26] = Def 1.1.4.

> **Note on numbering systems:** The audit plan (G1-Geometric-Foundation-Coherence-Audit.md) uses a 23-file list with F01–F23. The task specification uses a 26-file list (adding Prop 0.0.40, Prop 0.1.3a, Def 1.1.4). This report uses the task specification's ordering exclusively. When citing the audit plan's file IDs, they are prefixed with "AP-" to distinguish them (e.g., AP-F15 = Thm 0.0.6 in audit plan, vs [13] = Thm 0.0.6 in task spec).

---

## Complete Dependency DAG

### Extracted declared dependencies (from each file's "Dependencies" section)

| Task # | File | Declared Dependencies (G1-internal) | External Dependencies |
|--------|------|--------------------------------------|----------------------|
| [1] | Def 0.0.0 | None (foundational) | — |
| [2] | Thm 0.0.1 | Def 0.0.0 [1] | Standard physics |
| [3] | Thm 0.0.2 | Thm 0.0.1 [2], **Def 0.1.1-Apps §12.3.2 [19]** | Standard SU(3) Lie algebra |
| [4] | Thm 0.0.2b | Thm 0.0.1 [2], Thm 0.0.2 [3], Lem 0.0.2a [5] | Thm 0.2.2 (G3), standard Lie algebra |
| [5] | Lem 0.0.2a | Thm 0.0.1 [2], Thm 0.0.2 [3], ⚠️ Phys Hyp 0.0.0f | QCD confinement (experimental) |
| [6] | Prop 0.0.40 | Lem 0.0.2a [5], Def 0.0.0 [1] | QCD confinement, SU(N) coupling |
| [7] | Thm 0.0.0a | Thm 0.0.6 [13], Thm 0.0.3 §5.3.1 [9], Def 0.0.0 Lem 0.0.0f [1], Thm 0.0.1 [2] | Thm 0.0.10 (bootstrap target) |
| [8] | Prop 0.0.XX | Thm 0.0.1 [2], Lem 0.0.2a [5], Thm 0.1.0 [24] | Prop 0.0.XXa, Prop 0.0.17b, Thm 0.0.17, Lem 0.0.17c |
| [9] | Thm 0.0.3 | Def 0.0.0 [1], Thm 0.0.1 [2], Thm 0.0.2 [3], ⚠️ Phys Hyp 0.0.0f | — |
| [10] | Thm 0.0.3b | Def 0.0.0 [1], Thm 0.0.3 [9] | — |
| [11] | Prop 0.0.16a | ⚠️ Phys Hyp 0.0.0f, Thm 0.0.3 [9], Thm 0.0.6 [13], Thm 0.0.16 [12] | — |
| [12] | Thm 0.0.16 | Thm 0.0.2 [3], Thm 0.0.3 [9], Thm 0.0.6 [13], Def 0.0.0 [1] | Gap-Analysis (informational) |
| [13] | Thm 0.0.6 | Thm 0.0.3 [9], Def 0.1.1 [19], Def 0.1.2 [20], Thm 0.0.2 [3] | Thm 0.0.17; ⚠️ Phys Hyp 0.0.0f |
| [14] | Prop 0.0.6b | Thm 0.0.6 [13], Def 0.0.0 [1], Thm 0.0.15 [16] | Prop 0.0.5a, Prop 0.0.17r |
| [15] | Thm 0.0.9 | Thm 0.0.3 [9] | Thms 0.0.0, 0.0.4, 0.0.8, 0.0.10, 0.0.11, 5.2.1, 5.2.3, 5.2.4 |
| [16] | Thm 0.0.15 | Thm 0.0.1 [2], Lem 0.0.2a [5], Def 0.1.2 [20] (notational only), ⚠️ Phys Hyp 0.0.0f | Standard Lie theory, Assumption A-CS |
| [17] | Thm 0.0.12 | Def 0.0.0 [1], Thm 0.0.2 [3], Thm 0.0.3 [9], Thm 1.1.1 [25] | — |
| [18] | Thm 0.0.13 | Def 0.0.0 [1], Thm 0.0.2 [3], Thm 0.0.3 [9], Thm 0.0.12 [17], Thm 1.1.1 [25] | — |
| [19] | Def 0.1.1 | Thm 0.0.3 [9], Thm 0.0.1 [2] | Standard topology |
| [20] | Def 0.1.2 | Def 0.1.1 [19], Thm 0.0.3 [9] | Standard SU(3) |
| [21] | Def 0.1.3 | Def 0.1.1 [19], Def 0.1.2 [20] | Standard geometry |
| [22] | Prop 0.1.3a | Def 0.1.1 §8 [19], Def 0.1.3 [21] | — |
| [23] | Def 0.1.4 | Def 0.1.1 [19], Def 0.1.2 [20], Def 0.1.3 [21] | Standard Voronoi |
| [24] | Thm 0.1.0 | Thm 0.0.3 [9], Def 0.0.0 [1] | Thm 0.0.17 |
| [25] | Thm 1.1.1 | Def 0.1.1 [19] | — |
| [26] | Def 1.1.4 | Def 0.1.1 [19], Def 0.1.2 [20], Def 0.1.3 [21], Thm 1.1.1 [25] | Thm 0.2.1, Thm 1.1.2, Thm 1.1.3 |

> **Key issue:** [3] Thm 0.0.2 **explicitly declares** Def 0.1.1-Applications §12.3.2 [19] as a dependency (added by commit `0c6fe73d` to disambiguate a bare body reference "Theorem 12.3.2"). This declaration creates a formal 3-cycle (see M8.1). The D = N + 1 formula referenced is independently derivable from standard SU(N) representation theory without any stella octangula input.

> **Phys Hyp 0.0.0f classification (v7 refinement):** Four files ([5], [9], [13], [16]) declare Physical Hypothesis 0.0.0f with ⚠️ markers and informational notes that it is "now derived in Proposition 0.0.40." These are **assumed hypotheses**, not formal dependency edges to [6] Prop 0.0.40. The note about derivation is informational provenance tracking. See M8.H for details.

---

## DAG Visualization (G1-internal edges only)

```
[1] (Def 0.0.0) ──────────────────────────────────────────────────────┐
 │                                                                     │
 ├──→ [2] (Thm 0.0.1)                                                 │
 │     │                                                               │
 │     ├──→ [3] (Thm 0.0.2) ←─── [19] (Def 0.1.1-Apps §12.3.2)  ⚠️ CYCLE
 │     │     │                     ↑                                   │
 │     │     ├──→ [5] (Lem 0.0.2a) ←── [3]                           │
 │     │     │     │                                                   │
 │     │     │     ├──→ [6] (Prop 0.0.40)                             │
 │     │     │     ├──→ [4] (Thm 0.0.2b) ←── [3],[2]                 │
 │     │     │     └──→ [16] (Thm 0.0.15) ←── [2]                    │
 │     │     │                                                         │
 │     │     ├──→ [9] (Thm 0.0.3) ←── [1]                            │
 │     │     │     │                                                   │
 │     │     │     ├──→ [10] (Thm 0.0.3b)                             │
 │     │     │     ├──→ [24] (Thm 0.1.0) ←── [1]                     │
 │     │     │     ├──→ [19] (Def 0.1.1) ←── [2]   ──→ [3] ⚠️ CYCLE │
 │     │     │     │     ├──→ [20] (Def 0.1.2) ←── [9]               │
 │     │     │     │     │     ├──→ [21] (Def 0.1.3)                  │
 │     │     │     │     │     │     ├──→ [22] (Prop 0.1.3a) ←── [19]│
 │     │     │     │     │     │     └──→ [23] (Def 0.1.4) ←── [19],[20]│
 │     │     │     │     │     └──→ [16] (Thm 0.0.15) (notational)   │
 │     │     │     │     ├──→ [25] (Thm 1.1.1)                       │
 │     │     │     │     │     └──→ [26] (Def 1.1.4) ←── [20],[21]   │
 │     │     │     │     └──→ [13] (Thm 0.0.6) ←── [9],[20],[3]     │
 │     │     │     │           │                                       │
 │     │     │     │           ├──→ [12] (Thm 0.0.16) ←── [3],[9],[1]│
 │     │     │     │           │     └──→ [11] (Prop 0.0.16a) ←── [9]│
 │     │     │     │           ├──→ [14] (Prop 0.0.6b) ←── [1],[16]  │
 │     │     │     │           └──→ [7] (Thm 0.0.0a) ←── [9],[1],[2] │
 │     │     │     │                                                   │
 │     │     │     ├──→ [17] (Thm 0.0.12) ←── [1],[3],[25]           │
 │     │     │     │     └──→ [18] (Thm 0.0.13) ←── [1],[3],[25]     │
 │     │     │     │                                                   │
 │     │     │     ├──→ [8] (Prop 0.0.XX) ←── [2],[5],[24]           │
 │     │     │     └──→ [15] (Thm 0.0.9)                              │
 │     │     │                                                         │
 │     └─────┴────────────────────────────────────────────────────────┘
```

**⚠️ The DAG contains one confirmed formal cycle rooted at the [3]→[19] edge.**

The cycle path (3-node):
- [3] Thm 0.0.2 declares dependency on **Def 0.1.1-Applications §12.3.2** [19]
- [19] Def 0.1.1 declares dependency on **Thm 0.0.3** [9]
- [9] Thm 0.0.3 declares dependency on **Thm 0.0.2** [3]

> **v7 correction:** Prior reports also cited a 5-cycle [3]→[19]→[9]→[6]→[5]→[3]. This is **not a formal cycle** because the [9]→[6] edge passes through Physical Hypothesis 0.0.0f (an ⚠️-marked assumed hypothesis), not a declared dependency on Prop 0.0.40. The informational note "now derived in Proposition 0.0.40" is provenance tracking, not a formal dependency declaration. See M8.E and M8.H.

The cycle is **formal (documentation-level), not logical**: the D = N + 1 formula is independently derivable from standard SU(N) representation theory (rank(su(N)) = N - 1, plus the radial degree of freedom). Removing the single edge [3]→[19] eliminates all cycles.

### Topological Sort (valid ordering if [3]→[19] edge is removed)

```
Level 0:  [1]  (Def 0.0.0)
Level 1:  [2]  (Thm 0.0.1)
Level 2:  [3]  (Thm 0.0.2)
Level 3:  [5]  (Lem 0.0.2a)
Level 4:  [6]  (Prop 0.0.40), [4] (Thm 0.0.2b)
Level 5:  [9]  (Thm 0.0.3)
Level 6:  [10] (Thm 0.0.3b), [24] (Thm 0.1.0), [19] (Def 0.1.1), [15] (Thm 0.0.9)
Level 7:  [20] (Def 0.1.2), [25] (Thm 1.1.1), [8] (Prop 0.0.XX)
Level 8:  [21] (Def 0.1.3), [13] (Thm 0.0.6), [16] (Thm 0.0.15)
Level 9:  [22] (Prop 0.1.3a), [23] (Def 0.1.4), [26] (Def 1.1.4),
          [12] (Thm 0.0.16), [14] (Prop 0.0.6b), [17] (Thm 0.0.12)
Level 10: [11] (Prop 0.0.16a), [7] (Thm 0.0.0a), [18] (Thm 0.0.13)
```

---

## Check Results

### M8.1: No Circular Dependencies (DAG is acyclic)

| Result | **FAIL** |
|--------|----------|
| **Severity** | **MODERATE** |

**Method:** Constructed the full directed graph from all declared dependency edges. Performed cycle detection by tracing all paths.

**Finding:** The G1 dependency graph contains one cycle rooted at a single problematic edge:

**Confirmed cycle (3-node):**
```
[3] Thm 0.0.2  ──declares dep on──→  [19] Def 0.1.1  ──declares dep on──→  [9] Thm 0.0.3  ──declares dep on──→  [3] Thm 0.0.2
```

**Edge verification (v7):**
- [3]→[19]: Thm 0.0.2 line 40: `- Definition 0.1.1-Applications §12.3.2 (D = N + 1 formula; see Definition-0.1.1-Stella-Octangula-Boundary-Topology-Applications.md)` ✅
- [19]→[9]: Def 0.1.1 line 13: `- ✅ **Theorem 0.0.3 (Stella Octangula Uniqueness)**` ✅
- [9]→[3]: Thm 0.0.3 line 44: `- Theorem 0.0.2 (Euclidean Metric from SU(3))` ✅

**Root cause:** Commit `0c6fe73d` (M8.4 fix) disambiguated Thm 0.0.2's body reference "Theorem 12.3.2" by adding an explicit file path to the **Dependencies** section:

```
- Definition 0.1.1-Applications §12.3.2 (D = N + 1 formula; see Definition-0.1.1-Stella-Octangula-Boundary-Topology-Applications.md)
```

This elevated a notational cross-reference to a formal dependency, creating the cycle.

**Why this is NOT a logical cycle:** The D = N + 1 formula (Theorem 12.3.2 in the Applications file) is established from:
1. Lie algebra theory: rank(su(N)) = N - 1 → weight space is (N-1)-dimensional
2. Implicit function theorem: gradient independence for the radial coordinate
3. These are standard results requiring NO input from Def 0.1.1's stella octangula definition or Thm 0.0.3's uniqueness proof

**Independent verification:** Thm 0.0.2 §0 ("Critical Clarification") at line 47 states: "The D = N + 1 formula is now **derived** in Theorem 0.0.2b." This confirms the formula is available from Thm 0.0.2b's derivation chain ([2]→[3]→[5]→[4]), which does NOT pass through [19].

**Recommended fix:** In Thm 0.0.2's Dependencies section (line 40), reclassify the reference:
1. **Option A:** Move it to a "Cross-references" or "See also" section, or
2. **Option B:** Add qualifier: `(notational reference — independently derivable from standard SU(N) theory)`, or
3. **Option C:** Derive D = N + 1 inline (3-line argument from rank(su(N)) = N - 1)

**Former cycle {[11],[12],[13]} status:** RESOLVED. Thm 0.0.6's "Axiom A0 status upgrade (not a dependency)" blockquote at line 105 correctly classifies the relationship with Thm 0.0.16 and Prop 0.0.16a.

---

### M8.2: Layer Ordering Respected

| Result | **FAIL** |
|--------|----------|
| **Severity** | **MODERATE** |

**Method:** Compared each file's topological level against its assigned layer in the audit plan.

**Finding:** The thematic layer assignments do NOT form a partial order compatible with the dependency DAG. Four of six layer boundaries are violated:

| File | Assigned Layer | Actual Topo Level | Violation |
|------|---------------|-------------------|-----------|
| [7] (Thm 0.0.0a) | L2 (Stella Construction) | Level 10 | L2 file depends on L4 ([13]) and L5 ([9] via [13]) |
| [13] (Thm 0.0.6) | L4 (Spatial Extension) | Level 8 | L4 file depends on L5 ([19], [20]) |
| [19] (Def 0.1.1) | L5 (Phase 0 Definitions) | Level 6 | L5 file is upstream of L4 |
| [25] (Thm 1.1.1) | L6 (Bridge) | Level 7 | L6 file is upstream of L3 ([17], [18]) |

**Specific violations:**

1. **Thm 0.0.0a [7, L2] depends on Thm 0.0.6 [13, L4]:** An L2 file requiring an L4 result.

2. **Thm 0.0.12 [17, L3] and Thm 0.0.13 [18, L3] depend on Thm 1.1.1 [25, L6]:** L3 files requiring an L6 result.

3. **Thm 0.0.6 [13, L4] depends on Def 0.1.1 [19, L5] and Def 0.1.2 [20, L5]:** An L4 file requiring L5 results.

**Mitigation:** The audit plan acknowledges this at line 42: "These layers are **thematic groupings**, not strict dependency tiers. The actual dependency DAG crosses layer boundaries." The THEMATIC-GROUPS.md table was updated (commit `cceaee36`) to label proofs as "theorem-number order" with a prominent note linking to this M8 analysis.

**Recommendation:** Consider relabeling "layers" as "thematic categories" since 4 of 6 boundaries are violated.

---

### M8.3: No Upward Dependencies (L1–L3 files free of L4–L6 dependencies)

| Result | **FAIL** |
|--------|----------|
| **Severity** | **MODERATE** |

**Finding:** Three L1–L3 files depend on L4–L6 files:

| Source (L1–L3) | Depends On (L4–L6) | Declared? |
|----------------|---------------------|-----------|
| Thm 0.0.0a [7, L2] | Thm 0.0.6 [13, L4] | ✅ Yes |
| Thm 0.0.12 [17, L3] | Thm 1.1.1 [25, L6] | ✅ Yes |
| Thm 0.0.13 [18, L3] | Thm 1.1.1 [25, L6] | ✅ Yes |

All three upward dependencies are **honestly declared**. The audit plan's layer tables have been annotated with warning markers referencing M8.3 (prior resolution).

---

### M8.4: Declared Dependencies Are Complete

| Result | **PASS** |
|--------|----------|

**Method:** For each proof file, compared body inline references against the declared Dependencies section.

**Finding:** All actually-used results are declared:

1. **Thm 0.0.2 [3]:** The bare "Theorem 12.3.2" reference has been disambiguated to `Definition 0.1.1-Applications §12.3.2` with explicit file path. (Note: this created the M8.1 cycle — see recommendation there.)

2. **Thm 0.0.16 [12]:** Gap-Analysis reference correctly declared with "(informational)" qualifier.

3. **Thm 0.0.6 [13]:** The "Axiom A0 status upgrade" note correctly separates the retrospective derivation (not a dependency) from actual inputs.

**Residual NOTE:** Thm 0.0.13 [18] references "Definition 0.1.1 §4.1.5 (Apex-Cartan Theorem)" in its body. This is transitively covered via Thm 1.1.1 [25] → Def 0.1.1 [19]; it is an illustrative cross-reference, not a logical input.

---

### M8.5: Declared Dependencies Are Accurate (no phantom dependencies)

| Result | **PASS** |
|--------|----------|

**Method:** For each declared dependency, verified the proof body actually references or uses the cited result.

**Finding:** No phantom dependencies found. Every declared dependency is actually used:

| File | Declared Dep | Verification |
|------|-------------|--------------|
| [4] (Thm 0.0.2b) | Thm 0.2.2 (Internal Time) | Used in §Hypothesis P3 for time parameter λ |
| [9] (Thm 0.0.3) | Phys Hyp 0.0.0f | Used for 3D embedding requirement (lines 45, 97, 136, 197) |
| [13] (Thm 0.0.6) | Def 0.1.2 [20] | Phase structure matching across boundaries (line 101) |
| [16] (Thm 0.0.15) | Def 0.1.2 [20] | Explicitly marked "notational reference only" |
| [17] (Thm 0.0.12) | Thm 1.1.1 [25] | Vertex-weight bijection |
| [18] (Thm 0.0.13) | Thm 0.0.12 [17] | Cartan-level equivalence as starting point |

**Note on [16]:** Thm 0.0.15 declares Def 0.1.2 as a dependency but marks it "notational reference only." The Z₃ center is derived independently in §3.0 from stella geometry. Strictly, this is a phantom dependency, but since it's explicitly qualified, no FAIL is warranted.

---

### M8.6: Cross-Layer Dependencies Are Minimal (L5 Phase 0 defs free of L3 deps)

| Result | **PASS** |
|--------|----------|

**Method:** Checked [19]–[24] (L5 Phase 0 files) and [25]–[26] (L6 bridge files) for dependencies on L3 (Thm 0.0.15 [16], Thm 0.0.12 [17], Thm 0.0.13 [18]).

**Finding:** No L5 file depends on any L3 file:

- [19] (Def 0.1.1) → depends on [9] (L2), [2] (L1) — correct
- [20] (Def 0.1.2) → depends on [19] (L5), [9] (L2) — correct (Thm 0.1.0 is mentioned in "Derivation Status" note but NOT in Dependencies section)
- [21] (Def 0.1.3) → depends on [19], [20] (both L5) — correct
- [22] (Prop 0.1.3a) → depends on [19], [21] (both L5) — correct
- [23] (Def 0.1.4) → depends on [19], [20], [21] (all L5) — correct
- [24] (Thm 0.1.0) → depends on [9] (L2), [1] (L1) + Thm 0.0.17 (outside G1) — correct
- [25] (Thm 1.1.1) → depends on [19] (L5) — correct
- [26] (Def 1.1.4) → depends on [19]–[21] (L5), [25] (L6) + outside G1 — correct

The L3 reconstruction theorems are downstream consumers of Phase 0 definitions, not prerequisites. Architecturally sound.

---

### M8.7: Internal D=4 (Thm 0.0.9) Does NOT Depend on Thm 0.0.1

| Result | **PASS** |
|--------|----------|

**Method:** Read [15] (Thm 0.0.9) dependency section verbatim.

**Finding:** Thm 0.0.9 correctly separates its dependencies into two labeled categories:

**Dependencies (Logical Prerequisites):**
```
- ✅ Theorem 0.0.0 (GR Conditions Derivation)
- ✅ Theorem 0.0.3 (Stella Uniqueness)
- ✅ Theorem 0.0.4 (GUT Structure)
- ✅ Theorem 0.0.8 (Emergent Rotational Symmetry)
- ✅ Theorem 0.0.10 (Quantum Mechanics Emergence)
- ✅ Theorem 0.0.11 (Lorentz Boost Emergence)
- ✅ Theorem 5.2.1, 5.2.3, 5.2.4 (Emergent Gravity)
```

**Validated Against (Consistency Targets — not logical inputs):**
```
- ✅ Theorem 0.0.1 (D=4 from Observer Existence) — the target being validated, not a premise
```

The derivation is clearly independent of Thm 0.0.1. The restructured header (commit `d767b1cf`) correctly distinguishes logical prerequisites from consistency targets.

---

## Additional Findings

### M8.A: Thematic Group Ordering vs Dependency Order

| Result | **NOTE** |
|--------|----------|

The THEMATIC-GROUPS.md table note correctly states that proofs are listed in "theorem-number order, not by dependency." The note references this M8 analysis for the actual DAG. This is accurately self-documented.

### M8.B: External Dependencies Outside G1

| Result | **NOTE** |
|--------|----------|

Six G1 files have external dependencies. These are expected for boundary files:

| G1 File | External Dependency | Likely Group |
|---------|---------------------|--------------|
| Thm 0.0.2b [4] | Thm 0.2.2 (Internal Time Emergence) | G3 (Time & Entropy) |
| Prop 0.0.XX [8] | Prop 0.0.XXa, Prop 0.0.17b, Thm 0.0.17, Lem 0.0.17c | G1-adjacent (information geometry) |
| Thm 0.0.6 [13] | Thm 0.0.17 (Information-Geometric Unification) | G1-adjacent |
| Prop 0.0.6b [14] | Prop 0.0.5a, Prop 0.0.17r | G2/G6 |
| Thm 0.0.9 [15] | Thms 0.0.0, 0.0.4, 0.0.8, 0.0.10, 0.0.11, 5.2.x | G2, G3, G8 |
| Def 1.1.4 [26] | Thm 0.2.1, Thm 1.1.2, Thm 1.1.3 | G2, G4 |

These must be verified during cross-group audits.

### M8.C: Resolution History — Former {Thm 0.0.6, Thm 0.0.16, Prop 0.0.16a} Cycle

| Result | **RESOLVED** |
|--------|--------------|

The prior CRITICAL 3-node SCC was resolved by restructuring Thm 0.0.6's dependency section to classify the relationship with Thm 0.0.16 and Prop 0.0.16a as an "Axiom A0 status upgrade (not a dependency)." Independently verified at Thm 0.0.6 line 105: the blockquote correctly states they "depend on this theorem's results (honeycomb structure, phase coherence), not the reverse."

### M8.D: M8.4 Fix Created New Formal Cycle

| Result | **NOTE** |
|--------|----------|

Commit `0c6fe73d` resolved M8.4 (ambiguous body reference) by placing the Def 0.1.1-Apps §12.3.2 reference in the Dependencies section rather than a See-Also or Cross-references section. This elevated a notational cross-reference to a formal dependency, creating the M8.1 cycle.

**Lesson learned:** When disambiguating cross-references, preserve the original dependency classification. A file-path clarification should not change whether a reference is a logical prerequisite.

### M8.E: Prior 5-Cycle Claim Downgraded (v7 refinement)

| Result | **NOTE** |
|--------|----------|

Prior reports (v5–v6) cited a 5-cycle: [3]→[19]→[9]→[6]→[5]→[3]. Independent re-verification shows the [9]→[6] edge is **not a formal declared dependency**:

- Thm 0.0.3 line 45 declares: `Physical Hypothesis 0.0.0f (3D Embedding from Confinement) — now **derived** in [Proposition 0.0.40]`
- The ⚠️ marker indicates this is an **assumed hypothesis**, not a dependency on Prop 0.0.40
- The note "now derived in Proposition 0.0.40" is informational provenance tracking

The same pattern appears in Lem 0.0.2a (line 22), Thm 0.0.15 (line 27), and Thm 0.0.6 (body references). In none of these files is Prop 0.0.40 listed as a formal prerequisite.

**Conclusion:** Only the 3-cycle [3]→[19]→[9]→[3] is a genuine formal cycle. The 5-cycle was an artifact of interpreting ⚠️ hypothesis notes as dependency edges. The single edge [3]→[19] remains the sole root cause of all cyclic behavior.

### M8.F: Thm 0.0.6 Dependency Accuracy

| Result | **NOTE** |
|--------|----------|

Independently verified that Thm 0.0.6 does NOT declare Thm 0.0.4 (GUT Structure) as a dependency — the actual dependencies are Thm 0.0.3, Def 0.1.1, Def 0.1.2, Thm 0.0.2, and Thm 0.0.17 (external). Some prior reports incorrectly listed Thm 0.0.4 as a dependency. The file is accurate as written (lines 98–103).

### M8.G: Def 0.1.2 Does NOT Depend on Thm 0.1.0

| Result | **NOTE** |
|--------|----------|

**Finding (fifth audit correction, v7 re-confirmed):** Prior M8 reports listed [20] Def 0.1.2 as depending on [24] Thm 0.1.0. Independent verification shows this is **incorrect**. Def 0.1.2's Dependencies section (lines 13–17) lists only:
- Def 0.1.1 [19] (Stella Octangula as Boundary Topology)
- Thm 0.0.3 [9] (Stella Uniqueness)

Thm 0.1.0 appears in the "Derivation Status" note (lines 7–11) as having independently derived the same content, but this is an informational cross-reference, not a logical dependency. The DAG table and visualization have been corrected. The topological sort is unaffected (Level 7 for [20] is still correct: max(Level [19]=6, Level [9]=5) + 1 = 7).

### M8.H: Physical Hypothesis 0.0.0f Classification (v7 new finding)

| Result | **NOTE** |
|--------|----------|

**Finding:** Physical Hypothesis 0.0.0f (confinement requires d_embed = rank + 1) appears in four G1 files with ⚠️ markers:

| File | Line | Declared as | Note |
|------|------|-------------|------|
| [5] Lem 0.0.2a | 22 | ⚠️ Phys Hyp 0.0.0f | "now **derived** in Proposition 0.0.40" |
| [9] Thm 0.0.3 | 45 | Phys Hyp 0.0.0f | "now **derived** in [Proposition 0.0.40]" |
| [13] Thm 0.0.6 | body | Phys Hyp 0.0.0f | Referenced throughout body, not in Dependencies section header |
| [16] Thm 0.0.15 | 27 | ⚠️ Phys Hyp 0.0.0f | "now **derived** in [Proposition 0.0.40]" |

**Key observation:** [6] Prop 0.0.40 was written specifically to **derive** Physical Hypothesis 0.0.0f, using [5] Lem 0.0.2a's lower bound as Part A of its proof. This creates a subtle logical structure:

1. [5] provides the D_space ≥ N - 1 lower bound (does not require 0.0.0f for this)
2. [6] combines [5]'s lower bound with confinement and single-coupling arguments to derive d_embed = rank + 1 exactly (i.e., derives 0.0.0f)
3. [5], [9], [13], [16] all **use** 0.0.0f (originally as hypothesis, now provably true via [6])

This is logically coherent — there is no actual cycle between [5] and [6] because [5]'s core result (the lower bound) is independent of 0.0.0f. The ⚠️ markers correctly indicate the historical status as a hypothesis, and the informational notes correctly track that it's now derived.

**Recommendation:** For clarity, consider standardizing how derived-hypothesis references are formatted. Currently the ⚠️ marker is inconsistent (present in [5] and [16], absent in [9]'s dependencies section).

---

## Summary Table

| Check ID | Result | Description | Evidence | Severity |
|----------|--------|-------------|----------|----------|
| M8.1 | **FAIL** | One formal 3-cycle via [3]→[19] edge: [3]→[19]→[9]→[3]. Documentation-level, not logical. | Thm 0.0.2 line 40; Def 0.1.1 line 13; Thm 0.0.3 line 44. Root cause: commit 0c6fe73d. | MODERATE |
| M8.2 | **FAIL** | Layer ordering violated — 4 of 6 layer boundaries have cross-boundary dependencies | [7](L2)→[13](L4); [17],[18](L3)→[25](L6); [13](L4)→[19](L5). Self-documented at audit plan line 42. | MODERATE |
| M8.3 | **FAIL** | Three L1–L3 files depend on L4–L6 files | Thm 0.0.0a(L2)→Thm 0.0.6(L4); Thm 0.0.12(L3)→Thm 1.1.1(L6); Thm 0.0.13(L3)→Thm 1.1.1(L6). All honestly declared. | MODERATE |
| M8.4 | **PASS** | Declared dependencies are complete — all used results declared | Thm 0.0.2 has explicit file path for D=N+1 formula. Thm 0.0.16 Gap-Analysis marked informational. Thm 0.0.6 A0 upgrade note correct. | — |
| M8.5 | **PASS** | No phantom dependencies — all declared deps used in proof bodies | All 26 files checked. Thm 0.0.15's Def 0.1.2 dep marked "notational only" — honest and accurate. | — |
| M8.6 | **PASS** | Phase 0 definitions (L5) are free of L3 reconstruction dependencies | [19]–[26] depend only on L1 ([1],[2]), L2 ([9]), L5 (each other), L6 ([25]), or external. | — |
| M8.7 | **PASS** | Thm 0.0.9 correctly separates logical prerequisites from consistency targets | Dependency section has two labeled subsections. Thm 0.0.1 appears only in "Validated Against." | — |
| M8.A | **NOTE** | THEMATIC-GROUPS.md ordering correctly documented as theorem-number order with DAG link | Note added referencing M8 findings for actual dependency ordering. | — |
| M8.B | **NOTE** | Six G1 files have external dependencies (expected for boundary files) | [4]→G3, [8]→info-geom, [13]→Thm 0.0.17, [14]→G2/G6, [15]→G2/G3/G8, [26]→G2/G4 | — |
| M8.C | **RESOLVED** | Former CRITICAL cycle {[11],[12],[13]} resolved — A0 status upgrade note intact | Thm 0.0.6 line 105: blockquote correctly classifies relationship | — |
| M8.D | **NOTE** | M8.4 fix (commit 0c6fe73d) created M8.1 cycle by placing cross-reference in Dependencies | File-path disambiguation should not change dependency classification | — |
| M8.E | **NOTE** | Prior 5-cycle claim downgraded — [9]→[6] edge is ⚠️ hypothesis, not formal dependency | Thm 0.0.3 line 45: Phys Hyp 0.0.0f is ⚠️ assumed hypothesis, not dep on Prop 0.0.40 | — |
| M8.F | **NOTE** | Thm 0.0.6 correctly omits Thm 0.0.4 from dependencies (correcting prior report errors) | Thm 0.0.6 lines 98–103: lists only [9],[19],[20],[3], Thm 0.0.17 | — |
| M8.G | **NOTE** | Def 0.1.2 does NOT depend on Thm 0.1.0 — prior reports had phantom edge [20]→[24]; corrected | Def 0.1.2 Dependencies (lines 13–17): only Def 0.1.1, Thm 0.0.3. Thm 0.1.0 in "Derivation Status" only. | — |
| M8.H | **NOTE** | Phys Hyp 0.0.0f used in 4 files with inconsistent ⚠️ markers; no formal cycle with Prop 0.0.40 | [5] line 22, [9] line 45, [13] body, [16] line 27. All informational — not dependency edges to [6]. | — |

---

## Recommendations

1. **[MODERATE — M8.1 fix] Reclassify Thm 0.0.2's Def 0.1.1-Applications reference:** Move the `Definition 0.1.1-Applications §12.3.2 (D = N + 1 formula)` entry from the Dependencies section to a "Cross-references" section, or add the qualifier `(notational reference — independently derivable from standard SU(N) theory)`. This restores acyclicity while preserving the disambiguation achieved by the M8.4 fix.

2. **[MODERATE] Layer documentation:** Either (a) relabel the 6-layer structure as "thematic categories" rather than "layers" (which implies ordering), or (b) redefine layers to match the actual dependency DAG. The note at audit plan line 42 is accurate but insufficiently prominent.

3. **[NOTE] Cross-reference discipline:** When disambiguating cross-references, classify fixes as "dependency" (formal prerequisite) vs "cross-reference" (notational/bibliographic pointer). The M8.4 experience demonstrates that adding file paths to dependency sections can inadvertently create cycles.

4. **[NOTE — M8.H] Standardize Phys Hyp 0.0.0f formatting:** Add the ⚠️ marker consistently to all four files that reference Physical Hypothesis 0.0.0f in their Dependencies sections. Currently [9] Thm 0.0.3 omits the ⚠️ marker while [5] and [16] include it.

---

## JSON Summary

```json
{
  "group": "G1",
  "layer": 1,
  "module": "M8",
  "checks_total": 14,
  "checks_passed": 4,
  "checks_failed": 3,
  "checks_noted": 7,
  "findings": [
    {
      "check_id": "M8.1",
      "result": "FAIL",
      "description": "One formal 3-cycle via [3]→[19] edge: [3]→[19]→[9]→[3]. Documentation-level, not logical — D=N+1 independently derivable.",
      "evidence": "Thm 0.0.2 Dependencies line 40: 'Definition 0.1.1-Applications §12.3.2 (D = N + 1 formula)'. Def 0.1.1 depends on Thm 0.0.3 (line 13). Thm 0.0.3 depends on Thm 0.0.2 (line 44). Cycle introduced by commit 0c6fe73d.",
      "severity": "MODERATE"
    },
    {
      "check_id": "M8.2",
      "result": "FAIL",
      "description": "Layer ordering violated — 4 of 6 layer boundaries have upward or cross-boundary dependencies",
      "evidence": "[7](L2)→[13](L4), [17](L3)→[25](L6), [18](L3)→[25](L6), [13](L4)→[19](L5). Self-documented at audit plan line 42.",
      "severity": "MODERATE"
    },
    {
      "check_id": "M8.3",
      "result": "FAIL",
      "description": "Three L1–L3 files depend on L4–L6 files",
      "evidence": "Thm 0.0.0a(L2)→Thm 0.0.6(L4); Thm 0.0.12(L3)→Thm 1.1.1(L6); Thm 0.0.13(L3)→Thm 1.1.1(L6). All honestly declared.",
      "severity": "MODERATE"
    },
    {
      "check_id": "M8.4",
      "result": "PASS",
      "description": "Declared dependencies are complete — all used results declared with explicit references",
      "evidence": "Thm 0.0.2 includes explicit file path for D=N+1. Thm 0.0.16 Gap-Analysis declared informational. Thm 0.0.6 A0 upgrade correctly separated."
    },
    {
      "check_id": "M8.5",
      "result": "PASS",
      "description": "No phantom dependencies — all declared deps are actually used in proof bodies",
      "evidence": "All 26 files checked. Thm 0.0.15's Def 0.1.2 dep marked 'notational only' — honest and accurate."
    },
    {
      "check_id": "M8.6",
      "result": "PASS",
      "description": "Phase 0 definitions (L5) are free of L3 reconstruction dependencies",
      "evidence": "[19]–[26] depend only on L1, L2, L5, L6, or external results. No L3 dependencies."
    },
    {
      "check_id": "M8.7",
      "result": "PASS",
      "description": "Thm 0.0.9 correctly separates logical prerequisites from consistency targets — Thm 0.0.1 is validation target only",
      "evidence": "Two labeled subsections in dependency header. Thm 0.0.1 appears only under 'Validated Against (Consistency Targets)'."
    },
    {
      "check_id": "M8.A",
      "result": "NOTE",
      "description": "THEMATIC-GROUPS.md table ordering correctly documented as theorem-number order with link to M8 DAG",
      "evidence": "Note in THEMATIC-GROUPS.md references M8 findings for actual dependency ordering."
    },
    {
      "check_id": "M8.B",
      "result": "NOTE",
      "description": "Six G1 files have external dependencies on results outside G1 group",
      "evidence": "[4]→G3, [8]→info-geom, [13]→Thm 0.0.17, [14]→G2/G6, [15]→G2/G3/G8, [26]→G2/G4"
    },
    {
      "check_id": "M8.C",
      "result": "NOTE",
      "description": "Former CRITICAL cycle {[11],[12],[13]} remains resolved — Thm 0.0.6 A0 status upgrade note intact",
      "evidence": "Thm 0.0.6 line 105: blockquote correctly classifies A0 upgrade as non-dependency."
    },
    {
      "check_id": "M8.D",
      "result": "NOTE",
      "description": "M8.4 fix (commit 0c6fe73d) created M8.1 cycle by placing cross-reference in Dependencies section",
      "evidence": "Commit added Def 0.1.1-Apps §12.3.2 to Thm 0.0.2's Dependencies rather than Cross-references."
    },
    {
      "check_id": "M8.E",
      "result": "NOTE",
      "description": "Prior 5-cycle claim downgraded (v7) — [9]→[6] edge is ⚠️ hypothesis note, not formal dependency. Only the 3-cycle is genuine.",
      "evidence": "Thm 0.0.3 line 45: 'Physical Hypothesis 0.0.0f ... now derived in Proposition 0.0.40' — informational provenance, not dependency declaration."
    },
    {
      "check_id": "M8.F",
      "result": "NOTE",
      "description": "Thm 0.0.6 correctly omits Thm 0.0.4 from dependencies (correcting prior report errors)",
      "evidence": "Thm 0.0.6 lines 98–103: lists only [9],[19],[20],[3], Thm 0.0.17"
    },
    {
      "check_id": "M8.G",
      "result": "NOTE",
      "description": "Def 0.1.2 does NOT depend on Thm 0.1.0 — prior reports had phantom edge [20]→[24]; corrected in fifth audit",
      "evidence": "Def 0.1.2 Dependencies (lines 13–17) lists only Def 0.1.1 and Thm 0.0.3. Thm 0.1.0 mentioned in 'Derivation Status' note (lines 7–11) only."
    },
    {
      "check_id": "M8.H",
      "result": "NOTE",
      "description": "Phys Hyp 0.0.0f used in 4 files with inconsistent ⚠️ markers; no formal cycle with Prop 0.0.40 — all are informational notes",
      "evidence": "[5] line 22 (⚠️), [9] line 45 (no ⚠️), [13] body only, [16] line 27 (⚠️). None create dependency edges to [6]."
    }
  ],
  "overall_result": "FAIL"
}
```

---

*Report generated: 2026-03-14 (seventh audit — independent re-verification)*
*Auditor: Claude Opus 4.6 (autonomous agent)*
*Method: Full independent read of all 26 G1 proof files via parallel subagent extraction + direct grep verification of critical edges*
*v7 changes from v6: (1) Downgraded 5-cycle from formal cycle to informal transitive path. (2) Added M8.H finding on Phys Hyp 0.0.0f classification. (3) DAG table now shows ⚠️ markers for Phys Hyp 0.0.0f entries to distinguish them from formal dependency edges. (4) DAG visualization corrected to remove [6] from [11] edge label (Prop 0.0.16a's Phys Hyp 0.0.0f is a hypothesis, not a dep on [6]).*
*Prior reports: initial through sixth audit (all 2026-03-14) — all superseded*
