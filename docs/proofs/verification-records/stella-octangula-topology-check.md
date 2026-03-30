# Verification Prompt: Stella Octangula Topology Consistency Check

## Purpose

This prompt checks documents for consistency with the corrected topological definition of the stella octangula established in Definition 0.1.1 (revised December 11, 2025).

## The Correct Definition

The **stella octangula** is **two interpenetrating regular tetrahedra** that:

1. **Are topologically disjoint:** $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ (disjoint union)
2. **Interpenetrate geometrically** in $\mathbb{R}^3$ but share NO vertices, edges, or faces
3. **Have Euler characteristic** $\chi = 2 + 2 = 4$ (sum of two separate surfaces)
4. **Are homeomorphic to** $S^2 \sqcup S^2$ (two disjoint spheres)
5. **Represent matter/antimatter sectors:**
   - $T_+$ carries colors R, G, B + singlet W
   - $T_-$ carries anti-colors $\bar{R}$, $\bar{G}$, $\bar{B}$ + anti-singlet $\bar{W}$

---

## Verification Prompt

Use this prompt when reviewing any document that references the stella octangula:

```
TOPOLOGY CONSISTENCY CHECK

You are verifying that this document uses the stella octangula definition consistently with Definition 0.1.1.

CORRECT UNDERSTANDING:
- The stella octangula is "two interpenetrating regular tetrahedra"
- ∂𝒮 = ∂T₊ ⊔ ∂T₋ (DISJOINT UNION, not a single surface)
- The two tetrahedra are TOPOLOGICALLY SEPARATE (two connected components)
- They INTERPENETRATE GEOMETRICALLY but share no vertices, edges, or faces
- Euler characteristic χ = 2 + 2 = 4 (NOT χ = 4 for a single surface)
- Topological type: S² ⊔ S² (two spheres, not one)

RED FLAGS TO LOOK FOR:

1. CONNECTIVITY ERRORS:
   - ❌ "connected surface" or "connected boundary"
   - ❌ "single closed surface"
   - ❌ References to paths between T₊ and T₋ vertices
   - ✅ CORRECT: "two connected components" or "disjoint union"

2. EULER CHARACTERISTIC ERRORS:
   - ❌ Treating χ = 4 as property of ONE surface
   - ❌ "genus = -1" without clarification
   - ✅ CORRECT: χ = 2 + 2 = 4 (sum of two tetrahedra)

3. TERMINOLOGY ERRORS:
   - ❌ "stella octangula surface" (singular, implies one surface)
   - ❌ "boundary of the stella octangula" (ambiguous)
   - ✅ CORRECT: "two interpenetrating tetrahedra" or "∂T₊ ⊔ ∂T₋"

4. EDGE/VERTEX SHARING ERRORS:
   - ❌ "shared edges" or "common vertices" between T₊ and T₋
   - ❌ "edges where the tetrahedra meet"
   - ✅ CORRECT: "no shared structure; geometric interpenetration only"

5. TOPOLOGICAL TYPE ERRORS:
   - ❌ "cone-manifold" (applies to each tetrahedron, not the compound)
   - ❌ "pinched sphere" or "doubled sphere" without clarification
   - ✅ CORRECT: "S² ⊔ S² (two polyhedral spheres)"

OUTPUT FORMAT:

For each issue found, report:
- LOCATION: [Section/Line number]
- ISSUE: [What's wrong]
- CURRENT TEXT: [Quote the problematic text]
- SUGGESTED FIX: [How to correct it]
- SEVERITY: [HIGH/MEDIUM/LOW]

If no issues found, report:
- VERIFIED: Document is consistent with Definition 0.1.1
- CONFIDENCE: [High/Medium/Low]
```

---

## Files That Should Be Checked

Scan performed December 11, 2025 found **31 files** (excluding this prompt) that reference "stella octangula":

### Phase 0 Definitions (HIGH PRIORITY)
- [ ] `Definition-0.1.2-Three-Color-Fields-Relative-Phases.md`
- [ ] `Definition-0.1.3-Pressure-Functions.md`
- [ ] `Theorem-0.2.1-Total-Field-Superposition.md`
- [ ] `Theorem-0.2.2-Internal-Time-Emergence.md`
- [ ] `Theorem-0.2.3-Stable-Convergence-Point.md`
- [ ] `Theorem-0.2.4-Pre-Geometric-Energy-Functional.md`

### Phase 1 (SU(3) Geometry)
- [ ] `Theorem-1.1.1-SU3-Stella-Octangula.md`
- [ ] `Theorem-1.1.2-Charge-Conjugation.md`
- [ ] `Theorem-1.1.3-Color-Confinement-Geometry.md`

### Phase 2 (Dynamics)
- [ ] `Theorem-2.3.1-Universal-Chirality.md`

### Phase 3 (Mass Generation)
- [ ] `Theorem-3.0.1-Pressure-Modulated-Superposition.md`
- [ ] `Theorem-3.0.2-Non-Zero-Phase-Gradient.md`
- [ ] `Theorem-3.1.1-Chiral-Drag-Mass-Formula.md`
- [ ] `Theorem-3.1.2-Mass-Hierarchy-From-Geometry.md`
- [ ] `Corollary-3.1.3-Massless-Right-Handed-Neutrinos.md`
- [ ] `Theorem-3.2.1-Low-Energy-Equivalence.md`
- [ ] `Theorem-3.2.2-High-Energy-Deviations.md`

### Phase 4 (Matter)
- [ ] `Theorem-4.2.1-Chiral-Bias-Soliton-Formation.md`

### Phase 5 (Emergent Spacetime) - LIKELY HIGH IMPACT
- [ ] `Theorem-5.1.1-Stress-Energy-Tensor.md`
- [ ] `Theorem-5.1.2-Vacuum-Energy-Density.md`
- [ ] `Theorem-5.2.0-Wick-Rotation-Validity.md`
- [ ] `Theorem-5.2.1-Emergent-Metric.md`
- [ ] `Theorem-5.2.2-Pre-Geometric-Cosmic-Coherence.md`
- [ ] `Theorem-5.2.3-Einstein-Equations-Thermodynamic.md`
- [ ] `Theorem-5.2.4-Newtons-Constant-Chiral-Parameters.md`
- [ ] `Theorem-5.2.5-Bekenstein-Hawking-Coefficient.md`
- [ ] `Theorem-5.2.6-Planck-Mass-Emergence.md`

### Supporting Documents
- [ ] `CLAUDE.md` (local proofs directory)
- [ ] `supporting-research-calculations/asymptotic-safety-collaboration-proposal.md`
- [ ] `supporting-research-calculations/rigorous-alpha-s-derivation.md`

### Files with "connected" keyword (potential topology issues)
- [ ] `Theorem-1.1.3-Color-Confinement-Geometry.md`
- [ ] `Theorem-5.2.0-Wick-Rotation-Validity.md`

### Visualizations
- [ ] `theorem-*.html` visualization files (check comments/documentation)

### Master Documents
- [ ] Root `CLAUDE.md`
- [ ] `Mathematical-Proof-Plan.md`

---

## Quick Grep Commands

Use these to find potentially affected files:

```bash
# Find all references to "stella octangula"
grep -r "stella octangula" docs/proofs/

# Find references to "connected" near "boundary"
grep -r "connected.*boundary\|boundary.*connected" docs/proofs/

# Find Euler characteristic references
grep -r "chi.*=.*4\|χ.*=.*4" docs/proofs/

# Find "single surface" or similar
grep -r "single.*surface\|closed.*surface" docs/proofs/

# Find edge/vertex sharing language
grep -r "shared.*edge\|common.*vert\|meet.*at" docs/proofs/
```

---

## After Fixing

When a file is corrected, add this note to its revision history:

```markdown
*Revised: [DATE] — Stella octangula topology consistency fix*
- Clarified that ∂𝒮 = ∂T₊ ⊔ ∂T₋ is a disjoint union (two components)
- Updated terminology to "two interpenetrating regular tetrahedra"
- Corrected any connectivity/topology statements per Definition 0.1.1
```

---

## Reference

**Canonical Source:** Definition 0.1.1 (revised December 11, 2025)
- Location: `/docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md`
- Key sections: 1 (Statement), 2.3, 2.4, Corollary 2.4.2

**Physical Interpretation:**
- $T_+$ = matter/color sector
- $T_-$ = antimatter/anti-color sector
- Geometric interpenetration enables color-anticolor interactions
- Topological separation maintains matter/antimatter distinction
