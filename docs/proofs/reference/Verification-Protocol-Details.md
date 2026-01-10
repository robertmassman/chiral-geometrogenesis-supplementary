# Verification Protocol Details

This document provides detailed instructions for independent verification of Chiral Geometrogenesis proofs. See [CLAUDE.md](../CLAUDE.md) for the core verification protocol and when verification is required.

---

## Verification Agent Instructions

The verification agent MUST:

1. **Work independently:** Do not simply read and approve. Re-derive key results from scratch.

2. **Be adversarial:** Actively try to break the proof. Ask "what if this assumption is wrong?"

3. **Check numerical values:** Don't trust calculations — redo them independently.

4. **Verify references:** If a result is cited, check that the source actually says that.

5. **Test edge cases:** What happens at boundaries, limits, special values?

6. **Look for fragmentation:** Does this theorem use mechanisms consistently with the rest of the framework?

7. **Be honest:** A verification that finds no issues should be rare. Most work has something that can be improved.

---

## Handling Verification Results

### If Verification PASSES (No Errors Found)

```markdown
## Verification Record

**Verified by:** Independent Agent
**Date:** [Date]
**Scope:** [What was checked]
**Result:** ✅ VERIFIED

**Checks Performed:**
- [ ] Logical validity — confirmed
- [ ] Mathematical correctness — re-derived equations [X], [Y], [Z]
- [ ] Dimensional analysis — all terms consistent
- [ ] Limiting cases — tested [list limits]
- [ ] Framework consistency — checked against theorems [list]
- [ ] Physical reasonableness — no pathologies found

**Notes:** [Any observations]
```

### If Verification FAILS (Errors Found)

1. **Document the errors precisely:**
```markdown
## Verification Record

**Verified by:** Independent Agent
**Date:** [Date]
**Result:** ❌ ERRORS FOUND

**Error 1:** [Location] — [Description]
   - Expected: [What should be]
   - Found: [What is written]
   - Impact: [How this affects the result]

**Error 2:** ...
```

2. **Return to Author Agent for correction**

3. **Re-verify after corrections** (verification agent should check fixes)

4. **Iterate until verified**

### If Verification is PARTIAL (Warnings/Suggestions)

```markdown
## Verification Record

**Result:** ⚠️ VERIFIED WITH WARNINGS

**Warnings:**
1. [Issue that isn't definitively wrong but is concerning]

**Suggestions:**
1. [Improvement that would strengthen the proof]

**Recommendation:** [Proceed with caution / Address before publication / etc.]
```

---

## Verification Depth by Theorem Status

| Current Status | Target Status | Required Verification |
|----------------|---------------|----------------------|
| 🔮 CONJECTURE | 🔸 PARTIAL | Basic logic check |
| 🔸 PARTIAL | 🔶 NOVEL | Full independent derivation |
| 🔶 NOVEL | ✅ ESTABLISHED | Full verification + literature cross-check |
| Any | Publication-ready | Multiple independent verifications |

---

## Specific Verification Requirements by Phase

### Phase 0 (Pre-Geometric Foundations)
- Verify no circular dependencies with later phases
- Check that definitions don't implicitly assume spacetime
- Confirm internal time λ is consistently defined

### Phase 1-2 (Dynamics)
- Verify SU(3) calculations against standard tables
- Check Kuramoto stability analysis eigenvalues
- Confirm anomaly coefficients match ABJ

### Phase 3 (Mass Generation)
- Independently derive mass formulas
- Verify numerical predictions against PDG values
- Check Higgs equivalence mapping explicitly

### Phase 4 (Matter)
- Verify topological charge calculations
- Check Bogomolny bounds
- Confirm baryon asymmetry η calculation

### Phase 5 (Gravity)
- Verify Wick rotation validity conditions
- Check emergent metric reduces to Schwarzschild
- Confirm Newton's constant derivation

### Phase 7 (Consistency)
- This entire phase IS verification — apply extra scrutiny
- Multiple independent checks required
- Any unitarity/renormalizability claim needs adversarial review

---

## Multi-Agent Verification for Critical Results

For theorems marked as **CRITICAL** in the proof plan, use multiple verification agents:

1. **Mathematical Verification Agent:** Focus on algebra, calculus, proofs
2. **Physics Verification Agent:** Focus on physical interpretation, limits, consistency
3. **Literature Verification Agent:** Focus on citations, prior work, experimental data

A critical theorem is only ✅ COMPLETE when ALL THREE pass.

**Critical theorems requiring multi-agent verification:**
- Theorem 0.2.2 (Internal Time Emergence) — breaks bootstrap
- Theorem 3.1.1 (Phase-Gradient Mass Generation Mass Formula) — core mechanism
- Theorem 4.2.1 (Chiral Bias in Soliton Formation) — baryogenesis
- Theorem 5.2.1 (Emergent Metric) — gravity emergence
- Theorem 5.1.2 (Vacuum Energy Density) — cosmological constant
- Theorem 3.2.1 (Low-Energy Equivalence) — SM recovery

---

## Verification Log

Maintain a verification log tracking all verifications:

```markdown
# Verification Log

| Theorem | Date | Verifier | Result | Notes |
|---------|------|----------|--------|-------|
| 0.2.2 | [Date] | Agent-V1 | ✅ | Re-derived time emergence |
| 3.1.1 | [Date] | Agent-V2 | ⚠️ | Warning on coefficient |
| 3.1.1 | [Date] | Agent-V3 | ✅ | After correction |
```

---

## Escalation Protocol

If Author Agent and Verification Agent disagree:

1. **Document the disagreement precisely**
2. **Spawn a third "Arbitration Agent"** to evaluate both positions
3. **If still unresolved:** Flag for human review
4. **Never override verification** without documented justification
