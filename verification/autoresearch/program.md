# AutoResearch-CG: Research Direction

This file controls what the autonomous research loop focuses on.
Edit this to steer the agent's priorities. The agent reads this at the
start of each iteration to decide what to work on and how.

---

## Current Focus

Strengthen the weakest links in the proof chain. Prioritize:

1. **Phase 6 & 7 gaps** — Scattering theory and renormalization/consistency
   are the least-developed phases. Look for theorems marked 🔸 PARTIAL
   or 🔮 CONJECTURE in these phases.

2. **Cross-phase consistency** — Verify that parameter values used in later
   phases match what was derived in earlier phases. Flag any discrepancies.

3. **Verification freshness** — Re-verify theorems whose verification dates
   are oldest, especially if upstream dependencies have been updated since.

## Rules for the Agent

- **Do not modify established physics** (✅ ESTABLISHED). These are textbook
  results. Focus on novel framework-specific content.
- **Preserve existing verification scripts** that pass. If you need to update
  a script, ensure all existing tests still pass.
- **When strengthening a proof**, identify the weakest step first. Don't
  rewrite entire proofs — make targeted improvements.
- **Always run dimensional analysis** on any equation you modify.
- **Check limiting cases**: every new result must reduce to known physics
  in the appropriate limit.
- **Use PDG 2024 / CODATA 2018 constants** — never invent numerical values.
- **Use R_stella = 0.44847 fm** (observed) for verification, not the
  bootstrap-predicted value.

## What NOT to Do

- Don't restructure proof documents (use /restructure-proof for that)
- Don't modify Lean 4 files (those require separate careful work)
- Don't change the proof numbering system
- Don't add new theorems — focus on strengthening existing ones
- Don't modify the theorem_graph.py structure

## Success Criteria

An iteration is successful if ANY of these improve:
- A 🔸 PARTIAL theorem gets upgraded to 🔶 NOVEL or ✅ VERIFIED
- A verification script that was failing now passes
- A gap identified in a verification report gets resolved
- A dimensional inconsistency gets fixed
- A missing limiting case check gets added and passes

## Notes

_Add your research notes here as the campaign progresses._

---

*Last updated: 2026-03-14*
