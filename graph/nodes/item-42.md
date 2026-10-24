---
id: item-42
kind: leaf
leaf_kind: task
action: "Execute item 42 per its deliverable shape and acceptance check: An efficiently presentable sufficient row family for coherence."
who: agent
item: "42"
title: "An efficiently presentable sufficient row family for coherence"
section: "Normativity line — traderized enforcement"
maintainer_order: 24
difficulty: "open"
heading_notes: " — *narrowed by the proof-closing pass*"
project: normativity
dispatchable: true
item_status: open
deliverable: "`enumeration-verified` over a stated fragment family for a positive answer; `witness-checked` for a negative one."
acceptance: "the house enumeration checker generates the fragment's plausible worlds and confirms the claimed containment pointwise."
author: "@smithy-verity"
size: M
size_reason: "one item entry of 300 words"
version: 1
---
## Statement
Item 42, An efficiently presentable sufficient row family for coherence, is delivered in the shape its entry states: `enumeration-verified` over a stated fragment family for a positive answer; `witness-checked` for a negative one.

## Source
PRIORITIES.md, item 42 (An efficiently presentable sufficient row family for coherence); its context: `.../2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md` §§3–4, and its `src/deduction.py`.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Enforcing the coherence polytope of a deductive stage needs its facet system,
whose vertex set is the plausible worlds of the priced fragment — up to `2^|Φ|`
of them. The cheap alternative, the affine relations among priced sentences, is
strictly weaker: on a four-sentence Boolean fragment it admits twenty-four
incoherent grid points at denominator three, one of which prices a conjunction
above a conjunct.

The item is the gap between them. Is there a row family, computable in time
polynomial in the fragment, whose region is strictly between the affine relations
and the coherence polytope and whose residual incoherence admits a bound? A
negative answer — that any polynomially presentable family leaves a violation
bounded away from zero — is equally wanted and would say that finite-date
coherence is intrinsically expensive.

*Deliverable shape:* `enumeration-verified` over a stated fragment family for a
positive answer; `witness-checked` for a negative one.
*Acceptance check:* the house enumeration checker generates the fragment's
plausible worlds and confirms the claimed containment pointwise.
*Context:* `.../2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md`
§§3–4, and its `src/deduction.py`.
*Narrowed:* the proof-closing pass removed the *approximation* half of the question.
The **exact dual-distance presentation** — `src/coherence.py`, `PROOF_CLOSURE.md` §V —
is a finite rational row family, computable from the fragment's plausible worlds and
independent of the price, whose largest violation *is* `dist_∞(P, K)`, with no mesh and
no Hoffman constant; it is world-inclusive by construction, so it costs nothing in
liability however large it is. What remains is exactly the complexity question: that
family is `computable`, and nothing bounds it better than
`binom(2^{|Φ|} + |V|, |Φ|+1)`, against observed counts of 11 at `|Φ| = 3` and 17 at
`|Φ| = 4`. So a positive answer must now beat a *known-exact* baseline rather than
compete with an approximation, and a negative answer must rule out polynomial
presentability of that baseline.
