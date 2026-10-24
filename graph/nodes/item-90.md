---
id: item-90
kind: leaf
leaf_kind: task
action: "Execute item 90 per its deliverable shape and acceptance check: The generability certificate of the soft-weighted finite-menu constraint."
who: agent
item: "90"
title: "The generability certificate of the soft-weighted finite-menu constraint"
section: "Deference line — second wave"
maintainer_order: 86
difficulty: "open"
heading_notes: " — *narrowed 2026-09-15: T3's own certificate is constructed (`LICorrigibilityCertificate.lean`); what remains is T3′'s*"
project: deference
dispatchable: true
item_status: open
deliverable: "Lean declarations discharging `LUVCombinationSyntax` for the soft-weighted combination of a polynomial-size generated menu of compiled pairs, audited to the three axioms, with the T3′ endpoint stated in the form of `li_bypass_le_compiled`."
acceptance: "`python3 tests/run.py` green; Lean audits clean."
work:
  - {kind: decision, ref: 2026-09-15--corrigibility-nucleus-landed-item-90-split}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 323 words"
version: 1
---
## Statement
A solution to item 90 ships the certificate, or the exact combinator the pinned suite lacks.

## Source
PRIORITIES.md, item 90 (The generability certificate of the soft-weighted finite-menu constraint); its context: `LUV_COMPILATION.md` §2 and §4, `LI_CORRIGIBILITY.md` §3 of the round; the pinned formalization's `Construction/Witnesses/LUVSyntax.lean` for the certificate shape and its own `triangularSoftmaxPoly` for a fold of the same kind.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The li-corrigibility round (`projects/deference/rounds/2026-09-15-li-corrigibility/`)
learns the corrigibility inequality by `thm:expprovind`, and its landing pass constructs
the pinned-interface generability certificate for the compiled pair constraint
(`MediatedPair.syntaxOf`, `li_bypass_le_compiled`, inhabited by `Witness.li_instance`).
The finite-menu form T3′ — `max_{q ∈ Q_n} [E_n(U_q) − E_n(U_𝔠q) − λ E_n(G_δ,q) − E_n(G_ρ,q)
− E_n(G_M,q)] ≲_n 0` over a polynomial-size efficiently generated menu — is proved
through the near-argmax weighting whose kernel is Lean (`softWeight_aggregate_ge`,
`uniform_of_soft`) but whose `P`-generability is paper-level: the weights are
expressible features folded over the growing menu (`max` chains, a sum, one safe
reciprocal, and the mesh-expectation scores of every pair), and the pinned splice suite
mirrors the feature constructors one at a time (`RpnSpliceStream.serialize_*`) with a
variable-width fold only for token concatenation (`concatVar`).  Build the feature-chain
fold and the `LUVCombinationSyntax` of `(B'_n)`, so that T3′ is mechanized end to end as
T3 is.

*Deliverable shape:* Lean declarations discharging `LUVCombinationSyntax` for the
soft-weighted combination of a polynomial-size generated menu of compiled pairs, audited
to the three axioms, with the T3′ endpoint stated in the form of `li_bypass_le_compiled`.
*Acceptance check:* `python3 tests/run.py` green; Lean audits clean.

*Context:* `LUV_COMPILATION.md` §2 and §4, `LI_CORRIGIBILITY.md` §3 of the round; the
pinned formalization's `Construction/Witnesses/LUVSyntax.lean` for the certificate shape
and its own `triangularSoftmaxPoly` for a fold of the same kind.
*Consumed by:* T3′ of the round; any registration of the finite-menu theorem.
*A solution ships:* the certificate, or the exact combinator the pinned suite lacks.

*2026-09-25 (gate-is-legitimacy round):* the segment gate's asymptotic half is the
classification table read through Expectation Provability Induction
(`GateIsLegitimacy.li_manip_le`, an instance of `li_gated_le`): a row theorem "pattern ⇒
¬`Counted`" is the per-world hypothesis, and what the theory must contain is the
consultation model's semantics, the decidable checker's verdict and the declared reference.
What this item's shape now also covers: the `P`-generability of the gated securities —
that the checker's verdict and the model's run are expressible features — beside T3′'s
weighting.  The finite-time half needs none of this (`li_gate_finite`).
