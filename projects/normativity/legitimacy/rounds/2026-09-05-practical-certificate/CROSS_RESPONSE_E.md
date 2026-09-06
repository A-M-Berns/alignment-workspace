# Headline exposure loss and edge response loss

## Typing gap

The finite Progress theorem's headline statistic uses one loss `ell(e)` for each
evaluated exposure.  `PracticalCert` bounds the response loss
`Lambda_es(Pi_s)` on an exposure/service edge.  These are different types; the latter
cannot replace the former without an adapter premise.

Fix a finite exposure set `E`, service set `S`, evaluation probability `mu`,
subtransport `T`, and loss bound `D`.  Require

```text
0 <= ell(e) <= D                                      for every evaluated e
T(e,s) > 0  ⇒  ell(e) <= Lambda_es(Pi_s)              for every supported edge
sum_s T(e,s) <= mu(e)                                 for every evaluated e
```

Equality `ell(e)=Lambda_es(Pi_s)` is stronger than the proof needs.  Dominance permits
an edge response metric to be conservative or to include additional evaluation loss.
The inequality must still cite the same exposure anchor, evaluation protocol, and
response receipt as the edge certificate.

## Placement

This is an **evaluation/transport adapter condition**, provisionally
`HeadlineToEdgeDominance`.  It does not belong inside `PracticalCert`:

- `PracticalCert` controls `Lambda_es(Pi_s)` by operative defect and edge constants;
- `HeadlineToEdgeDominance` connects the headline evaluation readout `ell(e)` to that
  edge loss;
- transport support determines which comparisons are required and which mass is
  residual.

Putting the clause inside `PracticalCert` would conflate external response semantics
with the choice of headline evaluation statistic.  Making Progress edge-indexed would
remove the gap, but would change its subject from exposure outcomes to service-edge
receipts and would count a split exposure once per transported edge unless a new
normalization were imposed.  The adapter is the smaller repair.

## Composition theorem

Let

\[
 r=1-\sum_{e,s}T(e,s).
\]

The new Lean theorem `headline_loss_from_edge_losses` proves

\[
 \sum_e\mu(e)\ell(e)
 \le \sum_{e,s}T(e,s)\Lambda_{es}(\Pi_s)+Dr.
\]

For each exposure, split `mu(e)` into transported row mass and unmatched mass.  On
positive transport edges use `ell(e)<=Lambda_es(Pi_s)`; on unmatched mass use
`ell(e)<=D`.  Nonnegativity of `ell(e)` is part of the public loss typing and ensures
the headline statistic is a loss, although this upper-bound proof uses only
`ell(e)<=D`, nonnegative transport, and nonnegative row residual.

Composing with `PracticalCert` gives

\[
 \sum_e\mu(e)\ell(e)
 \le \sum_{e,s}T(e,s)(M_{es}d_s+\epsilon_{es})+Dr,
\]

after which the existing column-amplification and uptake bounds apply.

## Evidence status

- `HeadlineToEdgeDominance`: **proposed definition/interface**.
- `headline_loss_from_edge_losses`: **lean-proved**, conditional on the displayed
  subtransport, bounded-loss, and support-dominance premises.
- `headline_loss_from_edge_losses_inhabited`: **lean-proved** exact witness with two
  exposures and one service; the zero-loss exposure is transported and the unit-loss
  exposure contributes `D/2` residual.
- Authenticity of `ell`, `Lambda`, and their shared anchor: **ambient assumption**.

No theorem here establishes that a concrete response evaluator satisfies the dominance
premise.  That remains part of the external evaluation/transport bill.
