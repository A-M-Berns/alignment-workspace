"""Exact fixtures for the Logical-Induction corrigibility round.

`model.py` loads the 2026-09-09 mediated-repair-dominance model by path; `mismatch.py`
is the directional activation-mismatch algebra on that model's per-path rows;
`compile.py` is the finite compilation of a mediated pair into a bounded constraint
vector over worlds, with the soft selector for finite menus; `settlement.py` is the
occurrence-expiry fixture; `feedback.py` is the margin arithmetic of the feedback
boundary.  All arithmetic is exact (`fractions.Fraction`).
"""
