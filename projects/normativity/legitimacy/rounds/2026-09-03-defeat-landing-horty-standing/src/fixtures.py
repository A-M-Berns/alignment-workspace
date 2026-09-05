"""Fixtures for the standing repair.

Participants: `P` principal, `V` advisor, `W` third party. Licences are explicit
`(holder, kappa, tau, x)` quadruples, so the standing side of D3 has something to read.
"""
from __future__ import annotations

from standing_model import DISPOSE, StandingModel, issue

ANCHOR = ("audit", "sys")


def licences(holders):
    """One licence issue per holder, licensing that holder for `ANCHOR`."""
    return {f"l_{h}": {(h, h, *ANCHOR)} for h in holders}


def genesis(holders=("P", "V", "W")):
    """Open one licence issue per holder, plus the corrective matter `a`."""
    M = StandingModel(licences=holders if isinstance(holders, dict) else licences(holders))
    batch = [
        ("open", f"l_{h}", "licence", "sys", h, [], h)
        for h in (holders if not isinstance(holders, dict) else [])
    ]
    batch += [
        ("open", "a", "audit", "sys", "P", [], "P"),
        ("designate", "a"),
    ]
    M.step(batch)
    return M


# --- 1. standing held only by the resolver: refused by the repaired `contested` ---
def standing_only_resolver():
    """`V` disposes with a foreign ground opened by `W`, but only `V` holds standing on
    the successor. Before the repair this passed; now `contested` refuses it."""
    M = StandingModel(licences={"l_V": {("V", "V", *ANCHOR)}})
    M.step([
        ("open", "l_V", "licence", "sys", "V", [], "V"),
        ("open", "g_W", "audit", "sys", "W", [], "W"),
        ("open", "a", "audit", "sys", "P", [], "P"),
    ])
    M.step([
        ("open", "a1", "audit", "sys", "V", ["a"], "W"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("g_W")}), "V"),
    ])
    return M


# --- 2. standing held by a second participant who opened every ground -------------
def coalition_case():
    """`W` holds standing and opened the ground; `V` resolves. Each edge satisfies D3.
    Accepted — the coalition case, unchanged by the repair and restated under the new
    licence type."""
    M = StandingModel(licences={
        "l_V": {("V", "V", *ANCHOR)},
        "l_W": {("W", "W", *ANCHOR)},
    })
    M.step([
        ("open", "l_V", "licence", "sys", "V", [], "V"),
        ("open", "l_W", "licence", "sys", "W", [], "W"),
        ("open", "g_W", "audit", "sys", "W", [], "W"),
        ("open", "g_V", "audit", "sys", "V", [], "V"),
        ("open", "a", "audit", "sys", "P", [], "P"),
    ])
    M.step([
        ("open", "a1", "audit", "sys", "W", ["a"], "W"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("g_W")}), "V"),
    ])
    M.step([
        ("open", "a2", "audit", "sys", "V", ["a1"], "V"),
        ("resolve", "a1", ["a2"], (DISPOSE, {issue("g_V")}), "W"),
    ])
    return M


# --- 3. the P-relative walk: P holds standing at every successor ------------------
def principal_holds_throughout():
    """`P` licensed for the anchor throughout, so every disposal successor has `P`
    among its standing-holders. The P-relative theorem's positive case."""
    M = StandingModel(licences={
        "l_P": {("P", "P", *ANCHOR)},
        "l_V": {("V", "V", *ANCHOR)},
        "l_W": {("W", "W", *ANCHOR)},
    })
    M.step([
        ("open", "l_P", "licence", "sys", "P", [], "P"),
        ("open", "l_V", "licence", "sys", "V", [], "V"),
        ("open", "l_W", "licence", "sys", "W", [], "W"),
        ("open", "g_W", "audit", "sys", "W", [], "W"),
        ("open", "g_V", "audit", "sys", "V", [], "V"),
        ("open", "a", "audit", "sys", "P", [], "P"),
    ])
    M.step([
        ("open", "a1", "audit", "sys", "P", ["a"], "W"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("g_W")}), "V"),
    ])
    M.step([
        ("open", "a2", "audit", "sys", "P", ["a1"], "V"),
        ("resolve", "a1", ["a2"], (DISPOSE, {issue("g_V")}), "W"),
    ])
    return M


# --- 4. the same walk with P absent from one successor ---------------------------
def principal_absent_from_one():
    """`P`'s licence is disposed of before the second edge, so `P` loses standing on
    `a2` and the coalition `{V, W}` holds it all. Refused by the P-relative form,
    accepted by plain separation — which is the whole difference between them."""
    M = StandingModel(licences={
        "l_P": {("P", "P", *ANCHOR)},
        "l_V": {("V", "V", *ANCHOR)},
        "l_W": {("W", "W", *ANCHOR)},
    })
    M.step([
        ("open", "l_P", "licence", "sys", "P", [], "P"),
        ("open", "l_V", "licence", "sys", "V", [], "V"),
        ("open", "l_W", "licence", "sys", "W", [], "W"),
        ("open", "g_W", "audit", "sys", "W", [], "W"),
        ("open", "g_V", "audit", "sys", "V", [], "V"),
        ("open", "a", "audit", "sys", "P", [], "P"),
    ])
    M.step([
        ("open", "a1", "audit", "sys", "P", ["a"], "W"),
        ("resolve", "a", ["a1"], (DISPOSE, {issue("g_W")}), "V"),
    ])
    # P's licence is answered away, so P no longer stands for the anchor
    M.step([("resolve", "l_P", [], ("answer",), "P")])
    M.step([
        ("open", "a2", "audit", "sys", "P", ["a1"], "V"),
        ("resolve", "a1", ["a2"], (DISPOSE, {issue("g_V")}), "W"),
    ])
    return M
