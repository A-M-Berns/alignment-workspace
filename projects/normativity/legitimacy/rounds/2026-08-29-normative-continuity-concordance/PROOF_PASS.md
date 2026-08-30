# Normative Continuity — hostile proof pass (29 Aug 2026)

Inputs: `normative_continuity_refined (freeze).tex` / `.pdf`, the frozen Legitimate
Evolution round (`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution`,
origin/main of alignment-workspace), the Answerable Process freeze report
(`answerable_process_freeze_report.md`). Executable fixtures:
`normative_continuity_fixtures.py` (all pass).

## 1. Verdict

**SURVIVES WITH LOCAL REPAIRS.** No countermodel to any theorem; one lemma was
false as literally stated (at a boundary position the theorems never use), one
proof step was under-argued, and one statement was silently weaker than the
frozen LE kernel. All repaired locally. Marked **AGENT-CONSOLIDATED** in the
document's provenance section — explicitly *not* FROZEN / CANONICAL / PROVED /
LEAN-VERIFIED.

**Provenance finding first.** The `.tex` in Downloads was *stale*: all three
`normative_continuity_refined*.tex` files were byte-identical and predate the
freeze PDF, which already had the single wait-responsiveness assumption, the
"adjacent work" paragraph, the acceptance convention, and an expanded step 2.
The TeX was first brought up to the PDF's content, then repaired, then
recompiled (tectonic; no engine had been installed on this machine). The
pre-audit tex/pdf are kept in the session scratchpad.

## 2. Theorem-by-theorem audit

**Grounded Replay (Thm 1).** Holds under Requirement 1 alone. Matches LE's S1+S2
(`grounds ⊆ {o ∈ L_t : Auth(o)}`, `apply ≠ L_t → grounds ≠ ∅`), quantified over
`L_n` rather than LE's `Adm_t` (a restriction, fine). Two deviations found:
(a) LE constrains grounds of *every* accepted edit; the freeze only of changing
ones — harmless for the theorem, since only changing edits issue nodes; not
changed. (b) The freeze did not say `L_n^+` is fresh, so a removed occurrence
could re-enter and "the change through which it entered" was ambiguous. LE's
`issue_t` makes it fresh (readoption is a new occurrence). Added the freshness
clause — restores LE, does not strengthen it.

**Lemma 3 (route loss is permanent).** FALSE as stated at the introduction
position of `d` when a route root is co-opened: `Routes_j(d)=∅` but
`Routes_{j+1}(d)∋t` (fixture B). Restated for `n>j`; proof now cites Req 8.
The theorems only use it for `d ∈ Pre_n(·)`, i.e. `n>j`, so nothing downstream
was affected.

**Persistent-Wait (Thm 2).** Checked step by step against the definitions:
1. reachable resolution ⇒ ready ⇒ work — ✓ (Lemma 6).
2. `Live_{n+1}=Live_n`: a fresh descendant needs a parent in `Live_n`, which
   would resolve — ✓ uses Req 4, 5 and `m ∈ M_n ⇒ m` opened before `n`.
3. no fresh prerequisite on reachable `q`: Req 12 with `Work=∅` — ✓, and Req 7
   then gives `Pre_{n+1}(q) ⊆ Pre_n(q)`.
4. every live route of an unmet reachable prerequisite is reachable — ✓ by
   closure of `Reach` under `⇝`.
5. route sets cannot gain members: a fresh route must be a successor of a live
   route (**needs Req 8**: `T_d ⊆ I_n`, else a late-born root would enter
   without any resolution), and that parent would resolve — ✓.
6–8. everything monotone in a fixed finite set; `Met` monotone (Req 9) — ✓.
   Closure of `Reach_{n+1} ⊆ Reach_n` also needs `Met` persistence (an edge at
   `n+1` was an edge at `n`); now cited.
9–10. closed finite acyclic digraph has a sink; sink not ready ⇒ unmet `d`;
   route would give an out-edge — ✓ (self-loops must count as cycles; stated).
11. persistence by stabilization — ✓ (Lemma 3 no longer needed there, kept as
   alternative).
Unstated-but-used: finiteness of batches (so `O_n`, `Reach_n` finite) and
`n_1 ≥ n_0`; both now explicit. No missing structural assumption.

**Persistent Opportunity (Thm 3).** Contrapositive of Thm 2 plus wait
responsiveness; the old `External(d)` classification carried no logical weight
(hygiene ∘ input = wait responsiveness), confirming the PDF's collapse. ✓

**No Structural Abandonment (Thm 4).** Lemma 2 dichotomy + Thm 3 + Req 11. ✓

**Lemma 4 (feasibility).** ✓ (any fixed tie-break for same-position births).
**Lemma 5 (every issue has a matter).** ✓ but used by no theorem.

Edge cases checked: same-batch open+resolve (impossible: `Res_n ⊆ O_n`,
`Q^+_n ∩ O_n = ∅`); co-opened route roots (Lemma 3 fix); branching/merging
(fixture F); several matters reaching one issue (fixture A: gate binds on the
starving one though the owner is busy); late designation (birth `n+1`, may be
born already closed → NSA case 1); withdraw-then-reintroduce (occurrence
distinct, gate applies); resurrection of routes (impossible: descendants need
parents, designation does not alter `⪯`); `Met` at the same transition as a
withdrawal (both read at the prefix; fixture F); cycles incl. self-loops
(fixture E); standing change in the batch of an opening (Req 2 reads `H_n`,
matches LE phase order A34); standing loss with an open issue (issue persists,
still judged by `κ_q` — the Answerable Process episode-integrity design).

## 3. Dependency table

| Result | Exact hypotheses used | Not used but part of theory |
|---|---|---|
| Grounded Replay | Req 1 (Permit at pre-state, nonempty standing `Auth` grounds on change, exact `L` update, fresh `L^+`); grounds ⊆ `Past_n` | everything else |
| Persistent-Wait | Req 4, 5, 7, 8, 9, 10, 12; finite batches; `M_n` construction (matters are prior issues) | Req 1, 2, 3, 6, 11; compat assumption; `Permit`, `Due`, `Continue`, `Designate` semantics; Lemma 5 |
| Persistent Opportunity | PW hypotheses + wait responsiveness | same; `External(d)` is dispensable |
| No Structural Abandonment | PO hypotheses + Req 11 + Lemma 2 (Req 4, 5) | Req 1, 2, 3, 6; state continuity; Grounded Replay |

Grounded Replay and state continuity are indeed not load-bearing after Thm 1;
the standing layer meets the issue layer only at Req 2. Theorem statements now
name exactly these requirements.

## 4. Countermodels / fixtures (`normative_continuity_fixtures.py`)

- **A — rotating prerequisite (regression).** `a` (matter m1) waits via `d0`
  on `b1`; `b1` is a descendant of busy matter `b` whose sibling `c` is ready
  forever. From `n=2` the process withdraws `e_{k}` from `b1` and adds `e_{k+1}`.
  Live gate: admitted (`b1 ∈ Live(b)` only, `b` has work); `Work_n(m1)=∅` for
  all `n≥2`, `m1` live forever, and `NoRoute_n(m1)` moves every step — PW's
  conclusion fails. Reach gate: rejected at `n=2` on `(b1, m1)` by Req 12 alone;
  every other requirement holds on the trace.
- **B — co-opened route root.** `Routes_1(d)=∅`, `Routes_2(d)={t}`: Lemma 3
  needs `n>j`.
- **C — genuine no-route wait.** PW returns `d`.
- **D — route extinction after introduction.** `t` resolves terminally (an
  opportunity), then `d` is no-route forever.
- **E — 2-cycle** counts as work at every position.
- **F — branch, merge, same-transition Met/withdraw, designation.**

## 5. Exact edits to the freeze TeX

PDF-sync (content the PDF already had): §1.1 prose, acceptance convention,
§3 prose + Lemma 1 proof + post-Replay paragraphs, attention remark, wait
responsiveness (single assumption), PO statement/proof, §10 sentences and
labelled arrow, §11 `Front→Work` rename note and "Adjacent work" paragraph.

Audit repairs: Req 1 freshness clause (LE conformance); `AddPre` ownership
`q_d=q`; Lemma 3 restated for `n>j` with proof and remark; Thm 2 hypotheses
named, proof rewritten with the same five steps but every implication cited
(`n_1≥n_0`, Req 8, Req 9, closure, self-loops, stabilization); Thm 1/3/4
hypotheses named; new §11 paragraph "Which requirements each theorem uses";
"Audit status" paragraph with the AGENT-CONSOLIDATED label and its meaning.
No architectural or stylistic change. Recompiled: 14 pages, no unresolved refs.

## 6. Remaining proof obligations

- Everything is still a paper proof; nothing is registered or Lean-checked.
- The tex/pdf drift means the *newer* prose additions (acceptance convention,
  §3 prose) have only one adversarial pass (this one).
- Wait responsiveness is an assumption with two named sufficient conditions;
  neither is derived here (coverage theory / prerequisite-hygiene discipline).
- The "Answerable Process" report and the freeze differ in one design point
  worth recording at concordance: the AP report has NS at both claim and matter
  grain; the freeze has matter grain only, with reach-following in `Work`.
  Not a defect of the freeze's theorems, but the concordance should say why.

## 7. Recommendation

Ready for provenance concordance. For Lean: port in the order Grounded Replay
(Req 1 only, a list induction) → the issue-layer structures with fixtures A–F
as `example`s → Persistent-Wait. The reconstruction in step 2 of the proof is
now explicit enough to be the Lean proof skeleton.
