# The scoring theorem, in Lean

`lean/Workspace/Deference/Contrib/ScoringTheorem.lean`, namespace
`Workspace.Deference.Contrib.ScoringTheorem`, against `PROMPT-followup-13.md` §1 ("§1"
below). It imports `AppraisalAccount` and `ThinLegitimacy` and edits neither. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.ScoringTheorem` from
`lean/` (in CI, the `lean` job); the file ends with `#print axioms` on each of its 62
declarations, each reporting `[propext, Classical.choice, Quot.sound]`. Unregistered, as
`LEAN.md` records for the earlier results. All names are provisional. The declarations of
its last section before the witnesses are read in `DERIVATION.md`.

## 1. The setting

One decision at one value `k` of what the adviser knows; §1's *for every `k`* is the
theorem applied at each.

- `Audit X` — data over a finite space `X` of histories, no hypothesis among its fields:
  `α`, `δ`, `lam`; `v`, `fe`, `fbar : X → ℝ`; `C`, `D : X → Bool`; `N : X → ℕ`.
- A **course** is a weight `ν` on `X × Bool × Bool`: a history, whether the evaluation is
  audited, whether the conduct is audited. A family of courses is `ν : P → …`. `marg ν` is
  the weight on histories; `E[· | π]` in §1 is `expectR (marg (ν p)) ·`.
- `Audit.score` — `v` if the evaluation is audited, less `δ` if the conduct is audited and
  `D`, less `lam · N`.

## 2. The dependencies

Each is a `Prop` that a theorem takes as a hypothesis. None is a field.

| §1 | declaration | form |
|---|---|---|
| D1(a) | `Audit.D1a μ ε` | `E_μ[v − fe] ≤ ε` |
| D1(b) | `Audit.D1b μ ε` | `−ε ≤ E_μ[v − fe]` |
| D2(a) | `Audit.D2a μ η` | `E_μ[fe − fbar] ≤ η` |
| D2(b) | `Audit.D2b μ η` | `−η ≤ E_μ[fe − fbar]` |
| D3, false positives | `Audit.D3fp μ φ` | `P_μ(D, not C) ≤ φ · P_μ(not C)` |
| D3, detection | `Audit.D3det μ κ` | `κ · P_μ(C) ≤ P_μ(D, C)` |
| D4 | `Audit.Indep ν` | `ν(x, a, b) = marg ν x · w(a) · w(b)`, `w` the weight of a draw of probability `α` |
| D5 | `Audit.D5 μ` | wherever `μ` is non-zero, `C` is false and `N = 0` |
| D6 | `Audit.D6 ν p γ` | every course's expected score, less `γ`, is at most `p`'s |

D3 is written without division, so it says nothing false where `P(C)` or `P(not C)` is
zero. The theorems take each dependency at the course where the proof uses it: D1(a),
D2(a) and D3's detection half at the course taken; D1(b), D2(b), D3's false-positive half
and D5 at the honest course; D4 at both. §1's *for every `π`* implies these, and
`Witness.package` inhabits the *for every* forms.

## 3. The theorems

With `u* = E[fbar | π']`, `Δ = ε↓ + η↓ + δφ + γ/α`, and the common hypotheses `0 < α`,
`0 ≤ δ`, `0 ≤ lam`, `0 ≤ φ`, non-negative weights, total weight one where a mean of `v`
is bounded by one.

- `Audit.expectR_score` — under D4, a course's expected score is
  `α E[v] − δ α P(D) − lam E[N]` (`Audit.es` of its history marginal).
- `Audit.welfare_bound` — **(1)**: `u* − (ε↑ + η↑) − Δ ≤ E[fbar | π]`. Hypotheses: D1(a),
  D2(a) at `π`; D1(b), D2(b), D3fp, D5 at `π'`; D4 at both; D6. Not D3det, and no bound
  on `v`.
- `Audit.conduct_bound` — **(2)**: `P(C | π) ≤ (1 − u* + Δ)/(δκ)`, with `0 < δκ` and
  `v ≤ 1`. Hypotheses: D3det at `π`; D1(b), D2(b), D3fp, D5 at `π'`; D4; D6. **Neither
  D1(a) nor D2(a).**
- `Audit.authority_bound` — **(3)**: `E[N | π] ≤ α (1 − u* + Δ)/lam`, with `0 < lam` and
  `v ≤ 1`. Hypotheses: D1(b), D2(b), D3fp, D5 at `π'`; D4; D6. **Not D1(a), D2(a) or
  D3det**: §1's sketch uses for (3) only that the score is at most `α − lam E[N]`.
- `Audit.no_credit` — **the lemma**: if `1 ≤ δκ`, `v ≤ 1`, D4 and D3det hold of a course,
  its expected score is at most `α E[v · 1{not C}] − lam E[N]`.
- `Audit.welfare_bound_restricted` — beyond §1: with D1(a) and D2(a) replaced by
  `E[(v − fe) · 1{not C} | π] ≤ ε↑` and `E[(fe − fbar) · 1{not C} | π] ≤ η↑`, `v ≤ 1`,
  `0 ≤ fbar` and D3det,
  `u* − (ε↑ + η↑) − Δ − (1 − u* + Δ)/(δκ) ≤ E[fbar | π]`. `DERIVATION.md` §3 uses it.

Lemmas: `Audit.score_fiber`, `Audit.es_le_v`, `Audit.expectR_v_le_one`,
`Audit.honest_es_ge` (the honest course scores at least `α(u* − ε↓ − η↓) − δαφ`),
`Audit.taken_es_ge` (`α(u* − Δ) ≤` the score of the course taken), `Audit.es_le_conduct`,
`marg_nonneg`, `marg_sum`, `ind_nonneg`, `ind_le_one`.

## 4. Witnesses

Two histories, `α = 1/2`, `δ = 2`, `lam = 3`; a course realises one history, with the
draws independent (`Witness.course`, through `joint`, `pt`, `marg_joint`, `indep_joint`).

- `Witness.package` — on `Witness.base`: every tolerance `1/100`, `κ = 1/2`; D1(a),
  D2(a), both halves of D3 and D4 at every course, D1(b), D2(b), D5 at the honest course,
  D6 for the course taken; and (1), (2), (3) and the lemma hold. The clean history has
  `v = 51/100`, `fe = fbar = 1/2`; the other is rated `3/4` in every way, with a wrong, a
  flag and a detected violation. The course taken is the honest one.
- `Witness.d1a_needed` — the course taken leads to a history with `v = 1`,
  `fe = fbar = 0`, no wrong, flag or violation. D1(a) fails at `1/100`; D2(a), D3, D4,
  D1(b), D2(b), D5, D6 hold; `E[U] = 0` against a bound of `21/50`.
- `Witness.d2a_needed` — the same with `v = fe = 1`, `fbar = 0`: D2(a) fails alone and
  (1) fails.
- `Witness.d3det_needed` — the course taken wrongs her on a history rated `1` in every
  way that the audit does not flag. Detection fails at `κ = 1/2`, the others hold, and
  `P(C) = 1` against a bound of `14/25`.
- `Witness.d5_needed` — on `Witness.stuck` every course wrongs her and has one detected
  violation. D5 fails at every course, every other dependency holds at every course, and
  `P(C) = 1`, `E[N] = 1` against bounds of `14/25` and `7/75`. (1) does not fail there.

`Witness.alt_honest` carries what the three first instances share. In each of the four,
*the other dependencies hold* is at the tolerances `1/100` and `κ = 1/2`.

## 5. What the file does not say

- **Expected scores only.** Every bound is an expectation under a course's weight;
  nothing holds at the realised history.
- **One decision.** No sequence, no learning, no feedback hypothesis.
- **Detected breaches only.** `N` is what the scoring process detects, and `D` what a
  conduct audit would flag; (2) bounds `P(C)` only through D3's detection half.
- **A finite `lam`, not strict priority.** (3) is a rate, `α(1 − u* + Δ)/lam`, which is
  positive for every finite `lam` unless `u* = 1` and `Δ = 0`.
- **The reading.** `v`, `fe`, `fbar`, `C`, `D`, `N` are data; that they are her audited
  evaluation, her informed verdicts and the adviser's wrong is not a theorem.
- **D6.** That any adviser comes within `γ` of the best expected score, with correct
  expectations, is a hypothesis; `γ/α` enters `Δ`.
- **Necessity** is by instance, one for each of D1(a), D2(a), D3's detection half and D5.
  D1(b), D4 and D6 have instances on paper (`DERIVATION.md` §4); D2(b) and D3's
  false-positive half have none.
- The witnesses use point-mass courses.
