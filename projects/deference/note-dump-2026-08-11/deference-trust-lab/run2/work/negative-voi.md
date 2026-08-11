# negative-voi — Weatherson's 3-world VoI-tightness example, built and kernel-checked

**TODO id:** `negative-voi` · **Modality:** LEAN-CORE · **Status:** **PROVED** (kernel-checked,
sorry-free, axioms clean) + independent EXEC cross-check.

## Artifacts

- **Lean witness (the result):** `deference-trust-lab/run2/lean/negative-voi.lean`
  — `bash …/lean/check.sh …/run2/lean/negative-voi.lean` → exit 0, no errors, **no `sorryAx`**.
  Every theorem's `#print axioms` is a subset of `[propext, Classical.choice, Quot.sound]`
  (the `decide`-proved structural lemmas use only `[propext]`).
- **Exec cross-check:** `deference-trust-lab/run2/work/negative-voi.py`
  — recomputes the witness in exact `Fraction` arithmetic and exhaustively searches all
  3-world S4 experiments. Output: 72 strict-argmax negative-VoI instances, **0** with a
  partitional coarser expert, **0** refinements-of-a-partition that lose value (`ALL CHECKS PASS`).

## What was established (PROVED)

Finite prior frame `W = Fin 3`, uniform prior `π = (1/3,1/3,1/3)`, a menu of two
`[0,1]`-options `O⁰ = (0, 2/3, 1/3)`, `O¹ = (2/3, 0, 0)`, and three experiments
(`Info := W → W → Bool`, the expert's reported information set at each world):

| expert | cells | S4 | partitional |
|---|---|---|---|
| `E1` (finer)   | `{0},{1},{0,2}`   | ✔ `E1_S4` | ✘ `E1_not_partitional` |
| `E2` (coarser) | `{0},{1},{0,1,2}` | ✔ `E2_S4` | ✘ `E2_not_partitional` |
| `Q` (anchor)   | `{0,2},{1},{0,2}` | ✔ `Q_S4`  | ✔ `Q_partitional` |

`E1` refines both `E2` and `Q` (`E1_refines_E2`, `E1_refines_Q`), strictly finer at world 2.

The recommended strategy `recOpt E w` is the **genuine argmax of the expert's own posterior**
`E_π(O^j | E(w))`, computed from `π` and `E`, tie-break "prefer option 0" — the **same rule**
for all three experts. Since the two options share one conditioning cell, argmax of the
posterior = argmax of its numerator `condNum E j w = Σ_{u∈E(w)} π u · O^j u`;
`recOpt_eq_posterior_argmax` (using `condMass_pos`) certifies the division-free `recOpt` is
exactly the argmax of the **normalized** posterior, not a different rule. At world 2 every
expert's choice is a **strict** argmax (`E1_world2_strict`, `E2_world2_strict`), so the
tie-break is never exercised. `Value E := Σ_w π w · O^{recOpt E w}(w)`.

`norm_num` computes `Value E1 = 4/9`, `Value E2 = 5/9`, `Value Q = 4/9`. Headline results:

- **(i) Negative VoI — the strict gap is the CONCLUSION:** `negative_VoI : Value E1 < Value E2`
  (`4/9 < 5/9`). The more-refined, non-partitional `E1` is **strictly worse** than the coarser
  non-partitional `E2`. Value of information is **negative**.
- **(ii) Mandatory partitional near-miss:** `near_miss_partitional : Value Q ≤ Value E1` —
  replacing `E2` by the **partitional** anchor `Q` (which `E1` still refines; same `π`, same
  menu) restores Blackwell–Geanakoplos monotonicity (here `4/9 ≤ 4/9`). The companion
  `partitional_anchor_strictly_dominated : Value Q < Value E2` shows the partition is
  **strictly** beaten by the non-partitional `E2` on the same menu — so the sign genuinely
  tracks partitionality, not the payoffs.
- `tightness_witness` packages everything: (S4 of all three) ∧ (E2 non-partitional, Q
  partitional) ∧ (E1 refines both) ∧ (i) ∧ (ii).

**Mechanism (real information, not a payoff trick).** At world 2 the finer `E1` sees `{0,2}`
and its posterior strictly prefers `O¹` (numerators `2/9 > 1/9`), which pays `0` at world 2.
The coarser `E2` sees `{0,1,2}`; world 1's high `O⁰` payoff pulls its posterior toward `O⁰`
(`1/3 > 2/9`), and `O⁰` pays `1/3` at world 2. The extra information **changes the argmax to a
locally-rational choice that realizes worse** — Weatherson's exact phenomenon.

## Anti-fake compliance

- **No hypothesis-laundering.** The target objects (experiments, Values, the strict gap) never
  appear as hypotheses. No LI theorem, martingale, or asymptotic `≂ₙ` object anywhere — the
  whole file is finite `ℚ` arithmetic over `Fin 3`.
- **Shadow (a) adversarial strategy — defeated:** both experts use the identical
  argmax-of-own-posterior rule; `recOpt_eq_posterior_argmax` proves the numerator-argmax is the
  true normalized-posterior argmax.
- **Shadow (b) assuming "E2 better" — defeated:** `Value E1 < Value E2` is `norm_num`-proved
  from the definitions, a conclusion.
- **Shadow (c) no near-miss — defeated:** the partitional near-miss compiles and flips the
  sign; the EXEC search shows this is universal (a refinement of any partition never loses
  value), so (i) is not an arithmetic artifact.

## Cross-check (EXEC, exhaustive)

Over all 3-world S4 experiment pairs `(Ea refines Eb)` and all menus in `{0,1/2,1}^3` with
**strict argmax** (no ties → tie-break irrelevant): **72** strict negative-VoI instances, of
which **0** had a partitional coarser expert; and **0** refinements of any partitional
experiment ever lost value. This is the converse-direction confirmation that the negative sign
*requires* non-partitionality — exactly what the Lean near-miss certifies on the concrete
witness.

## What was NOT established / scope

- This formalizes only the **finite static value-of-information** comparison. It does **not**
  prove Geanakoplos's general theorem, nor the LI dynamic-martingale route (PROOF-ONLY /
  already in v2 §3 and LeanDeference — untouched here).
- For this `Q` the near-miss is the **equality** `4/9 = 4/9`; the *strict* separation tracking
  partitionality is recorded as `Value Q < Value E2`. (The EXEC search also confirms the
  no-information trivial partition gives `1/2 < 4/9 = Value E1`, a strictly-dominated
  partitional anchor.)
- Off-limits items were **not** re-stated or re-skinned: v2 1.1 prose, Geanakoplos VoI≥0 as a
  theorem, `value_of_CM`/`value_of_argmax`/`payoff_gap_le_l1` (single-expert positive-Value
  route), and the `AntiExpert` single-expert frame. This is a genuinely new **two-expert**
  construction whose driver is non-partitionality.

## Axiom report

All theorems: only `[propext, Classical.choice, Quot.sound]` (or a subset). No `sorryAx`.
Kernel-verified.
