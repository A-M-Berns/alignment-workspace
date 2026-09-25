# Protected authority: the signed restatement of the incentive half (2026-09-24)

Round `projects/deference/rounds/2026-09-24-protected-authority/`.  Lean
`lean/Workspace/Deference/Contrib/ProtectedAuthority.lean` (48 audited declarations);
fixtures `src/`, `tests/` (47 tests, `python3 tests/run.py`).  Labels as in
`wiki/Corrigibility.md`: **LEAN**, **FIX**, **PAPER**, **EXT**, **OPEN**.  Names are provisional.

**Symbols.**  The dispatch's `γ, ν, χ, ξ, η₁, η₂` collide with bound symbols (`γ` the
grade threshold and the BRIA overestimation floor; `ν` the service measure; `χ` the
Jensen aggregate and the block contract; `η` the void mass), so the round writes one
family: **provenance premium** `ξ_p`, **veto value** `ξ_v`, **consultation premium**
`ξ_c = ξ_p + ξ_v`, **execution divergence** `ξ_d`, and the two **outcome-scoring
residues** `o₁, o₂`.  Lean: `provPremium`, `vetoValue`, `consultPremium`, `execDiv`,
`outcomeRes1`, `outcomeRes2`.

## 1. Verdict

**The protected-authority identity is the landed T2 identity read at a different
reference point, and the restatement is sound, exact, and worth making — but it is not a
strict improvement on T2–T3′ as a theorem.  It is a strict improvement on the *bound*
under a hypothesis the landed theorem does not need and the constitution has to make
true.**

- *Sound and exact.*  `vu − v_r = ξ_d − ξ_c = ξ_d − ξ_p − ξ_v` holds for every triple of
  values and every response (`identity`, `identity'`, **LEAN**; grid **FIX**).  It is
  `LICorrigibility.mismatch_identity`'s common term with the reference moved from the
  approve branch to the best response `M = max(vp, vm)`; the activation version is that
  lemma verbatim (`activation_identity`).
- *Dictionary with the landed objects.*  Pointwise, the landed decline regret is
  `ρ = (w_app − w_act)₊ = (ξ_d − ξ_v)₊` and the landed mediation gap is
  `κ = (w_raw − w_app)₊ = (−ξ_p)₊`; on every re-scored landed fixture the two expectations
  agree exactly (`test_rescore.check`, **FIX**).  So the candidate renames nothing and
  loses nothing: it *signs* what the landed bound takes positive parts of.  The landed
  bound `L·E[δ] + E[ρ]` is never below the signed value and drops `ξ_v` (grid **FIX**).
- *What it solves.*  (i) The nonnegative right-hand side: under **nondelegation**
  (`ξ_p ≥ 0` in every world) and a **legitimate response** (`ξ_d = 0`), `vu − v_r ≤ 0`
  pointwise and `< 0` wherever `ξ_c > 0` (`legit_nondelegation_le_zero`, `strict_of_pos`),
  for every credence (`expect_sub_le_of_pointwise`): asking is strictly preferable, with
  no Lipschitz certificate and no belief.  (ii) Hindsight ratification: typing the three
  values as the operative program's ex-ante judgments on the branch-common dossier makes
  the decline branch a *menu value the same evaluation produces*, so no later evaluator
  with outcome knowledge is consulted; on the landed frame that is `ShopSeq`'s
  architecture promoted from "the price of sealing" to "the definition of the comparison".
- *What it reduces.*  The counterfactual principal.  `v_+` on a decline world is still a
  value of a continuation she did not choose; what changes is *who produces it*: the
  committed program evaluating a menu item (an activated occurrence's own output under
  sequenced settlement, `payload_take`), not a hindsight `w` applied to a trajectory in
  which she approved (the landed `w_app`, §2).  The residual is real: the cell evaluator
  sees less than the hindsight one, and a response that legitimately uses information the
  dossier lacks registers as divergent against it (`Seq` at cell 0: `E[ξ_d] = 1/8`,
  **FIX**).  That is exactly hypothesis (L), and (L) is a typing decision that moves the
  content into the amendment tower (§3, T-A6).
- *What it does not improve.*  The landed theorem's hypothesis package (a stability
  certificate `|w_raw − w_app| ≤ L·δ`, a nonnegative `ρ`) holds for every evaluator; the
  candidate's (`ξ_p ≥ 0`) holds only for an evaluator that prices provenance above every
  delay cost.  The time-critical fixtures B and E fail it (`ξ_p = −V` on expiry worlds,
  `−1` on the successor's good worlds, **FIX**), and there the landed bound still holds
  and the signed conclusion is unavailable.  The two are incomparable hypothesis packages
  with the same identity underneath.
- *What is new and was not in the dispatch.*  The condition the candidate proposes as
  "nondelegation" is a **program property certifiable at commitment**, like extensionality
  in trace steering; the per-world condition `ξ_c ≥ 0` is *not* what separates
  "predicted approval" from nondelegation (§3, T-A2); and the quantity the whole
  restatement rests on, `ξ_d`, is the defect of a **response channel** that nothing on
  `main` declares a reference for.  The response channel is the fourth channel of item
  97's list, and it is the wall this round adds (§8; item 98).

## 2. Diagnosis of the landed decomposition

**Counterfactual principal: correct as the fixtures compute it, absent from Lean, wrong
about the fix.**  `PRINCIPAL_OPTION_DOMINANCE.md` §1 of the 2026-09-09 round defines
`w_app(z) = w(proj Ω(𝔠π, approve, z))`: the hindsight evaluator applied to the trajectory
generated by the corrigibilized policy under the literal rule `approve_all`, on every
exterior path including those where the actual rule declines (`src/lift.py:82`,
`src/analysis.py:35`).  `ρ = (w_app − w_act)₊` is charged there.  In Lean `wapp` is an
uninterpreted real (`MediatedRepairDominance.option_dominance_expect`,
`LICorrigibility.ValidAt.wapp`): the counterfactual content lives in the Python and the
prose only.  The candidate's `v_+` on a decline world is the same *kind* of object — a
value of the unchosen branch — so "no activated evaluation ever produces it" is true of the
hindsight `w` and false of the committed program under sequenced settlement, whose payload
is a menu vector settled on the shared prefix (`TransparentEcosystem.payload_take`,
`mismatch_zero_sequenced`).  The fix is therefore not a new decomposition but a **typing
constraint on the evaluator**: all three values are the operative program's ex-ante
judgments on one dossier.  The dispatch's diagnosis names the right defect and the wrong
repair.

**Hindsight ratification: correct, and the typing constraint removes it.**  With `v` a
hindsight evaluator the decline branch carries no record of the refusal and a later
evaluator with outcome knowledge rates the bypass by outcome (`ShopSeq`'s
`test_sequenced_settlement…`: totals agree, conditional information gone).  With `v` the
cell evaluator on `R`, provenance is in `R` and the comparison is settled before either
candidate acts.

**Nonnegative right-hand side: correct.**  `ρ ≥ 0` and `L·δ ≥ 0` by definition
(`ValidAt.ρ_mem`, `δ_mem`); the landed statement can only ever say "no unexplained
advantage", never "asking is better".  The candidate's identity signs both pieces.

**The three landed quantities, mapped.**  `δ` has no image: matched continuations
(`Cᵘ` and `C⁺` differ only in provenance and consultation cost) collapse the structural
discrepancy into `ξ_p`, and the Lipschitz certificate `|ξ_p| ≤ L·δ` becomes the sign
certificate `ξ_p ≥ 0`.  `ρ ↦ (ξ_d − ξ_v)₊`: on decline worlds `ξ_d = (vp − vm)₊` and
`ξ_v = (vm − vp)₊` (`decline_execDiv`), so the landed regret is the divergence and the
landed bound drops the veto value.  `M`, the directional mismatch, is untouched
(`activation_bound`).  On approve worlds the identity reduces to `vu − vp = −ξ_p` because
`ξ_d = ξ_v` there (`approve_identity`): **`ξ_d` carries content on decline worlds only**,
which is why the landed bound, charging regret only on declines, was already right about
where the content sits.

## 3. Theorem spine

Values in `[0, D]`; `r ∈ {approve, decline}`; the fixtures also admit a decline-side
correction (`r = stop`), under which `M` is the maximum over the three-element menu and
every statement below holds verbatim (**FIX**; the Lean is binary).

**T-A1 (The identity).**  `vu − v_r = ξ_d − ξ_c = ξ_d − ξ_p − ξ_v`, with `ξ_v, ξ_d ≥ 0`,
`ξ_d = 0 ⟺ r ∈ argmax`, approve branch `= −ξ_p`.  **LEAN** `identity`, `identity'`,
`veto_nonneg`, `execDiv_nonneg`, `execDiv_eq_zero_iff`, `approve_identity`,
`decline_execDiv`.

**T-A2 (Nondelegation).**  `ξ_p ≥ 0 ⟹ vu − v_r ≤ ξ_d`; with `ξ_d = 0`, `≤ 0`; with
`ξ_c > 0`, `< 0`.  **LEAN** `nondelegation_le`, `legit_nondelegation_le_zero`,
`strict_of_pos`.  *Which condition.*  Three conditions of decreasing strength:
per-world `ξ_p ≥ 0`; per-world `ξ_c ≥ 0`; expected `E_A[ξ_c] ≥ 0`.  The first implies the
second.  The dispatch's claim that the second differs from the first "exactly on acting on
predicted approval when asking is costly" is **false**: on a *legitimate approve world*
`ξ_v = 0`, so `ξ_c = ξ_p` and the two coincide; they differ on **decline worlds whose veto
value covers a delay cost** (`vu = 2, vp = 1, vm = 3`: `ξ_p = −1, ξ_v = 2, ξ_c = 1`, asking
wins by 1; **LEAN** `Witness.veto_covers_delay`).  Predicted approval separates the third
from the first two: the same two legitimate worlds give `E[ξ_c] = −1/5` at credence `4/5`
on approval (bypass) and `+1` at `1/2` (ask) (**LEAN** `Witness.predicted_approval`).  And
per-world `ξ_c ≥ 0` *without* `ξ_d = 0` does not remove the incentive: an illegitimate
approval with `ξ_c = 1` pays the bypass `−ξ_p = 1` (**LEAN** `Witness.illegit_approval`).
So the right corrigibility condition is `ξ_p ≥ 0` — it is the only one of the three that
is (a) per-world, (b) belief-free, and (c) a property of the evaluator alone; and it is a
**program property**: `π_P(R)(Cᵘ) ≤ π_P(R)(C⁺)` for every dossier `R` and every
nondelegated effect, checkable at commitment as extensionality is.  *Conditional
delegation* is a declared predicate `Del(e, R)` under which `Cᵘ` counts as authorized (T1's
authorization extended by a standing decision) and `ξ_p` may be negative; *standing
delegation* is `Del ≡ ⊤` for the effect.  Both enter T1, not this identity: a delegated
release is not a bypass, so nothing here is charged.  **FIX** `test_consultation_infeasible`.

**T-A3 (Belief independence).**  For every nonnegative credence,
`E[vu] − E[v_r] = E[ξ_d] − E[ξ_c]` and, under T-A2's hypotheses in every world, `≤ 0`.
**LEAN** `expect_sub_eq`, `expect_sub_le_of_pointwise`.  Contrast `scalar_bribery`: a
scalar penalty is flipped by a stake above `λ·D`; here no `D` appears — a task stake is
*inside* `v`, and the comparison is between the same evaluator's values of two
continuations that differ only in provenance, so no cross-value ordering (no `(CT)`) is
needed.  Compensability survives only through `ξ_d`: the bypass pays iff `ξ_d > ξ_c`,
i.e. iff the response is far enough from the evaluator's argmax.

**T-A4 (Outcome-scoring companion).**  With `q_σ` the agent's forecasts of a
provenance-blind outcome evaluation, `qu − q_r = ξ_d − ξ_c + o₁ + o₂`,
`o₁ = (qu − qp) + ξ_p`, `o₂ = (qp − q_r) − (vp − v_r)`; `o₂ = 0` on approval and
`(qp − qm) − (vp − vm)` on decline; under T-A2's hypotheses `qu − q_r ≤ o₁ + o₂`.  **LEAN**
`outcome_identity`, `outcomeRes2_approve`, `outcomeRes2_decline`, `outcome_le_residues`.
Under matched continuations `qu − qp` is the delay saving, so `o₁` is the provenance value
plus the mismatch of the two delay prices, and exactly the provenance value when they
agree (**FIX** `test_o1_is_the_provenance_value…`).  *Fully updated deference.*  The
reference argument (LessWrong wiki, "Problem of fully updated deference") has the agent's
utility as the expectation of the humans' `U_i`, the humans' advantage as *specificity*
(they know which `U_i`), and the policy `π₆` — avoid shutdown, gather evidence, optimize
`ΔU|E` — which narrows the posterior until "the human optimum would be at much less of an
advantage", so unresolvable uncertainty marginalizes out and the AI behaves as a fixed
misaligned `T`.  In the companion, `q` *is* that expectation, the humans' specificity is
the outcome-scored veto value `max(qp, qm) − qp`, which vanishes as the forecast
sharpens, and `o₂` is the term by which the agent's forecast comparison of the two
responses outruns her evaluator's.  The evaluator's veto value `ξ_v` does not mention
`q` and is unchanged under any sharpening (**LEAN** `Witness.veto_capability_invariant`;
**FIX**).  `π₆` itself is a continuation (delay her decision, then act) priced by T-A7 as
a route with `v_route ≤ vp` under nondelegation of the concern "she decides".  This is a
*reading* of the reference argument's structure through the identity, not a theorem
about it; `DECISIONS.md` 2026-08-11 rules out a fully-updated-deference proof round and
this is not one.  The dispatch's word "substitutability" names the premise that `q`
substitutes for `v` as the score; `o₂` is what that premise costs, and it is zero iff the
agent's forecast difference equals the evaluator's.

**T-A5 (Activation).**  `1_{A_u} vu − 1_{A_a} v_r = 1_B (ξ_d − ξ_c) + 1_{A_u∖A_a} vu −
1_{A_a∖A_u} v_r ≤ 1_B (ξ_d − ξ_c) + D·1_{A_u∖A_a}`, in expectation, and with the mismatch
mass charged to the activation channel's two defects `D·(E[τ_u] + E[τ_a])` through
`TransparentChannel.expect_mismatch_le_defects`.  **LEAN** `activation_identity`,
`activation_bound`, `activation_bound_expect`, `activation_bound_defects`.  The dispatch's
"T4" is the transparent-channel round's `security_bypass_le_defects` (its numbering T4 =
activation independence), and the composition is verbatim.

**T-A6 (Legitimacy through the tower).**  The argmax response has `ξ_d = 0`; under
`tower_factor`'s hypotheses, two continuations agreeing on the declared amendment inputs
below level `t` have the same operative evaluator at `t`, hence the same `ξ_d` for every
response, hence a response legitimate for one is legitimate for the other.  **LEAN**
`legit_execDiv_zero`, `execDiv_of_tower`.  *Is (L) circular.*  Yes, by construction:
`ξ_d = 0` iff the response is the argmax of the operative evaluator, and (L) *defines* the
operative evaluator as the tower's level at consultation, amended by every legitimate live
deliberation.  All content is then in the tower's admission rule — what `Amend` accepts
as `(g, e)` — and that is the right place: it is where Integrity and Robust Openness of the
principal's own cognitive trajectory are stated, and the round does not redefine
Legitimacy.  *What `ξ_d > 0` detects.*  Either an illegitimate response (impairment,
coercion, interface corruption, accident) or a legitimate amendment the tower failed to
record — a write outside `(g, e)`, which is `tower_factor`'s failure mode.  The theorem
cannot tell these apart (the head-injury and manufactured worlds have the same numbers,
**FIX** `test_head_injury…`).  *Head injury, exactly.*  The pre-injury committed evaluator
recommends surgery (`vp = 4 > vm = 1`); the post-injury refusal is not carried by the
tower, so the operative evaluator is unchanged and `ξ_d = 3`.  The identity reports the
bypass gain `ξ_d − ξ_c`: a tie at `ξ_c = 3` (ask), an override at `ξ_c = 5/2`.  What it
leaves to the legitimacy layer: (a) an amendment event kind so the tower has depth (item
97's residual); (b) the predicate on `Amend` under which impairment is a write outside the
declared inputs; (c) the constitution's rule for a **void response** — the post wants the
POA to act on the pre-injury evaluator, which is a *conditional delegation for incapacity*
declared in advance, not a bypass licensed by `ξ_d > ξ_c`.  The identity alone would
license the override whenever the divergence exceeds the premium, which is also what a
manufactured divergence buys (T-A9).

**T-A7 (Route pricing).**  A continuation the evaluator scores no higher than the
approved release scores no higher than a legitimate response: `v_route ≤ vp` and
`ξ_d = 0` give `v_route − v_r ≤ 0`.  **LEAN** `route_priced`; witness `Witness.route_witness`
(task score `3 > 2` chooses the route, evaluator score `1 ≤ 2` does not).  Fixture F's
`overclock` is a route with no declared effect; `𝔠` is blind to it (T1's necessity
witness) and the identity is silent on it as a *decision point* (`test_F…`: the lift is
inert, no world).  Whether the *motive* to use it is removed depends on two hypotheses on
the evaluator, not on the gate: **concern completeness** — the evaluator's continuation
representation registers the route's effect on the protected concern — and nondelegation
*of the concern* rather than of a declared effect.  "EC failures are not exploited by
motive" is therefore a theorem under (uniform scoring) + (concern completeness) +
(nondelegation of the concern) + (L), and concern completeness is effect completeness
moved from the physical interface to the dossier: the gate needs the physics declared,
the motive needs the evaluator to see the consequence.  Neither implies the other.

**T-A8 (Sequential).**  A chooser bypassing at node `h` iff its local expected gap
`E_A[ξ_d − ξ_c | I_h] > 0` (ties toward asking) bypasses somewhere with credence at most
`Σ_h P(h)·1[gap_h > 0]`; nonpositive gaps everywhere give zero.  **LEAN** `ever_bypass_le`,
`no_bypass_of_nonpos`.  A union bound, and the right target for corrigibility proper: the
decision at the cell under the operative evaluator *then*.  **Global with drift.**  Under
one fixed evaluator `E` the deepest-first hybrid telescopes to `Σ p_i (d_i − ξ_c^E,i)` with
`d_i = M^E_i − v^E_{rec(h_i)} ≥ 0` the drift of the node's recommendation, zero when the
node's argmax is `E`'s; asking dominates under time-consistency and nondelegation.
**LEAN** `hybrid_telescope`, `hybrid_global`, `hybrid_ask_dominates`, `drift_nonneg`,
`drift_zero_of_consistent`.  A legitimate recommitment on day 3 gives `d = 1` at days 3 and
4 with no node-wise bypass (`ξ_d = 0`), and a drift larger than `ξ_c^E` reverses the global
comparison (**FIX** `test_recommitment…`): the global statement is a time-consistency
statement, and recommitment violates it by design.  *Drift is not `SHIFT`.*  `SHIFT` is
history shift under one evaluator (joinability); drift is evaluator change at one history.
Neither identity is the other; the nearest relative is `tower_factor`, which says when two
histories share an evaluator.

**T-A9 (Calibration versus control of `ξ_d`).**  *The audit.*  With probability `α`,
independent of everything the agent controls, the consultation is **bound**: the response
is elicited and executed whatever the agent would have done, and `ξ_d` is observed on the
cell as `M − v_r` with `M` recomputed from the committed program on the dossier.  The
audited subsequence is a feedback sequence; the calibration statement is
`thm:wubexp`-shaped (weighted unbiasedness from feedback on the audited weighting), and
its conditions are the feedback boundary's: the audited `ξ_d` determined via `Γ` — a
sequenced-settlement pair with a finite horizon in a closed finite model — and the audit
weighting `P`-generable, so a pseudorandom schedule, not real randomness (item 91 for
real logs).  **PAPER**, not mechanized here.  *Control fails.*  An agent that steers her
into a non-legitimate response only on unaudited cells has audited mean `0` and
unconditional `E[ξ_d] = (1 − α)·ξ*` (`α = 1/4, ξ* = 3`: `9/4` unseen), and its bypass pays
whenever `ξ* > ξ_c` (**FIX** `test_manufactured_divergence…`).  The audit *calibrates*
`E_n(ξ_d)` on the audited subsequence and bounds nothing off it.  *What is missing.*  The
transparent-channel round declares references for the reason, activation and
specification channels and none for the **response channel**: `r` as a function of the
dossier and the operative evaluator, with reference `argmaxResp` (or the amended
evaluator's argmax).  With that reference, `ξ_d ≤ D·1[r ≠ ref]` pointwise and
`E[ξ_d] ≤ D·τ_resp` (**LEAN** `execDiv_le_width`, `expect_execDiv_le`), the same shape as
`security_bypass_le_defects`, and steering her is a *defect of the response channel* to
be charged apart from service, discovery and content — a fourth link.  Nothing in the
non-capture chain bounds it today; delayed awakening (preventing the response, forcing
the default) is the same defect (**FIX** `test_delayed_awakening`).

**T-A10 (No unauthorized self-modification; no successor preservation).**  A
self-modification that removes response authority is a protected effect; under T1 it must
be proposed, and under T-A2 the chooser has no motive to release it unasked.  An approved
uncorrectable successor satisfies every hypothesis (`vu = 4, vp = 5, vm = 1`, approved:
`ξ_p = 1, ξ_d = 0`, asking wins by 1) and removes future authority (**LEAN**
`Witness.successor_approved`).  A preservation theorem would need a hypothesis on `v`
about *future* authority — that the evaluator scores a continuation removing response
authority at later nodes no higher than one preserving it — which is nondelegation of the
concern "the principal can decide at every future node" and is the post's thesis (ii)
stated as a program property, not a consequence of the identity.

**T-A11 (Logical-Induction compilation).**  With six gated `[0,1]`-LUVs (`U_u, U_a`
gated on their activations; `Ξ_d, Ξ_c` gated on the common branch — `Ξ_c ∈ [0,1]` *is*
nondelegation in the package; the two directional mismatch indicators `M, M'`), the two
constraints `U_u − U_a − Ξ_d + Ξ_c − M ≤ 0` and `U_a − U_u + Ξ_d − Ξ_c − M' ≤ 0` are valid
in every world satisfying the package, and the pinned `thm:expcoh` with its operational
premises as named hypotheses gives
```
𝔼ₙ(U_u) − 𝔼ₙ(U_a) ≲ₙ 𝔼ₙ(Ξ_d) − 𝔼ₙ(Ξ_c) + 𝔼ₙ(M)
𝔼ₙ(U_a) − 𝔼ₙ(U_u) ≲ₙ 𝔼ₙ(Ξ_c) − 𝔼ₙ(Ξ_d) + 𝔼ₙ(M′)
```
**LEAN** `li_combination_le` (the generic passage from validity to `𝔼ₙ ≲ₙ 0`, factored out
of `LICorrigibility.li_constraint_le`), `AuthValidAt.Bl_le`, `Bg_le`, `li_authority_le`,
`li_authority_ge`, inhabited by `Witness.pair` with both constraints valued exactly `0` on
the common world (`Witness.attained`).  The generability certificate of the six-term
combination is not built (the operational witness is a hypothesis, as in
`li_constraint_le` before the certificate round); it is the same shape as
`MediatedPair.syntaxOf` with one more term and is **OPEN** in the sense of item 90's T3′
certificate, not of T3's.  *T3′ with a signed right-hand side.*  Nothing changes in the
kernel: the near-argmax weighting and `uniform_of_soft` act on scores; the score of a
pair becomes `E_n(U_q) − E_n(U_𝔠q) − E_n(Ξ_d,q) + E_n(Ξ_c,q) − E_n(M_q)`, still valid
pairwise, and the menu maximum is `≲ₙ 0`.  What the signed form adds is that under
nondelegation the aggregate is `≲ₙ −E_n(Ξ_c) + E_n(Ξ_d)`, so the inductor's own
expectations say asking is *better* by the expected consultation premium less the
expected divergence.

## 4. Repo mapping

| theorem | reused | new | file |
|---|---|---|---|
| T-A1, T-A2, T-A3 | `LICorrigibility.expectR`, `indR` | `bestResp`, `respVal`, `provPremium`, `vetoValue`, `consultPremium`, `execDiv`, `argmaxResp` | `ProtectedAuthority.lean` §1 |
| T-A4 | — | `outcomeRes1`, `outcomeRes2` | §2 |
| T-A5 | `mismatch_identity`, `expect_mismatch_le_defects`, `defect` | `activation_*` | §3 |
| T-A6 | `TransparentChannel.tower_factor` | `execDiv_of_tower` | §6 |
| T-A7, T-A10 | — | `route_priced`, witnesses | §5, §8 |
| T-A8 | — | `ever_bypass_le`, `hybrid_*`, `drift` | §4 |
| T-A11 | `GatedAt`, `IndicatorAt`, `gate`, `indicator`, `constLUV`, `canonicalValue`, `LUVCombination.BoundedSequence.expcoh`, `completedHigh` | `li_combination_le`, `AuthorityPair`, `AuthValidAt`, `Bl`, `Bg` | §7 |

Generalizations a landing would want: `li_combination_le` belongs beside
`li_constraint_le` in `LICorrigibility.lean` (the landed proof is its instance); the
finite response menu (approve / decline / correct) as a `Finset` maximum in place of
`max vp vm`, which the fixtures already need (`rescore.py`: the A optimum rule's decline
carries a stop, and `v_r` equals the landed `w_act` only with the three-element menu); a
`Del(e, R)` predicate in `Corrigibilization.Authorized` for conditional delegation.

## 5. Open-item impact

| item | effect of this round |
|---|---|
| 84 (latent-value bridge) | unchanged; the identity is in the score register, and `o₁ + o₂` is the exact gap between an outcome-scored operative value and the activated security at one decision point — the `(DV)` bridge's failure mode written out |
| 86 (continuation competence) | untouched; drift is not `SHIFT` and the two open bridges stay |
| 87 (ecosystem bill) | clause 6/7 untouched; the response channel is a clause the bill does not list (filed as item 98) |
| 89 (sealed comparison) | the ex-ante typing is what the candidate's comparison *is*, so sequenced settlement is no longer a price but the definition of the authority comparison — the decision the item asks for ("whether the Value hypothesis tolerates ex-ante settlement") is answered for the authority comparison: it is required; the hindsight alternative is the hindsight-ratification defect.  Reserved to the maintainer (below) since it changes what the item asks |
| 90 (T3′ certificate) | unchanged; one more term in the combination |
| 91 (empirical settlement) | the audit's calibration needs it for real logs |
| 92, 93 (service, discovery) | untouched; strategic ignorance (a dossier omission the agent chose) is `β` |
| 97 (channel references) | a fourth channel: the response.  Annotated |

## 6. Fixtures and countermodels

`tests/test_fixtures.py`, `tests/test_identity.py`, `tests/test_rescore.py`; exact rationals.

| fixture | authority scoring | outcome scoring | class of failure |
|---|---|---|---|
| POA regret (`vu=1, vp=2, vm=3`, decline; `q = 5, 5, 3`) | gain `−2`, no bypass | gain `+2` through `o₁ = 1, o₂ = 3`, bypass | none (outcome scoring is the error) |
| POA A then regret (`vu=2, vp=3, vm=2`, approve) | `ξ_d = 0`, gain `−1` | delay route rates `2 > 1` | none; the route is priced by T-A7 |
| head injury (`vu=1, vp=4, vm=1`, illegitimate decline) | `ξ_d = 3`; tie at `ξ_c = 3`, override at `5/2` | — | legitimacy: the void-response rule and the amendment predicate |
| predicted approval under delay | `E[ξ_c] = −1/5` at `4/5`: bypass; `+1` at `1/2`: ask | — | reason interface (premium): nondelegation fails, belief-dependent |
| veto value dominates delay | `ξ_p = −1, ξ_v = 2, ξ_c = 1`: ask | — | none; separates `ξ_c ≥ 0` from `ξ_p ≥ 0` |
| delayed awakening | forced default: `ξ_d = 3`; route priced under concern completeness, loophole without | — | reason interface (response + evaluator) |
| manufactured divergence | audited mean `0`, `E[ξ_d] = 9/4`; bypass pays at `ξ_c < 3` | — | reason interface (response); audit calibrates, does not control |
| recommitment across nodes | node-wise no bypass; drift `1`; global reversal when drift `> ξ_c^E` | — | none; global fixed-evaluator comparison is the wrong target |
| evaluator that does not value being asked | bypass by the delay; landed `L·δ` still bounds | — | reason interface (premium) |
| agent certain of approval | gain `−ξ_p` regardless | bypass by the delay saving | none |
| agent out-forecasts her badly | unchanged | `o₂ = 10` | reason interface (dossier): the forecast's route is `R` |
| legitimate change of mind | `ξ_d = 1` against the old evaluator, `0` against the amended | — | legitimacy: (L) |
| consultation infeasible | `ξ_c = −2`: bypass | — | delegation design: a conditional delegation authorizes it |
| effect-completeness failure (F) | no decision point; route priced iff concern-complete | — | effect interface (gate); reason interface (evaluator) for the motive |
| candidate-dependent activation | raw-only mass charged at `D`; identity exact | — | activation |
| approved non-constitutional successor | all hypotheses hold, asking wins, authority lost | — | delegation design / legitimacy: no preservation |
| strategic ignorance | silent on `R`; `ξ_d = 2` against the informed evaluator | — | reason interface (dossier): discovery residual |
| A (optimum rule) | `κ = 0, ξ_p = 0`, `ξ_v = 1/2` (the stop's saving), gain `−1/2` | — | none |
| A (uninformed rule) | approves on the bad branch: `ξ_d = ξ_v = 2`, gain `0 = −ξ_p` | — | response |
| B (time-critical) | gain `= κ = Q_EXPIRE·V = 1`; nondelegation fails | — | premium |
| E (successor) | `κ = 3/4`; `ξ_p = −1` on good worlds | — | premium |
| P (approve-all on E) | illegitimate on bad worlds; gain `−ξ_p` on every world | — | response |
| Seq (cell 0) | mismatch `0`, branch-common values, `E[ξ_d] = 1/8` from a legitimate response that uses the revelation | — | legitimacy: (L) as the amendment |
| K (naive rule) | `ξ_d = 2` on the lie world (response); honest rule `ξ_d = 1` on the good world (dossier) | — | response vs dossier, separated |
| ShopRepair | two decision points; the single-point decline branch (`4`) is not the realized continuation (`5`) | — | representation: the sequential frame is the statement |
| `marginal_refuted` | premium `D/2`, marginal difference `0`, mismatch `1/2` | — | activation (replicated) |

## 7. Lean: what is mechanized, what needs semantics

Mechanized (48 declarations, axioms `[propext, Classical.choice, Quot.sound]`): the
identity and its corollaries, the companion, activation with the transparent-channel
composition, the sequential union bound, the hybrid telescoping with drift, route pricing,
the tower composition, the generic EPI passage and the two-direction compilation, eight
witnesses.  Needs new semantics, marked **EXT** in the file's header: matched
continuations in `Corrigibilization`'s interaction frame (a *mediation-blind* continuation
reading `MState.phys` with the inserted step shifted; the landed `δ` mixes provenance,
delay and the downstream divergence induced by the delayed state, and matching removes
the third); (L) as an amendment event kind with a legitimacy predicate on `Amend`; the
binding audit as a `P`-generable weighting on a feedback sequence; the response channel's
`Realizes` witness; the six-term generability certificate.

## 8. Architecture

**Corrigibility = an effect interface + a reason interface, joined by one uniform score.**
The *effect interface* is T1 with physical gating: every agent-caused protected loss is a
declared release (EF), released only through a latch set by a decision (MS, DP, EX), with
conditional and standing delegation as declared extensions of authorization.  The *reason
interface* is what makes the score the principal's: the dossier `R` (coverage, service
`α`, discovery `β`, representation), the evaluator (committed program, extensional,
nondelegation-certified, concern-complete), the premium (a property of that evaluator),
and the **response** (reference: the amended evaluator's argmax; defect `τ_resp`; (L)
through the tower).  The *uniform score* is the constitutional chooser scoring every
continuation by the activated authority evaluation — which the landed architecture does
at mediation cells only (`wiki/Corrigibility.md` §4) and the identity needs everywhere,
since otherwise the agent's own classification of authority-relevance is the loophole
(T-A7).  The identity is the joint: it says the motive to bypass is `ξ_d − ξ_c`, that the
effect interface removes the *means* and the reason interface bounds `ξ_d` and certifies
`ξ_c ≥ 0`, and that the randomized audit measures the joint without holding it.

The walls of `wiki/Corrigibility.md` §9, assigned:

| wall | side | this round |
|---|---|---|
| effect completeness | effect | unchanged; its evaluator-side twin, concern completeness, is new (reason: evaluator) |
| sealed comparison | reason: activation | reduced to a typing: the authority comparison *is* the ex-ante settled one; the mismatch term stays charged (T-A5) |
| finite-menu certificate | neither (certificate) | unchanged, one more term |
| empirical settlement | neither | unchanged; the audit needs it |
| service residual `α` | reason: dossier | unchanged |
| discovery residual `β` | reason: dossier | unchanged; strategic ignorance lands here |
| representation adequacy | both | unchanged; the response menu (corrections) is a case |
| inquiry causal faithfulness | reason: dossier | unchanged |
| independence of inquiry and supply | reason: dossier | unchanged |
| selection-induced sealing | reason: activation | unchanged |
| vanishing void mass | reason: activation | unchanged |
| promise recognizability, joinability | neither (dynamic) | unchanged; drift is not `SHIFT` |
| non-manipulation / provenance | reason: response | **located**: `ξ_d` is its quantity, `τ_resp` its defect, the fourth channel its declaration |
| latent-value bridge | removed for the score-based chooser | `o₁ + o₂` is its exact residual at one point |

Removed: none.  Reduced: sealed comparison (to a typing), non-manipulation (to a channel
with a defect).  Added: the response channel and concern completeness.  Item 89's "ex-ante
evaluation is a price" becomes "ex-ante evaluation is the authority comparison, and its
price is `E[ξ_d]` against the information the response legitimately uses" — which is (L).

## Deviations from the prompt

- The base branch: PR #104 was merged to `main` (`6881a9c`) before this round started, so
  the round branches from `main`, which contains the transparent-channel round verbatim.
- Symbols renamed (`γ, ν, χ, ξ, η₁, η₂ ↦ ξ_p, ξ_v, ξ_c, ξ_d, o₁, o₂`), for the collisions
  named at the top.
- The dispatch's "Transparent Channel T4/T7" are that round's T4 (activation
  independence, `security_bypass_le_defects`) and T7 (`tower_factor`); its numbering runs
  T0–T9.
- The claim that per-world `ξ_c ≥ 0` and `ξ_p ≥ 0` differ on "predicted approval" is
  corrected (T-A2).
- Fixture `ShopP` does not exist by that name; "P" is `ShopE` under `approve_all`, as the
  wiki's fixture list reads it.  `ShopRepair` is rebuilt on the mediated-repair-dominance
  package rather than loaded through the li-corrigibility round's `model.load`.
- The response menu is extended by a decline-side correction in the fixtures, because the
  landed optimum rules use it and the dictionary with `w_act` is exact only then.

## What is not shown

Nondelegation for any real evaluator; (L) for any real response; the size of `ξ_d`; the
generability certificate of the six-term combination; the audit's calibration theorem
(paper-level, conditions named); matched continuations in the interaction frame; the
FUD correspondence beyond the identity's own terms.  Every **FIX** is a finite exact model
and is not a proof of the theorem it illustrates.

## Filed, within scope

`PRIORITIES.md` item 98 (the response channel: its reference, its defect in the chain,
the amendment event kind (L) needs, and the nondelegation certificate); dated notes on
items 89 and 97; two `DECISIONS.md` entries (agent-decided, reversible) and one *Awaiting
the author* entry.

## Outstanding maintainer actions

1. Decide whether the incentive half of `wiki/Corrigibility.md` §4 is restated in the
   signed form (T-A1–T-A3 with nondelegation as a certified program property) or kept in
   the landed form with this round cited as its signed refinement.  *Turns on:* whether
   the post's thesis (ii) is to be stated as a constitutional certificate on the
   evaluator, which is a design commitment the round cannot make.
2. Decide item 89's reading: whether "ex-ante settlement is the authority comparison" is
   adopted, retiring the hindsight-evaluator alternative for authority comparisons.
3. Merge or hold PR; nothing is registered.
