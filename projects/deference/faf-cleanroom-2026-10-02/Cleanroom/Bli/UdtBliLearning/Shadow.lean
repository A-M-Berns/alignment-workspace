import Cleanroom.Bli.UdtBliLearning.Calibration

/-!
# `udt-bli-learning` · Shadow: PDF 14's conjectures in the finite single-coin shadow (T8)

**Scope: single coin, additive stakes, finite horizon `K`; "average over all trees" read as the
uniform average over the coin's two realizations** (the only variation this tree has). The
source (PDF 14, Sep 10 2023) proposes two impossibility conjectures and concedes its definitions
are ill-posed ("what do we mean by identical situations above? Here start the problems"; "we're
baking in 'the right prior' when defining 'average'"). Each is formalized in its nearest
well-posed finite form and refuted there; the infinite-tree conjectures stay conjectures.

* (a) **Comparing averages** (Def. 1): `avgValue π := ½ valueUnder 1 π + ½ valueUnder 0 π`.
  `avgValue_eq_half` (**L**, `ring` on the closed form): this *is* the ex-ante value under the
  prior with `q = ½`. The source says the same of its finite average ("a uniform prior", PIBBSS
  §5.3) and places its claim — "it won't correspond to any *simplicity* prior" — in the limit over
  all depth-`n` trees; the two-realization shadow has one tree and no simplicity prior, so that
  claim is not engaged here.
* (b) **"Doesn't learn"** (Def. 2) and Theorem 1 ("Suppose `A` doesn't learn. Then, another `A'`
  that does learn does better on average"): `DoesntLearn π := ∀ j k, π Ask_j = π Ask_k` (the same
  action in every identical situation); `conj1_shadow` is the sentence; `not_conj1_shadow`
  (**refuted, finite shadow**): a constant policy is average-optimal for every stake (`payAll` if
  `c ≤ V`, `refuseAll` if `V ≤ c`), so no learner does strictly better (content for `K ≥ 2`; for
  `K ≤ 1` every policy "doesn't learn" and the sentence is vacuously false). Reading
  (ATTRIBUTION-UNVETTED): the source restricts "identical" to subtrees "isolated from the rest of
  the tree"; the rounds here share the coin, so the source may hold its clause excludes this tree,
  under which the conjecture is unstatable here.
* (c) **The humbler result** (Theorem 2: freeze `A` versus forced-update `A_f`, "there is `f` such
  that `A_f` does better than `A` on average"): `avgValue (refrozen t) − avgValue payAll = −((V −
  c)/2) · ∑_{k ≥ t} γ_k` (`avg_refrozen_gap`, from `udt-bli-tiling`'s `frozen_gap` at `q = ½`).
  With `A` read as the source reads it — *the frozen prior's own policy* — two forms:
  `conj2_shadow_frozen_iff` (`A` any `IsPriorOptimal` policy of `scPrior p`, under `gain p > 0`
  so that `refrozen t` is its re-freeze): the sentence holds iff `V < c` — **false exactly when
  `c ≤ V`**, and "true when `V < c`" means the frozen prior pays while the fair-coin average says
  refuse, i.e. `q < ½` (`q_lt_half_of_gain_pos_of_lt`): a frozen prior *miscalibrated against
  the average*; `not_conj2_shadow_calibrated` (the frozen prior calibrated to the average,
  `q = ½`): **false for every stake**, with no hypothesis — once the average is the prior the
  frozen agent optimizes, nothing beats that agent on average; this is PDF 14 p. 3's own caveat
  ("we're baking in 'the right prior' when defining 'average'") formalized (Kind L), not a
  refutation of the conjecture as posed, which needs an average that is no agent's prior (repair
  round 2). `conj2_shadow`/`conj2_shadow_iff`
  (`A := payAll`, no `gain` hypothesis) are kept as the two-policy computation they are.

Surviving neighbours: Theorem A (`theoremA`: the well-posed incompatibility) and Theorem B
(`refrozen_gap`: what "freeze versus re-freeze" really contrasts); `Conventions.lean`'s
convention-free verdict. Status column: `refuted (finite shadow)` with the reading named.

Sources: bli-soto-b-007/008/009/012 (PDF 14 pp. 1–4), bli-soto-b-038 (PIBBSS §5.2–5.3);
Abram's objections at journal 2023-09-11 ll. 940–990 ("I don't think this idea makes sense …
UDT faces a different observed market state in the two subtrees"), 985 (Theorem 2 "seems
implausible"); mandate T8.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

variable {K : ℕ} (p : Params K)

/-! ## (a) Comparing averages -/

/-- **The uniform average over the coin's two realizations** — the finite shadow of PDF 14's
"average reward across all decision trees" (Def. 1).
Source: bli-soto-b-007 (PDF 14 Def. 1); mandate T8 (a)
Kind: D
Fidelity: variant: the shadow averages the two realizations of this tree's one coin -/
def avgValue (π : Policy (iterTables K) Bool) : ℚ :=
  1 / 2 * valueUnder p 1 zero_le_one le_rfl π + 1 / 2 * valueUnder p 0 le_rfl zero_le_one π

/-- The half parameters: the model with `q = ½`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def halfParams : Params K := withQ p (1 / 2) (by norm_num) (by norm_num)

/-- **In the finite shadow the uniform average is a prior**: `avgValue π` is the ex-ante value
under the prior with `q = ½` — `ring` on the closed form `valueUnder_eq`, which is affine in `q'`.
This is consistent with the source, which itself calls the finite average "a uniform prior" and
places its claim in the limit: "if we take the average uniformly as above, it won't correspond to
any *simplicity* prior" is about the average over *all decision trees of depth `n`* as `n → ∞`,
where a uniform law is no simplicity prior; the two-realization shadow has one tree and no
simplicity prior, so that claim is not engaged here (it is neither confirmed nor refuted).
Source: bli-soto-b-012 (PDF 14 p. 3: "we're baking in 'the right prior' when defining
'average'"); PIBBSS §5.3 ("a uniform prior … doesn't exist as a probability distribution (all
priors are eventually simplicity biased)"); mandate T8 (a)
Kind: L
Fidelity: exact (the shadow's identity; the source's limit claim is out of reach here)
Hyps: (a) none; does not use faith -/
theorem avgValue_eq_half (π : Policy (iterTables K) Bool) :
    avgValue p π = (scPrior (halfParams p)).exAnteValue π := by
  unfold avgValue halfParams
  rw [valueUnder_eq, valueUnder_eq, exAnteValue_eq]
  change _ = (p.V * (1 - 1 / 2) - p.c * (1 / 2)) * roundSum p.γ π +
    (1 / 2 * p.r₀ true + (1 - 1 / 2) * p.r₀ false)
  ring

/-- `gain (halfParams p) = (V − c)/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gain_half : gain (halfParams p) = (p.V - p.c) / 2 := by
  unfold gain halfParams withQ; simp; ring

/-! ## (b) "Doesn't learn" and the sought-for impossibility -/

/-- **"Doesn't learn"** (PDF 14 Def. 2, in the shadow): the same action at every `Ask_k` — the
"identical situations" are the rounds of the one mugging.
Source: bli-soto-b-008 (PDF 14 Def. 2: "when `A` faces … two identical situations in different
parts of that one tree, it takes the same actions"); mandate T8 (b)
Kind: D
Fidelity: variant: "identical situations" = the rounds `Ask_k` (reading ATTRIBUTION-UNVETTED;
the source may exclude this tree, see the module docstring) -/
def DoesntLearn (π : Policy (iterTables K) Bool) : Prop := ∀ j k : Fin K, π (askT K j) = π (askT K k)

/-- **PDF 14 Theorem 1 in the shadow**: every policy that doesn't learn is strictly beaten on
average by one that does.
Source: bli-soto-b-008 (PDF 14 Thm. 1: "Suppose `A` doesn't learn. Then, another `A'` that does
learn does better on average"); PIBBSS report Conj. 1; mandate T8 (b)
Kind: D
Fidelity: variant: the single-coin shadow under the uniform average -/
def conj1_shadow : Prop :=
  ∀ π : Policy (iterTables K) Bool, DoesntLearn π →
    ∃ π' : Policy (iterTables K) Bool, ¬ DoesntLearn π' ∧ avgValue p π < avgValue p π'

/-- `payAll` doesn't learn.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma doesntLearn_payAll : DoesntLearn (payAll (K := K)) := fun _ _ => rfl

/-- `refuseAll` doesn't learn.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma doesntLearn_refuseAll : DoesntLearn (refuseAll (K := K)) := fun _ _ => rfl

/-- **A constant policy is average-optimal for every stake**: `payAll` if `c ≤ V`, `refuseAll` if
`V ≤ c` (nonnegative weights).
Source: mandate T8 (b) (iii) ("for `V ≠ c` a constant policy is prior-optimal at `q = ½`")
Kind: C (`avgValue_eq_half`, `priorOptimal_payAll`, `priorOptimal_refuseAll`)
Fidelity: exact
Hyps: (a) `0 ≤ γ`; does not use faith -/
theorem exists_constant_avgOptimal (hγ : ∀ k, 0 ≤ p.γ k) :
    ∃ π : Policy (iterTables K) Bool, DoesntLearn π ∧ ∀ π', avgValue p π' ≤ avgValue p π := by
  rcases le_total p.c p.V with h | h
  · refine ⟨payAll, doesntLearn_payAll, fun π' => ?_⟩
    rw [avgValue_eq_half, avgValue_eq_half]
    exact priorOptimal_payAll (halfParams p) (by rw [gain_half]; linarith) hγ π'
  · refine ⟨refuseAll, doesntLearn_refuseAll, fun π' => ?_⟩
    rw [avgValue_eq_half, avgValue_eq_half]
    exact priorOptimal_refuseAll (halfParams p) (by rw [gain_half]; linarith) hγ π'

/-- **PDF 14's Theorem 1 is false in the finite shadow**, for every stake: some policy that
doesn't learn is average-optimal, so no learner does strictly better. Content for `K ≥ 2` (with
`K ≤ 1` every policy satisfies `DoesntLearn`, and the sentence fails for want of a learner).
Reading: the rounds `Ask_k` of the one coin are the "identical situations"; under the source's
isolation clause ("no inter-dependencies … with the rest of the tree") this tree may be excluded,
in which case the conjecture is unstatable here rather than false (ATTRIBUTION-UNVETTED).
Source: bli-soto-b-008 (PDF 14 Thm. 1), bli-soto-b-012; mandate T8 (b) (refutation row)
Kind: C (`exists_constant_avgOptimal`; refutation)
Fidelity: variant: the shadow (reading ATTRIBUTION-UNVETTED)
Hyps: (a) `0 ≤ γ`; does not use faith -/
theorem not_conj1_shadow (hγ : ∀ k, 0 ≤ p.γ k) : ¬ conj1_shadow p := by
  intro h
  obtain ⟨π, hdl, hopt⟩ := exists_constant_avgOptimal p hγ
  obtain ⟨π', _, hlt⟩ := h π hdl
  exact absurd (hopt π') (not_le.mpr hlt)

/-! ## (c) The humbler result: freeze versus forced update -/

/-- **The average gap of the re-frozen policy**: `avgValue (refrozen t) − avgValue payAll =
−((V − c)/2) · ∑_{k ≥ t} γ_k`.
Source: bli-soto-b-009 (PDF 14 Thm. 2); mandate T8 (c)
Kind: C (`avgValue_eq_half`, `frozen_gap`, `gain_half`)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem avg_refrozen_gap (t : ℕ) :
    avgValue p (refrozen t) - avgValue p payAll = -((p.V - p.c) / 2) * tailSum p.γ t := by
  rw [avgValue_eq_half, avgValue_eq_half]
  have := frozen_gap (halfParams p) t
  rw [gain_half] at this
  have ht : tailSum (halfParams p).γ t = tailSum p.γ t := rfl
  rw [ht] at this
  linarith

/-- **PDF 14 Theorem 2 in the shadow with `A` fixed to `payAll`**: some re-freeze day `t < K`
makes `refrozen t` do strictly better on average than `payAll`. `payAll` is the frozen prior's
policy only when the frozen prior pays (`gain p > 0`); this definition does not carry that
hypothesis, so on its own it is a statement about two named policies, not about the source's
`A`. The source-faithful forms are `conj2_shadow_frozen` (`A` quantified over the frozen prior's
optimal policies) and `conj2_shadow_calibrated` (the frozen prior calibrated to the average).
Source: bli-soto-b-009 (PDF 14 Thm. 2: "There is `f` such that `A_f` does better than `A` on
average"); PIBBSS report Conj. 2; mandate T8 (c)
Kind: D
Fidelity: variant: the single-coin shadow; `A` := `payAll` (the frozen prior's policy *when it
pays*; see `conj2_shadow_frozen_iff` for the form that carries this), `A_f` := `refrozen t` -/
def conj2_shadow : Prop := ∃ t, t < K ∧ avgValue p payAll < avgValue p (refrozen t)

/-- **`payAll` is beaten on average by a re-freeze iff `V < c`**, for every re-freeze day. Read as
Theorem 2's shadow this is exact only where `payAll` is the frozen prior's policy (`gain p > 0`,
`conj2_shadow_frozen_iff`): false exactly when `c ≤ V`; "true when `V < c`" is then a fact about
a frozen prior miscalibrated against the average (`q < ½`, `q_lt_half_of_gain_pos_of_lt`), and
for a calibrated frozen prior the sentence is false for every stake (`not_conj2_shadow_calibrated`).
Source: bli-soto-b-009 (PDF 14 Thm. 2); journal 2023-09-11 l. 985 ("this seems implausible");
mandate T8 (c) (refutation row: "false exactly when `V > c`, true when `V < c`" — the mandate's
"true" half is carried only under `gain p > 0`, STANDARDS §3 over the mandate; audit r1 B2)
Kind: C (`avg_refrozen_gap`, `tailSum_pos`)
Fidelity: variant: the shadow; `A` := `payAll`
Hyps: (a) `0 < γ`, `0 < K`; does not use faith -/
theorem conj2_shadow_iff (hγ : ∀ k, 0 < p.γ k) (hK : 0 < K) : conj2_shadow p ↔ p.V < p.c := by
  constructor
  · rintro ⟨t, ht, hlt⟩
    have hg := avg_refrozen_gap p t
    have hpos := tailSum_pos p hγ t ht
    by_contra hVc
    have : 0 ≤ (p.V - p.c) / 2 := by linarith [not_lt.mp hVc]
    nlinarith
  · intro hVc
    refine ⟨0, hK, ?_⟩
    have hg := avg_refrozen_gap p 0
    have hpos := tailSum_pos p hγ 0 hK
    nlinarith

/-! ### Theorem 2 with `A` read as the source reads it: the frozen prior's own policy

PDF 14 p. 4: `A` "just runs `Q` for `n` steps, and then freezes that prior and uses it forever";
`A_f` "does the same, but hard-codes into the prior 'after `f(n)` steps, become updateful'". So
`A` is *whatever the frozen prior prescribes* — an `IsPriorOptimal` policy of the frozen prior —
and `A_f` is the re-freeze, which on the model is `refrozen t` exactly when the frozen prior pays
(`gain p > 0`: before `t` it pays as the frozen prior does, from `t` on it refuses as the updateful
rule does; for `gain p ≤ 0` the frozen prior already refuses and `A_f = A` at every `Ask`).
`conj2_shadow` fixes `A := payAll`, which is the frozen prior's policy only under `gain p > 0`;
the two definitions below carry the identification instead of presupposing it. -/

/-- **PDF 14 Theorem 2 in the shadow, `A` the frozen prior's policy**: some prior-optimal policy
`A` of the frozen prior `scPrior p` is strictly beaten on the uniform average by some re-freeze
`refrozen t`, `t < K`.
Source: bli-soto-b-009 (PDF 14 Thm. 2, p. 4: "`A` … freezes that prior and uses it forever");
mandate T8 (c); audit r1 B2
Kind: D
Fidelity: variant: the single-coin shadow; `A` = any `IsPriorOptimal` policy of `scPrior p`,
`A_f` = `refrozen t` (which is the re-freeze of a *paying* frozen prior, `gain p > 0`) -/
def conj2_shadow_frozen : Prop :=
  ∃ A : Policy (iterTables K) Bool, (scPrior p).IsPriorOptimal A ∧
    ∃ t, t < K ∧ avgValue p A < avgValue p (refrozen t)

/-- A prior-optimal policy of a paying frozen prior (`gain > 0`, `γ ≥ 0`) has the full
`roundSum`: `roundSum γ A = ∑ γ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_eq_sum_of_priorOptimal (hg : 0 < gain p) (hγ : ∀ k, 0 ≤ p.γ k)
    (A : Policy (iterTables K) Bool) (hA : (scPrior p).IsPriorOptimal A) :
    roundSum p.γ A = ∑ k, p.γ k := by
  have h1 := hA payAll
  rw [exAnteValue_eq, exAnteValue_eq, roundSum_payAll] at h1
  have h2 := roundSum_le p hγ A
  have h3 : ∑ k, p.γ k ≤ roundSum p.γ A := by nlinarith
  exact le_antisymm h2 h3

/-- Under `gain p > 0` every prior-optimal policy of the frozen prior has the average value of
`payAll` (the `Rec`/`Other` actions are free; the `Ask` actions are forced to `pay`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma avgValue_eq_payAll_of_priorOptimal (hg : 0 < gain p) (hγ : ∀ k, 0 ≤ p.γ k)
    (A : Policy (iterTables K) Bool) (hA : (scPrior p).IsPriorOptimal A) :
    avgValue p A = avgValue p payAll := by
  rw [avgValue_eq_half, avgValue_eq_half, exAnteValue_eq, exAnteValue_eq]
  have e : (halfParams p).γ = p.γ := rfl
  rw [e, roundSum_eq_sum_of_priorOptimal p hg hγ A hA, roundSum_payAll]

/-- **PDF 14's Theorem 2 in the shadow, with `A` the frozen prior's policy, holds iff `V < c`**
(`gain p > 0`, so that `refrozen t` is the re-freeze of the frozen prior's own policy): false
exactly when `c ≤ V`, true when `V < c` — and `V < c` together with `gain p > 0` means `q < ½`
(`q_lt_half_of_gain_pos_of_lt`): the frozen prior pays because it under-weights the coin's true
side relative to the fair-coin average that judges it. The "true" half is therefore a fact about a
frozen prior *miscalibrated against the average*, never about a calibrated one
(`not_conj2_shadow_calibrated`).
Source: bli-soto-b-009 (PDF 14 Thm. 2); journal 2023-09-11 l. 985 ("this seems implausible");
mandate T8 (c); audit r1 B2
Kind: C (`avgValue_eq_payAll_of_priorOptimal`, `conj2_shadow_iff`, `priorOptimal_payAll`)
Fidelity: variant: the shadow; `A` quantified over the frozen prior's optimal policies
Hyps: (a) `0 < γ`, `0 < K`, `0 < gain p`; does not use faith -/
theorem conj2_shadow_frozen_iff (hγ : ∀ k, 0 < p.γ k) (hK : 0 < K) (hg : 0 < gain p) :
    conj2_shadow_frozen p ↔ p.V < p.c := by
  constructor
  · rintro ⟨A, hA, t, ht, hlt⟩
    rw [avgValue_eq_payAll_of_priorOptimal p hg (fun k => (hγ k).le) A hA] at hlt
    exact (conj2_shadow_iff p hγ hK).mp ⟨t, ht, hlt⟩
  · intro hVc
    obtain ⟨t, ht, hlt⟩ := (conj2_shadow_iff p hγ hK).mpr hVc
    exact ⟨payAll, priorOptimal_payAll p hg.le (fun k => (hγ k).le), t, ht, hlt⟩

/-- **The "true" half is miscalibration**: a frozen prior that pays (`gain > 0`) while the stakes
are adverse (`V < c`) has `q < ½` — it is further from the coin's true side than the fair-coin
average that judges it (`q < V/(V + c) < ½`).
Source: mandate T8 (c) (the reading of "true when `V < c`"); audit r1 B2 and fidelity N3
Kind: L
Fidelity: n/a
Hyps: (a) `0 < c`, `0 < V`, `0 < gain`, `V < c` -/
lemma q_lt_half_of_gain_pos_of_lt (hc : 0 < p.c) (hV : 0 < p.V) (hg : 0 < gain p)
    (hVc : p.V < p.c) : p.q < 1 / 2 := by
  have h := (gain_pos_iff p hc hV).mp hg
  have h2 : p.V / (p.V + p.c) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  exact h.trans h2

/-- **PDF 14 Theorem 2 in the shadow, `A` the policy of a frozen prior calibrated to the
average** (`q = ½`): some prior-optimal policy of `scPrior (halfParams p)` is strictly beaten on
the uniform average by some re-freeze.
Source: bli-soto-b-009 (PDF 14 Thm. 2); mandate T8 (c); audit r1 B2
Kind: D
Fidelity: variant: the shadow, with the frozen prior calibrated to the averaging prior -/
def conj2_shadow_calibrated : Prop :=
  ∃ A : Policy (iterTables K) Bool, (scPrior (halfParams p)).IsPriorOptimal A ∧
    ∃ t, t < K ∧ avgValue p A < avgValue p (refrozen t)

/-- **With a calibrated frozen prior Theorem 2's shadow is false for every stake**, with no
hypothesis at all: the uniform average *is* the ex-ante value under `q = ½` (`avgValue_eq_half`),
so a policy optimal for that prior is not beaten on average by anything, re-freezes included. The
refutation is structural — "does better on average" than the frozen agent is impossible as soon
as the average is the prior the frozen agent optimizes. **This is PDF 14 p. 3's own caveat
formalized**, not a refutation of the conjecture as the source poses it: the source says "if we
average differently, for example with a simplicity prior, then indeed the agent with that prior
will perform best … we're baking in 'the right prior' when defining 'average'", and poses Theorem
2 for an average that is *no* agent's prior (its "won't correspond to any simplicity prior"). The
refutation with content is `conj2_shadow_frozen_iff` (false for `c ≤ V` with the model's own
frozen prior). Structurally two lines — `avgValue_eq_half` twice and the definition of optimality
(audit r2 adversarial N3 / fidelity N1: Kind P → L).
Source: bli-soto-b-009 (PDF 14 Thm. 2), bli-soto-b-012 (PDF 14 p. 3, the caveat); mandate T8 (c)
(refutation row); audit r1 B2 (probe `T8cHonestA`); audit r2 adversarial N3, fidelity N1
Kind: L (refutation under the calibrated reading)
Fidelity: variant: the shadow, with the frozen prior calibrated to the averaging prior — the case
the source itself calls tautological
Hyps: (a) none; does not use faith -/
theorem not_conj2_shadow_calibrated : ¬ conj2_shadow_calibrated p := by
  rintro ⟨A, hA, t, _, hlt⟩
  rw [avgValue_eq_half, avgValue_eq_half] at hlt
  exact absurd (hA (refrozen t)) (not_le.mpr hlt)

end Cleanroom.Bli.UdtBliLearning
