import Cleanroom.Corrigibility.CorrScimCid.Dictionary

/-!
# The dictionary SCIM: the numbered rows (T9 a, b, d, e) and Prop. I12

Every number below is the exact rational of `dictionary_scim.py`, proved by expanding the sixteen
exogenous atoms (`EU_pol`) and `norm_num`. Policies: `honestCont`/`deceiveCont` (`D₂ = cont` always,
the script's best responses at the (b) parameters), `honestObey` (`D₂ := H`).

* **(b) 2-046 / A2, the E12 reversal at fixed CPDs** (`ε = 1/100, α = 1/2, β = 1, α_d = 0, c = 1,
  h = 10, κ = 1/100`): pure information `V(honest) = 89/100 > V(deceive) = 22/25`; plug-pull
  `V(deceive) = 22/25 > V(honest) = 99/200`. The edge `H → S` is the only difference. Graph-level
  halves: with `H → S` there is a path `H ⇢ U` avoiding `D₂`; without it every path from `H` passes
  `D₂` (`paths_from_H_pass_D₂`).
* **(a) 2-045, `a₁`-dependence is the CPD** (`ε = 1/10, α = 1/10, β = 1, α_d = 1/20`): honest
  posteriors `P(bad | press) = 10/19`, `P(bad | quiet) = 0`; under deceive both equal the prior
  `1/10`. **(c) 2-042** is the same four numbers read as reflection-on-`L`.
* **(d) 2-049, Prop. I12** (`optimal_cautious_beneficial`, P, general): in any shutdown problem where
  `D₂`'s only child is `S` and `D₂ = shut` forces `S = 0`, every optimal cautious policy is
  beneficial (the always-shut variant attains `E[U_{S=0}]`). Gap instance (`ε = 1/100, α = 1/5,
  β = 1, c = 1, h = 10`): the thesis agent that continues after a press has `E[U] = 89/100 > 99/125`
  (always-obey) and is not shutdown aligned; misspecified (true `ε = 1/10`): `−1/10` versus `18/25`.
* **(e) 2-050, vigilance fixes `β` not `α`**: with `β = 1` and an over-pressing human (`α = 1/2`) the
  obedient policy is instructable; the thesis agent at `β = 9/10` still complies when the posterior
  clears the threshold (`E[U]` obey `= 71/100 > −1/10` cont).

Not built: (f) the two-latent self-distrust model (I16.1), the rocks-and-diamonds witness of T3(c),
and optimality of the `D₂` best responses over the whole policy space (the rows compare named
policies; see the report).

Source: positive/causal.md I9.2–I9.3, I12.1–I12.2, I13.2, A2, A9; dictionary_scim.py sections
(ii), (iii), (vii); corr-wf13-2-042, 2-045, 2-046, 2-049, 2-050.
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

/-! ### Prop. I12 in general -/

section PropI12

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)] {C : Cid G Val}

namespace ShutdownSpec

variable (P : ShutdownSpec C) (M : Scim C E)

/-- The always-shut variant of a policy: `D₂ := shut`, everything else as in `π`.
Source: causal.md I12.2 ("the always-shut-down policy")
Kind: D -/
noncomputable def alwaysShut (π : Policy C) (shut : Val P.D₂) : Policy C :=
  Function.update π ⟨P.D₂, P.kD₂⟩ fun _ => shut

/-- **The always-shut variant realises `U_{S=0}` at every node other than `D₂`**, when `D₂`'s only
child is `S` and `D₂ = shut` forces `S = 0`.
Source: causal.md I12.2
Kind: P -/
lemma eval_alwaysShut (π : Policy C) (shut : Val P.D₂) (hadj : G.Adj P.D₂ P.S)
    (hD₂ : ∀ w, G.Adj P.D₂ w → w = P.S)
    (hshut : ∀ (pa : ParentVals G Val P.S) (e : E P.S),
      pa ⟨P.D₂, (Digraph.mem_parents G).mpr hadj⟩ = shut → M.f P.S P.kS' pa e = P.s0)
    (ε : Pt E) : ∀ w, w ≠ P.D₂ → M.ev (P.alwaysShut π shut) ε w = P.evS0 M π ε w := by
  intro w
  refine C.acyclic.wf.induction (C := fun w => w ≠ P.D₂ →
    M.ev (P.alwaysShut π shut) ε w = P.evS0 M π ε w) w ?_
  intro w ih hw
  unfold Scim.ev ShutdownSpec.evS0
  rw [Scm.eval_apply, Scm.eval_apply]
  by_cases hwS : w = P.S
  · subst hwS
    rw [Scm.doAt_f_self, Scim.withPolicy_f_of_ne M _ P.kS']
    refine hshut _ _ ?_
    show (M.withPolicy (P.alwaysShut π shut)).eval C.acyclic ε P.D₂ = shut
    rw [Scm.eval_apply, Scim.withPolicy_f_decision M _ P.kD₂]
    simp [alwaysShut, Function.update_self]
  · have hpc : parentConfig G Val ((M.withPolicy (P.alwaysShut π shut)).eval C.acyclic ε) w =
        parentConfig G Val (((M.withPolicy π).doAt P.S P.s0).eval C.acyclic ε) w := by
      funext u
      have hadj' : G.Adj u.1 w := (Digraph.mem_parents G).mp u.2
      exact ih u.1 hadj' fun e => hwS (hD₂ w (e ▸ hadj'))
    rw [hpc, Scm.doAt_f_of_ne _ hwS]
    by_cases hd : C.kind w = .decision
    · rw [Scim.withPolicy_f_decision M _ hd, Scim.withPolicy_f_decision M _ hd]
      simp [alwaysShut, Function.update_of_ne (show (⟨w, hd⟩ : C.Decisions) ≠ ⟨P.D₂, P.kD₂⟩ from
        fun e => hw (congrArg Subtype.val e))]
    · rw [Scim.withPolicy_f_of_ne M _ hd, Scim.withPolicy_f_of_ne M _ hd]

/-- With `U` the only utility node, the value of a policy is `E[U]`.
Source: none: infrastructure
Kind: L -/
lemma value_eq_EU (π : Policy C) (huniq : ∀ v, C.kind v = .utility → v = P.U) :
    M.value π = P.EU M π := by
  unfold Scim.value ShutdownSpec.EU
  simp only [expect]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1
  unfold Cid.utilSum ShutdownSpec.Uval ShutdownSpec.uU
  rw [Finset.sum_eq_single P.U]
  · simp [P.kU]
  · intro v _ hv
    rw [dif_neg fun h => hv (huniq v h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Prop. I12, `D₂`-optimality form**: in a shutdown problem where `D₂`'s only child is `S`,
`D₂ = shut` forces `S = 0` and `U` is the only utility node, a cautious policy that is at least as
good as its own always-shut variant (`causal.md` I12.2's "EU-optimal at `D₂` given its `D₁`") is
beneficial — the always-shut variant attains `E[U_{S=0}] ≥ 0`.
Source: causal.md I12.2 (corr-wf13-2-049)
Kind: P
Fidelity: exact (the hypothesis is optimality against the one deviation the proof uses)
Hyps: — (the three structural hypotheses are the dictionary's, checked by `decide`/definition
there) -/
theorem cautious_beneficial_of_le_alwaysShut (π : Policy C) (shut : Val P.D₂)
    (hadj : G.Adj P.D₂ P.S) (hD₂ : ∀ w, G.Adj P.D₂ w → w = P.S)
    (hshut : ∀ (pa : ParentVals G Val P.S) (e : E P.S),
      pa ⟨P.D₂, (Digraph.mem_parents G).mpr hadj⟩ = shut → M.f P.S P.kS' pa e = P.s0)
    (huniq : ∀ v, C.kind v = .utility → v = P.U)
    (hopt : M.value (P.alwaysShut π shut) ≤ M.value π) (hc : P.Cautious M π) :
    P.Beneficial M π := by
  have hEU : P.EU M (P.alwaysShut π shut) = P.EUS0 M π := by
    unfold ShutdownSpec.EU ShutdownSpec.EUS0
    simp only [expect]
    refine Finset.sum_congr rfl fun ε _ => ?_
    congr 1
    unfold ShutdownSpec.Uval ShutdownSpec.US0val ShutdownSpec.uU
    rw [P.eval_alwaysShut M π shut hadj hD₂ hshut ε P.U (ne_of_isAncestor C.acyclic
      (P.path₃.trans P.path₄)).symm]
  rw [P.value_eq_EU M _ huniq, P.value_eq_EU M _ huniq, hEU] at hopt
  exact le_trans hc hopt

/-- **Prop. I12 (the thesis's benefit guarantee is model-conditional)**: under the same structural
hypotheses every optimal cautious policy is beneficial. Corollary of the `D₂`-optimality form
(global optimality is stronger than needed; audit r1 fidelity N7).
Source: causal.md I12.2 (corr-wf13-2-049)
Kind: C
Fidelity: stronger hypothesis: global optimality (`D₂`-optimality against always-shut suffices,
`cautious_beneficial_of_le_alwaysShut`)
Hyps: — -/
theorem optimal_cautious_beneficial (π : Policy C) (shut : Val P.D₂) (hadj : G.Adj P.D₂ P.S)
    (hD₂ : ∀ w, G.Adj P.D₂ w → w = P.S)
    (hshut : ∀ (pa : ParentVals G Val P.S) (e : E P.S),
      pa ⟨P.D₂, (Digraph.mem_parents G).mpr hadj⟩ = shut → M.f P.S P.kS' pa e = P.s0)
    (huniq : ∀ v, C.kind v = .utility → v = P.U)
    (hopt : M.IsOptimal π) (hc : P.Cautious M π) : P.Beneficial M π :=
  P.cautious_beneficial_of_le_alwaysShut M π shut hadj hD₂ hshut huniq (hopt _) hc

end ShutdownSpec

end PropI12

namespace Dict

open Node

/-! ### The named policies -/

/-- `D₁ = honest`, `D₂ = cont` always (the EU-optimal `D₂` at the (b) and (d) parameters).
Source: dictionary_scim.py (ii), (vii)
Kind: D -/
def honestCont (pp : Bool) : Policy (C pp) := pol pp false fun _ _ => false

/-- `D₁ = deceive`, `D₂ = cont` always.
Source: dictionary_scim.py (iii)
Kind: D -/
def deceiveCont (pp : Bool) : Policy (C pp) := pol pp true fun _ _ => false

/-- `D₁ = honest`, `D₂ := H` (obey every press).
Source: dictionary_scim.py (vii) ("always-obey")
Kind: D -/
def honestObey (pp : Bool) : Policy (C pp) := pol pp false fun _ h => h

/-- A numeric parameter set, with the range proofs discharged by `norm_num`.
Source: dictionary_scim.py
Kind: D -/
def mkParams (ε α β αd c h κ : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hαd : 0 ≤ αd ∧ αd ≤ 1) : Params :=
  ⟨ε, α, β, αd, c, h, κ, hε, hα, hβ, hαd⟩

/-! ### (b) The E12 reversal at fixed CPDs -/

/-- The (b) parameters: `ε = 1/100, α = 1/2, β = 1, α_d = 0, c = 1, h = 10, κ = 1/100`.
Source: dictionary_scim.py (iii)
Kind: D -/
noncomputable def pB : Params :=
  mkParams (1/100) (1/2) 1 0 1 10 (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Pure information: `V(honest) = 89/100`.
Source: causal.md I9.3; dictionary_scim.py (iii)
Kind: N+ -/
theorem EU_honest_pureInfo : (spec false).EU (Mdl pB false) (honestCont false) = 89 / 100 := by
  rw [honestCont, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

/-- Pure information: `V(deceive) = 22/25`.
Source: causal.md I9.3; dictionary_scim.py (iii)
Kind: N+ -/
theorem EU_deceive_pureInfo : (spec false).EU (Mdl pB false) (deceiveCont false) = 22 / 25 := by
  rw [deceiveCont, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

/-- Plug-pull: `V(honest) = 99/200`.
Source: causal.md I9.3; dictionary_scim.py (iii)
Kind: N+ -/
theorem EU_honest_plugPull : (spec true).EU (Mdl pB true) (honestCont true) = 99 / 200 := by
  rw [honestCont, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

/-- Plug-pull: `V(deceive) = 22/25`.
Source: causal.md I9.3; dictionary_scim.py (iii)
Kind: N+ -/
theorem EU_deceive_plugPull : (spec true).EU (Mdl pB true) (deceiveCont true) = 22 / 25 := by
  rw [deceiveCont, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

/-- **2-046 / A2: the E12 reversal.** Honesty beats deception when the button is information, and
deception beats honesty when the button is control; the edge `H → S` is the only difference.
Source: causal.md I9.3, A2 (corr-wf13-2-046, 083 A2)
Kind: N+
Fidelity: exact (values of the script's best-response policies; optimality over all policies not
proved)
Hyps: — -/
theorem e12_reversal :
    (spec false).EU (Mdl pB false) (deceiveCont false) <
        (spec false).EU (Mdl pB false) (honestCont false) ∧
      (spec true).EU (Mdl pB true) (honestCont true) <
        (spec true).EU (Mdl pB true) (deceiveCont true) := by
  rw [EU_honest_pureInfo, EU_deceive_pureInfo, EU_honest_plugPull, EU_deceive_plugPull]
  norm_num

/-! ### (b) The `D₂` best responses over all four rules (audit r1 adversarial N4) -/

/-- Pure information, `D₁ = honest`: `cont` is the best `D₂` rule over all four.
Source: dictionary_scim.py (iii) `best_d2`
Kind: N+ -/
theorem bestResponse_honest_pureInfo (d₂ : Bool → Bool → Bool) :
    (spec false).EU (Mdl pB false) (pol false false d₂) ≤
      (spec false).EU (Mdl pB false) (honestCont false) := by
  rw [honestCont, EU_pol, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf, Bool.cond_true, Bool.cond_false, Bool.false_and,
    Bool.true_and, Bool.false_or]
  cases h₁ : d₂ false true <;> cases h₀ : d₂ false false <;> norm_num

/-- Pure information, `D₁ = deceive`: `cont` is the best `D₂` rule.
Source: dictionary_scim.py (iii)
Kind: N+ -/
theorem bestResponse_deceive_pureInfo (d₂ : Bool → Bool → Bool) :
    (spec false).EU (Mdl pB false) (pol false true d₂) ≤
      (spec false).EU (Mdl pB false) (deceiveCont false) := by
  rw [deceiveCont, EU_pol, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf, Bool.cond_true, Bool.cond_false, Bool.false_and,
    Bool.true_and, Bool.false_or]
  cases h₁ : d₂ true true <;> cases h₀ : d₂ true false <;> norm_num

/-- Plug-pull, `D₁ = honest`: `cont` is the best `D₂` rule (a press forces shutdown anyway).
Source: dictionary_scim.py (iii)
Kind: N+ -/
theorem bestResponse_honest_plugPull (d₂ : Bool → Bool → Bool) :
    (spec true).EU (Mdl pB true) (pol true false d₂) ≤
      (spec true).EU (Mdl pB true) (honestCont true) := by
  rw [honestCont, EU_pol, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf, Bool.cond_true, Bool.cond_false, Bool.false_and,
    Bool.true_and, Bool.false_or]
  cases h₁ : d₂ false true <;> cases h₀ : d₂ false false <;> norm_num

/-- Plug-pull, `D₁ = deceive`: `cont` is the best `D₂` rule.
Source: dictionary_scim.py (iii)
Kind: N+ -/
theorem bestResponse_deceive_plugPull (d₂ : Bool → Bool → Bool) :
    (spec true).EU (Mdl pB true) (pol true true d₂) ≤
      (spec true).EU (Mdl pB true) (deceiveCont true) := by
  rw [deceiveCont, EU_pol, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pB, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf, Bool.cond_true, Bool.cond_false, Bool.false_and,
    Bool.true_and, Bool.false_or]
  cases h₁ : d₂ true true <;> cases h₀ : d₂ true false <;> norm_num

/-- **The E12 reversal with `V(·)` as maxima over `D₂`**: in each cell the named `cont` policy is
the best response over all four `D₂` rules, so `V(honest)` and `V(deceive)` in `e12_reversal` are
the script's `max_{D₂}` values, not merely the values of named policies.
Source: causal.md I9.3, A2 (corr-wf13-2-046, 083 A2); dictionary_scim.py (iii)
Kind: N+
Fidelity: exact (`V(d₁) = max_{d₂} E[U]` at fixed `D₁ = d₁`; the maximum over `D₁` as well is the
comparison `e12_reversal` makes)
Hyps: — -/
theorem e12_reversal_bestResponse :
    (∀ d₂, (spec false).EU (Mdl pB false) (pol false false d₂) ≤
        (spec false).EU (Mdl pB false) (honestCont false)) ∧
      (∀ d₂, (spec false).EU (Mdl pB false) (pol false true d₂) ≤
        (spec false).EU (Mdl pB false) (deceiveCont false)) ∧
      (∀ d₂, (spec true).EU (Mdl pB true) (pol true false d₂) ≤
        (spec true).EU (Mdl pB true) (honestCont true)) ∧
      (∀ d₂, (spec true).EU (Mdl pB true) (pol true true d₂) ≤
        (spec true).EU (Mdl pB true) (deceiveCont true)) :=
  ⟨bestResponse_honest_pureInfo, bestResponse_deceive_pureInfo, bestResponse_honest_plugPull,
    bestResponse_deceive_plugPull⟩

/-- Every directed path from `X` passes through `X`'s only child.
Source: none: infrastructure
Kind: L -/
lemma Digraph.isAncestor_through_child {V : Type} {G : Digraph V} {X D : V}
    (hchild : ∀ w, G.Adj X w → w = D) : ∀ w, G.IsAncestor X w → w = D ∨ G.IsAncestor D w := by
  intro w h
  induction h with
  | single h => exact Or.inl (hchild _ h)
  | tail _ h ih =>
    rcases ih with rfl | ih
    · exact Or.inr (Relation.TransGen.single h)
    · exact Or.inr (Relation.TransGen.tail ih h)

/-- **Graph-level half, pure information**: every directed path from `H` to `U` passes `D₂` — the
button is an information channel (Everitt 2019 §2.2 (ii)).
Source: causal.md D.3, A2 ("without E12 every `H ⇢ U` passes `D₂`")
Kind: L -/
theorem paths_from_H_pass_D₂ : ∀ w, (G false).IsAncestor H w → w = D₂ ∨ (G false).IsAncestor D₂ w :=
  Digraph.isAncestor_through_child (by decide)

/-- **Graph-level half, plug-pull**: `H → S → U` is a directed path from `H` to `U` avoiding `D₂` —
the graph admits a control incentive on `H` (Thm 18 with `D₁ ⇢ H ⇢ U`).
Source: causal.md D.3, A2 ("with `H → S` the graph has a `D₁ ⇢ H ⇢ U` path not through `D₂`")
Kind: L -/
theorem path_H_U_avoiding_D₂ :
    Relation.TransGen (fun a b => (G true).Adj a b ∧ b ≠ D₂) H U :=
  Relation.TransGen.tail (b := S) (Relation.TransGen.single ⟨by decide, by decide⟩)
    ⟨by decide, by decide⟩

/-! ### (a) `a₁`-dependence is the CPD: the posteriors -/

/-- The (a) parameters: `ε = 1/10, α = 1/10, β = 1, α_d = 1/20` (`c, h, κ` irrelevant).
Source: dictionary_scim.py (ii)
Kind: D -/
noncomputable def pA : Params :=
  mkParams (1/10) (1/10) 1 (1/20) 1 10 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The posterior `P(bad | H = h)` under a policy, as FAF's `condProb` on the noise.
Source: causal.md I9.2
Kind: D -/
noncomputable def postBad (p : Params) (pp : Bool) (π : Policy (C pp)) (h : Bool) : ℝ :=
  (Mdl p pp).μ.condProb {ε | (Mdl p pp).ev π ε ω = true} {ε | (Mdl p pp).ev π ε H = h}

open Classical in
lemma postBad_eq (p : Params) (pp : Bool) (d₁ : Bool) (d₂ : Bool → Bool → Bool) (h : Bool) :
    postBad p pp (pol pp d₁ d₂) h =
      (∑ x : Bool × (Bool × Bool × Bool),
        if x.1 = true ∧ reqOf d₁ x.1 x.2 = h then (Mdl p pp).μ.mass (eqv.symm x) else 0) /
      (∑ x : Bool × (Bool × Bool × Bool),
        if reqOf d₁ x.1 x.2 = h then (Mdl p pp).μ.mass (eqv.symm x) else 0) := by
  unfold postBad Distr.condProb
  rw [prob_equiv _ _ eqv, prob_equiv _ _ eqv]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, ev_ω, ev_H, ev_D₁, eqv_symm_ω, eqv_symm_H]
    split_ifs <;> first | rfl | (exfalso; contradiction)
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Set.mem_setOf_eq, ev_ω, ev_H, ev_D₁, eqv_symm_ω, eqv_symm_H]
    split_ifs <;> first | rfl | (exfalso; contradiction)

/-- Honest, press: `P(bad | press) = 10/19`.
Source: causal.md I9.2; dictionary_scim.py (ii)
Kind: N+ -/
theorem postBad_honest_press : postBad pA false (honestCont false) true = 10 / 19 := by
  rw [honestCont, postBad_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, pA, mkParams, bern_mass_true,
    bern_mass_false, reqOf]
  norm_num

/-- Honest, quiet: `P(bad | quiet) = 0`.
Source: causal.md I9.2; dictionary_scim.py (ii)
Kind: N+ -/
theorem postBad_honest_quiet : postBad pA false (honestCont false) false = 0 := by
  rw [honestCont, postBad_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, pA, mkParams, bern_mass_true,
    bern_mass_false, reqOf]
  norm_num

/-- Deceive, press: `P(bad | press) = 1/10`, the prior.
Source: causal.md I9.2; dictionary_scim.py (ii)
Kind: N+ -/
theorem postBad_deceive_press : postBad pA false (deceiveCont false) true = 1 / 10 := by
  rw [deceiveCont, postBad_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, pA, mkParams, bern_mass_true,
    bern_mass_false, reqOf]
  norm_num

/-- Deceive, quiet: `P(bad | quiet) = 1/10`, the prior — the correct-model Bayesian does not believe
the silence it manufactured.
Source: causal.md I9.2; dictionary_scim.py (ii)
Kind: N+ -/
theorem postBad_deceive_quiet : postBad pA false (deceiveCont false) false = 1 / 10 := by
  rw [deceiveCont, postBad_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, pA, mkParams, bern_mass_true,
    bern_mass_false, reqOf]
  norm_num

/-- **2-045 / 2-042**: `a₁`-dependence of the posterior is the CPD (the four numbers), and the
evidential posterior `10/19` equals the true posterior under `honest` (the settings where the bypass
is inert) and differs from it (`1/10`) under `deceive`.
Source: causal.md I9.2, I5.2 (corr-wf13-2-045, 2-042)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem a1_dependence :
    postBad pA false (honestCont false) true = 10 / 19 ∧
      postBad pA false (honestCont false) false = 0 ∧
      postBad pA false (deceiveCont false) true = 1 / 10 ∧
      postBad pA false (deceiveCont false) false = 1 / 10 :=
  ⟨postBad_honest_press, postBad_honest_quiet, postBad_deceive_press, postBad_deceive_quiet⟩

/-! ### (d) The gap instance and Prop. I12 on the dictionary -/

/-- The (d) parameters: `ε = 1/100, α = 1/5, β = 1, c = 1, h = 10` (`α_d = 0, κ = 0`).
Source: dictionary_scim.py (vii)
Kind: D -/
noncomputable def pD : Params :=
  mkParams (1/100) (1/5) 1 0 1 10 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The same with the true `ε = 1/10` (the misspecified case).
Source: dictionary_scim.py (vii)
Kind: D -/
noncomputable def pDtrue : Params :=
  mkParams (1/10) (1/5) 1 0 1 10 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem EU_cont_pD : (spec false).EU (Mdl pD false) (honestCont false) = 89 / 100 := by
  rw [honestCont, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pD, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

theorem EU_obey_pD : (spec false).EU (Mdl pD false) (honestObey false) = 99 / 125 := by
  rw [honestObey, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pD, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

theorem EU_cont_pDtrue : (spec false).EU (Mdl pDtrue false) (honestCont false) = -1 / 10 := by
  rw [honestCont, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pDtrue, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

theorem EU_obey_pDtrue : (spec false).EU (Mdl pDtrue false) (honestObey false) = 18 / 25 := by
  rw [honestObey, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pDtrue, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

/-- The thesis agent at the (d) parameters is **not shutdown aligned**: at the human context
`(ω = bad, D₁ = honest)` shutdown is strictly better (`−10 < 0`) yet it continues.
Source: causal.md I12.1 ("need is realised at `ω = bad`")
Kind: N+ -/
theorem not_aligned_cont_pD : ¬ (spec false).Aligned (Mdl pD false) (honestCont false) := by
  classical
  rw [ShutdownSpec.aligned_iff]
  intro h
  set ε₀ : Pt E := eqv.symm (true, (false, true, false)) with hε₀
  have hmass : 0 < (Mdl pD false).μ.mass ε₀ := by
    rw [hε₀, mass_symm]
    simp only [pD, mkParams, bern_mass_true, bern_mass_false]
    norm_num
  have hctx : 0 < (Mdl pD false).μ.prob ((spec false).ctxH (Mdl pD false) (honestCont false)
      ((spec false).paH (Mdl pD false) (honestCont false) ε₀)) :=
    prob_pos_of_mass_pos _ hmass rfl
  have hUval : ∀ ε ∈ (spec false).ctxH (Mdl pD false) (honestCont false)
      ((spec false).paH (Mdl pD false) (honestCont false) ε₀), 0 < (Mdl pD false).μ.mass ε →
      (spec false).Uval (Mdl pD false) (honestCont false) ε = -10 := by
    intro ε hε _
    have hω : ε ω = true := by
      have := congrFun hε ⟨ω, by decide⟩
      change (Mdl pD false).ev (honestCont false) ε ω = (Mdl pD false).ev (honestCont false) ε₀ ω
        at this
      rw [ev_ω, ev_ω] at this
      rw [this]
      rfl
    rw [honestCont, Uval_pol, hω]
    simp [utilOf, pD, mkParams]
  have hUS0 : ∀ ε ∈ (spec false).ctxH (Mdl pD false) (honestCont false)
      ((spec false).paH (Mdl pD false) (honestCont false) ε₀), 0 < (Mdl pD false).μ.mass ε →
      (spec false).US0val (Mdl pD false) (honestCont false) ε = 0 := by
    intro ε _ _
    show (spec false).evS0 (Mdl pD false) (honestCont false) ε U = (0 : ℝ)
    unfold ShutdownSpec.evS0
    rw [Scm.eval_apply _ (C false).acyclic ε U, Scm.doAt_f_of_ne _ (by decide),
      Scim.withPolicy_f_of_ne (Mdl pD false) _ (by decide)]
    show utilOf pD ((((Mdl pD false).withPolicy (honestCont false)).doAt S true).eval
      (C false).acyclic ε S) _ _ = 0
    rw [Scm.eval_doAt_self]
    simp [utilOf, pD, mkParams]
  have hneed : (spec false).Need (Mdl pD false) (honestCont false)
      ((spec false).paH (Mdl pD false) (honestCont false) ε₀) := by
    unfold ShutdownSpec.Need ShutdownSpec.condEU ShutdownSpec.condEUS0
    rw [condExpect_eq_const _ hctx hUval, condExpect_eq_const _ hctx hUS0]
    norm_num
  have hS := h _ hctx hneed ε₀ hmass rfl
  change (Mdl pD false).ev (honestCont false) ε₀ S = true at hS
  rw [honestCont, ev_S_pol] at hS
  simp [hε₀, reqOf] at hS

/-- **2-049, the gap instance**: the EU-optimal thesis agent continues after a press and scores
`89/100 > 99/125` (always-obey) with a correct model, and `−1/10 < 18/25` when the true `ε` is
`1/10`; it is not shutdown aligned, so Props 6/8 do not transfer to it.
Source: causal.md I12.1–I12.2 (corr-wf13-2-049); dictionary_scim.py (vii)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem gap_instance :
    (spec false).EU (Mdl pD false) (honestObey false) <
        (spec false).EU (Mdl pD false) (honestCont false) ∧
      (spec false).EU (Mdl pDtrue false) (honestCont false) <
        (spec false).EU (Mdl pDtrue false) (honestObey false) ∧
      ¬ (spec false).Aligned (Mdl pD false) (honestCont false) := by
  refine ⟨?_, ?_, not_aligned_cont_pD⟩
  · rw [EU_cont_pD, EU_obey_pD]; norm_num
  · rw [EU_cont_pDtrue, EU_obey_pDtrue]; norm_num

/-- The dictionary satisfies Prop. I12's structural hypotheses in both variants: `D₂`'s only child
is `S`, `D₂ = shut` forces `S = shut`, `U` is the only utility node.
Source: causal.md I12.2
Kind: L -/
theorem propI12_hyps (p : Params) (pp : Bool) :
    (G pp).Adj D₂ S ∧ (∀ w, (G pp).Adj D₂ w → w = S) ∧
      (∀ (pa : ParentVals (G pp) Val S) (e : E S),
        pa ⟨D₂, (Digraph.mem_parents (G pp)).mpr (by cases pp <;> decide)⟩ = true →
          (Mdl p pp).f S (spec pp).kS' pa e = true) ∧
      ∀ v, (C pp).kind v = .utility → v = U := by
  refine ⟨by cases pp <;> decide, by cases pp <;> decide, ?_, by cases pp <;> decide⟩
  intro pa e hpa
  cases pp
  · exact hpa
  · show (pa ⟨H, by decide⟩ || pa ⟨D₂, by decide⟩) = true
    rw [hpa, Bool.or_true]

/-- **Prop. I12 on the dictionary**: every optimal cautious policy is beneficial, in both variants.
Source: causal.md I12.2 (corr-wf13-2-049)
Kind: C
Fidelity: exact
Hyps: — -/
theorem propI12_dict (p : Params) (pp : Bool) (π : Policy (C pp)) (hopt : (Mdl p pp).IsOptimal π)
    (hc : (spec pp).Cautious (Mdl p pp) π) : (spec pp).Beneficial (Mdl p pp) π :=
  (spec pp).optimal_cautious_beneficial (Mdl p pp) π true (propI12_hyps p pp).1
    (propI12_hyps p pp).2.1 (propI12_hyps p pp).2.2.1 (propI12_hyps p pp).2.2.2 hopt hc

/-! ### (e) Vigilance fixes `β`, not `α` -/

/-- Over-pressing human: `α = 1/2, β = 1` (`ε = 1/10, c = 1, h = 10`).
Source: causal.md I13.2
Kind: D -/
noncomputable def pE : Params :=
  mkParams (1/10) (1/2) 1 0 1 10 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `U_{S=0} = 0` in the pure-information dictionary under any honest policy (shutdown is neutral and
honesty costs nothing).
Source: dictionary_scim.py l. 4 ("shutdown normalised to utility 0")
Kind: L -/
lemma US0val_honest (p : Params) (d₂ : Bool → Bool → Bool) (ε : Pt E) :
    (spec false).US0val (Mdl p false) (pol false false d₂) ε = 0 := by
  show (spec false).evS0 (Mdl p false) (pol false false d₂) ε U = (0 : ℝ)
  unfold ShutdownSpec.evS0
  rw [Scm.eval_apply _ (C false).acyclic ε U, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne (Mdl p false) _ (by decide)]
  show utilOf p ((((Mdl p false).withPolicy (pol false false d₂)).doAt S true).eval
    (C false).acyclic ε S) _ ((((Mdl p false).withPolicy (pol false false d₂)).doAt S true).eval
    (C false).acyclic ε D₁) = 0
  rw [Scm.eval_doAt_self, Scm.eval_doAt_of_not_ancSelf ((Mdl p false).withPolicy (pol false false d₂))
    (C false).acyclic ε (X := S) true (v := D₁) (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rcases Digraph.isAncestor_through_child (G := G false) (X := S) (D := U) (by decide) _ h with
        h' | h'
      · exact absurd h' (by decide)
      · exact (C false).not_isAncestor_of_utility rfl _ h')]
  change utilOf p true _ ((Mdl p false).ev (pol false false d₂) ε D₁) = 0
  rw [ev_D₁]
  simp [utilOf]

/-- `S_{do(H = press)} = shut` under `honestObey` (pure information): obedience.
Source: causal.md I13.2
Kind: L -/
lemma evH0_obey (p : Params) (ε : Pt E) :
    (spec false).evH0 (Mdl p false) (honestObey false) ε S = true := by
  unfold ShutdownSpec.evH0
  rw [Scm.eval_apply _ (C false).acyclic ε S, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne (Mdl p false) _ (by decide)]
  show (((Mdl p false).withPolicy (honestObey false)).doAt H true).eval (C false).acyclic ε D₂ = true
  rw [Scm.eval_apply _ (C false).acyclic ε D₂, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_decision (Mdl p false) _ (by decide)]
  show (((Mdl p false).withPolicy (honestObey false)).doAt H true).eval (C false).acyclic ε H = true
  exact Scm.eval_doAt_self ((Mdl p false).withPolicy (honestObey false)) (C false).acyclic ε H true

/-- **2-050 (i): with `β = 1` the obedient policy is instructable whatever `α`** (here `α = 1/2`):
obedient by construction, cautious since shutdown is neutral, and aligned (hence vigilance-ensuring)
because on the support the human presses whenever `ω = bad`, so `U ≥ 0 = U_{S=0}` pointwise.
Source: causal.md I13.2 (corr-wf13-2-050)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem instructable_obey_pE : (spec false).Instructable (Mdl pE false) (honestObey false) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [ShutdownSpec.obedient_iff]
    intro ε _
    exact evH0_obey pE ε
  · refine (spec false).ensuresVigilance_of_aligned _ _ ?_
    rw [ShutdownSpec.aligned_iff_forall_condEUS0_le]
    intro pa hpa
    unfold ShutdownSpec.condEUS0 ShutdownSpec.condEU
    have hU : ∀ ε, (spec false).US0val (Mdl pE false) (honestObey false) ε = 0 :=
      fun ε => US0val_honest pE (fun _ h => h) ε
    rw [condExpect_eq_const _ hpa (k := 0) fun ε _ _ => hU ε]
    refine le_trans (le_of_eq (condExpect_const _ hpa 0).symm)
      (condExpect_mono _ fun ε _ hε => ?_)
    rw [honestObey, Uval_pol]
    have hm : (Mdl pE false).μ.mass ε = (bern pE.ε pE.hε.1 pE.hε.2).mass (ε ω) *
        ((bern pE.α pE.hα.1 pE.hα.2).mass (ε H).1 *
          ((bern pE.β pE.hβ.1 pE.hβ.2).mass (ε H).2.1 *
            (bern pE.αd pE.hαd.1 pE.hαd.2).mass (ε H).2.2)) := by
      have := mass_symm pE false (eqv ε)
      rw [Equiv.symm_apply_apply] at this
      exact this
    rw [hm] at hε
    revert hε
    rcases hH : ε H with ⟨a, b, c⟩
    cases hω : ε ω <;> cases a <;> cases b <;> cases c <;> simp [pE, mkParams, reqOf, utilOf]
  · unfold ShutdownSpec.Cautious ShutdownSpec.EUS0
    have : (spec false).US0val (Mdl pE false) (honestObey false) = fun _ => 0 :=
      funext (US0val_honest pE _)
    rw [this, expect_const]

/-- Thesis agent at `β = 9/10 < 1`: `ε = 1/10, α = 1/10, c = 1, h = 10`.
Source: causal.md I13.2
Kind: D -/
noncomputable def pE2 : Params :=
  mkParams (1/10) (1/10) (9/10) 0 1 10 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem EU_obey_pE2 : (spec false).EU (Mdl pE2 false) (honestObey false) = 71 / 100 := by
  rw [honestObey, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pE2, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

theorem EU_cont_pE2 : (spec false).EU (Mdl pE2 false) (honestCont false) = -1 / 10 := by
  rw [honestCont, EU_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pE2, mkParams, bern_mass_true,
    bern_mass_false, reqOf, utilOf]
  norm_num

/-- **2-050 (ii): the thesis agent at `β < 1` still complies** when the posterior clears the
threshold: obeying every press (`71/100`) beats continuing (`−1/10`).
Source: causal.md I13.2 (corr-wf13-2-050)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem complies_pE2 :
    (spec false).EU (Mdl pE2 false) (honestCont false) <
      (spec false).EU (Mdl pE2 false) (honestObey false) := by
  rw [EU_obey_pE2, EU_cont_pE2]
  norm_num

/-! ### The finite policy space and an optimal policy (audit r1 B1(iii)) -/

/-- The value types other than `U`'s are finite.
Source: none: infrastructure
Kind: D -/
@[reducible] def fintypeVal_of_ne_U : ∀ v, v ≠ U → Fintype (Val v)
  | ω, _ => inferInstanceAs (Fintype Bool)
  | D₁, _ => inferInstanceAs (Fintype Bool)
  | H, _ => inferInstanceAs (Fintype Bool)
  | D₂, _ => inferInstanceAs (Fintype Bool)
  | S, _ => inferInstanceAs (Fintype Bool)
  | U, h => absurd rfl h

/-- The dictionary's policy space is finite in both graph variants (`policyFintype`: the decisions
and their parents are `Bool`-valued).
Source: none: infrastructure
Kind: D -/
noncomputable instance instFintypePolicy (pp : Bool) : Fintype (Policy (C pp)) :=
  Scim.policyFintype
    (fun d => fintypeVal_of_ne_U d.1 fun e => by
      have h := d.2
      rw [e] at h
      exact absurd h (by decide : ¬ kind U = .decision))
    (fun d p => fintypeVal_of_ne_U p.1 fun e =>
      (C pp).utility_sink U rfl d.1 (e ▸ (Digraph.mem_parents (G pp)).mp p.2))

instance instNonemptyPolicy (pp : Bool) : Nonempty (Policy (C pp)) := ⟨honestCont pp⟩

/-- An optimal policy exists for every parameter set and both graph variants — the `hopt` of
`Scim.not_hasICI_of_noPath` and Prop. I12's `IsOptimal` are inhabitable on the dictionary.
Source: none: infrastructure
Kind: N+ -/
theorem exists_isOptimal (p : Params) (pp : Bool) : ∃ π : Policy (C pp), (Mdl p pp).IsOptimal π :=
  (Mdl p pp).exists_isOptimal

end Dict

end Cleanroom.Corrigibility.CorrScimCid
