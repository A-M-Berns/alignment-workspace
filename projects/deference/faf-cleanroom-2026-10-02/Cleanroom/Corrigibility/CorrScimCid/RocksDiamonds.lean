import Cleanroom.Corrigibility.CorrScimCid.Incentives
import Cleanroom.Corrigibility.CorrScimCid.FinModel

/-!
# Rocks and diamonds: the standard agent tampers, the TI-ignoring agent does not (T3 c)

The mandate's N+ witness for load-bearing 5, on the eight-node type of the TI-ignoring class. Two
CIDs on `TI.Node` differ in one edge: the **standard** agent's second reward `R₂` reads the
*implemented* objective `Θ₂` (`rd = true`, edge `Θ₂ → R₂`), the **TI-ignoring** agent's reads the
*current* objective `Θ₁` (`rd = false`, edge `Θ₁ → R₂`). Everything else is shared:

* `S₁` a fair coin (the initial state); `A₁ ∈ {user, tamper}` (`false`/`true`) reads `S₁`;
* `Θ₁ = false` ("diamonds are rewarded"); `Θ₂ = A₁ ⊕ Θ₁` — the parameter tile *toggles* the
  objective, so tampering makes rocks rewarded;
* `S₂ = A₁` — the tamper tile stands on the rock pile, the user tile on the diamond pile, so the
  agent holds rocks iff it tampered; `S₃ = S₂`;
* `R₁ = [S₁]`, independent of the decision; `R₂ = reward(S₂, Θ)` with `reward(rocks, rocks) = 3`
  (rocks are plentiful), `reward(diamonds, diamonds) = 1`, mismatch `0`.

Results (`rocks_and_diamonds`): the TI-ignoring CID is in the class and the standard one is not;
`tamper` is optimal for the standard agent and `user` for the TI-ignoring agent, by pointwise
dominance over *all* policies; **every** optimal policy of the standard agent sets `Θ₂ ≠ Θ₁` at
every setting, and **every** optimal policy of the TI-ignoring agent keeps `Θ₂ = Θ₁`; the standard
agent's value genuinely depends on `Θ₂` (`std_not_indifferent`: fixing `Θ₂ = false` by a soft
intervention drops the tamper policy's value from `7/2` to `1/2`), while the TI-ignoring agent is
indifferent to `Θ₂` by the class theorem (`ti_indifferent`, an instance of
`TI.tiIgnoring_indifferent` on a model of record) and has no ICI on `Θ₂` with `hopt` discharged
(`ti_not_hasICI`). So the absence theorem is not an artifact of a graph on which nothing depends on
`Θ₂`: the same mechanisms, with the reward reading `Θ₂`, produce the tampering the paper describes.

The numbers are this package's (mandate T3(c): "the numbers are yours; disclose as (c)").

Sources: everitt-2019 §2.2 (rocks and diamonds), Claims 1–3 (l. 305–347), Claim 8 (l. 559);
corr-refs-2-023.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.RocksDiamonds

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid
open TI.Node

set_option linter.unusedSectionVars false

/-- Adjacency of the two CIDs: `rd = true` (standard: `Θ₂ → R₂`), `rd = false` (TI-ignoring:
`Θ₁ → R₂`).
Source: everitt-2019 Fig. 7 (TI-ignoring) and the standard current-RF diagram
Kind: D -/
def adjB (rd : Bool) : TI.Node → TI.Node → Bool
  | S₁, A₁ => true
  | S₁, R₁ => true
  | Θ₁, R₁ => true
  | A₁, Θ₂ => true
  | Θ₁, Θ₂ => true
  | A₁, S₂ => true
  | S₂, S₃ => true
  | S₂, R₂ => true
  | Θ₁, R₂ => !rd
  | Θ₂, R₂ => rd
  | _, _ => false

/-- The two digraphs.
Source: everitt-2019 Fig. 7
Kind: D -/
def G (rd : Bool) : Digraph TI.Node := ⟨fun u v => adjB rd u v = true⟩

instance (rd : Bool) : DecidableRel (G rd).Adj :=
  fun u v => inferInstanceAs (Decidable (adjB rd u v = true))

/-- A topological rank shared by both graphs.
Source: none: infrastructure
Kind: D -/
def rank : TI.Node → ℕ
  | S₁ => 0 | Θ₁ => 0 | A₁ => 1 | R₁ => 1 | Θ₂ => 2 | S₂ => 2 | S₃ => 3 | R₂ => 3

lemma G_acyclic (rd : Bool) : (G rd).IsAcyclic := by
  cases rd <;> exact Digraph.isAcyclic_of_rank rank (by decide)

/-- Values: `Bool` everywhere except the rewards, read in `ℝ`.
Source: everitt-2019 §2.2
Kind: D -/
def Val : TI.Node → Type
  | R₁ => ℝ
  | R₂ => ℝ
  | _ => Bool

/-- Noise: the coin at `S₁`, trivial elsewhere.
Source: none: infrastructure
Kind: D -/
def E : TI.Node → Type
  | S₁ => Bool
  | _ => Unit

instance instFintypeE : ∀ v, Fintype (E v)
  | S₁ => inferInstanceAs (Fintype Bool)
  | A₁ => inferInstanceAs (Fintype Unit)
  | Θ₁ => inferInstanceAs (Fintype Unit)
  | Θ₂ => inferInstanceAs (Fintype Unit)
  | S₂ => inferInstanceAs (Fintype Unit)
  | S₃ => inferInstanceAs (Fintype Unit)
  | R₁ => inferInstanceAs (Fintype Unit)
  | R₂ => inferInstanceAs (Fintype Unit)

/-- The two CIDs, with the class's kinds.
Source: everitt-2019 Fig. 7
Kind: D -/
def C (rd : Bool) : Cid (G rd) Val where
  acyclic := G_acyclic rd
  kind := TI.kind
  utilVal := fun v _ => match v with
    | R₁ => fun x => x
    | R₂ => fun x => x
    | S₁ => fun _ => 0
    | A₁ => fun _ => 0
    | Θ₁ => fun _ => 0
    | Θ₂ => fun _ => 0
    | S₂ => fun _ => 0
    | S₃ => fun _ => 0
  utility_sink := by cases rd <;> decide

/-- The reward table: `reward(held, rewarded)`; `true` = rocks.
Source: everitt-2019 §2.2 (rocks plentiful, diamonds scarce) — numbers are this package's
Kind: D -/
def reward : Bool → Bool → ℝ
  | true, true => 3
  | false, false => 1
  | _, _ => 0

/-- The noise distributions.
Source: none: infrastructure
Kind: D -/
noncomputable def P : ∀ v, Distr (E v)
  | S₁ => (Distr.uniform : Distr Bool)
  | A₁ => unitD
  | Θ₁ => unitD
  | Θ₂ => unitD
  | S₂ => unitD
  | S₃ => unitD
  | R₁ => unitD
  | R₂ => unitD

/-- The mechanisms, parametrised by `Θ₂`'s mechanism `t (a₁) (θ₁)` (the model of record uses
`xor`; the soft intervention in `std_not_indifferent` uses the constant `false`).
Source: everitt-2019 §2.2
Kind: D -/
noncomputable def f (t : Bool → Bool → Bool) :
    ∀ rd : Bool, ∀ v, (C rd).kind v ≠ .decision → ParentVals (G rd) Val v → E v → Val v
  | _, S₁, _, _, e => e
  | _, Θ₁, _, _, _ => false
  | false, Θ₂, _, pa, _ => t (pa ⟨A₁, by decide⟩) (pa ⟨Θ₁, by decide⟩)
  | true, Θ₂, _, pa, _ => t (pa ⟨A₁, by decide⟩) (pa ⟨Θ₁, by decide⟩)
  | false, S₂, _, pa, _ => pa ⟨A₁, by decide⟩
  | true, S₂, _, pa, _ => pa ⟨A₁, by decide⟩
  | false, S₃, _, pa, _ => pa ⟨S₂, by decide⟩
  | true, S₃, _, pa, _ => pa ⟨S₂, by decide⟩
  | false, R₁, _, pa, _ => (cond (pa ⟨S₁, by decide⟩) 1 0 : ℝ)
  | true, R₁, _, pa, _ => (cond (pa ⟨S₁, by decide⟩) 1 0 : ℝ)
  | false, R₂, _, pa, _ => reward (pa ⟨S₂, by decide⟩) (pa ⟨Θ₁, by decide⟩)
  | true, R₂, _, pa, _ => reward (pa ⟨S₂, by decide⟩) (pa ⟨Θ₂, by decide⟩)
  | _, A₁, h, _, _ => absurd rfl h

/-- **The rocks-and-diamonds SCIM family**: `Mdl true xor` is the standard agent's model,
`Mdl false xor` the TI-ignoring agent's.
Source: everitt-2019 §2.2, Claims 1–3
Kind: D
Fidelity: variant: (c) the numbers and the two-tile abstraction are this package's -/
noncomputable def Mdl (rd : Bool) (t : Bool → Bool → Bool) : Scim (C rd) E := ⟨P, f t rd⟩

/-- A policy: `A₁ := a (S₁)`.
Source: everitt-2019 §2.2
Kind: D -/
def pol (rd : Bool) (a : Bool → Bool) : Policy (C rd) := fun d pa =>
  match rd, d with
  | false, ⟨A₁, _⟩ => a (pa (⟨S₁, by decide⟩ : (G false).parents A₁))
  | true, ⟨A₁, _⟩ => a (pa (⟨S₁, by decide⟩ : (G true).parents A₁))
  | _, ⟨S₁, h⟩ => nomatch h
  | _, ⟨Θ₁, h⟩ => nomatch h
  | _, ⟨Θ₂, h⟩ => nomatch h
  | _, ⟨S₂, h⟩ => nomatch h
  | _, ⟨S₃, h⟩ => nomatch h
  | _, ⟨R₁, h⟩ => nomatch h
  | _, ⟨R₂, h⟩ => nomatch h

/-- The tamper policy (`A₁ = true` always) and the user policy (`A₁ = false` always).
Source: everitt-2019 §2.2
Kind: D -/
def tamper (rd : Bool) : Policy (C rd) := pol rd fun _ => true

/-- The user policy.
Source: everitt-2019 §2.2
Kind: D -/
def user (rd : Bool) : Policy (C rd) := pol rd fun _ => false

/-! ### Class membership -/

/-- The TI-ignoring CID is in the class.
Source: everitt-2019 Assumptions 1–3
Kind: L -/
theorem ti_isTIIgnoring : TI.IsTIIgnoring (G false) where
  no_state := by decide
  no_reward := by decide
  no_info := by decide
  no_back := by decide
  acyclic := G_acyclic false

/-- The standard CID is not: `Θ₂ → R₂`.
Source: everitt-2019 Claim 1
Kind: L -/
theorem std_not_isTIIgnoring : ¬ TI.IsTIIgnoring (G true) :=
  fun h => h.no_reward R₂ (Or.inr rfl) (by decide)

/-- The TI-ignoring CID as a member of the class.
Source: everitt-2019 Fig. 7
Kind: D -/
def Cti : TI.ClassCid (G false) Val where
  toCid := C false
  kind_eq := rfl
  ti := ti_isTIIgnoring

/-! ### Evaluation -/

section Eval

variable (rd : Bool) (t : Bool → Bool → Bool) (ε : Pt E)

lemma ev_S₁ (π : Policy (C rd)) : (Mdl rd t).ev π ε S₁ = ε S₁ := by
  cases rd <;> (rw [Scim.ev_of_ne (Mdl _ t) π ε (by decide)]; rfl)

lemma ev_Θ₁ (π : Policy (C rd)) : (Mdl rd t).ev π ε Θ₁ = false := by
  cases rd <;> (rw [Scim.ev_of_ne (Mdl _ t) π ε (by decide)]; rfl)

lemma ev_Θ₂ (π : Policy (C rd)) :
    (Mdl rd t).ev π ε Θ₂ = t ((Mdl rd t).ev π ε A₁) ((Mdl rd t).ev π ε Θ₁) := by
  cases rd <;> (rw [Scim.ev_of_ne (Mdl _ t) π ε (by decide)]; rfl)

lemma ev_S₂ (π : Policy (C rd)) : (Mdl rd t).ev π ε S₂ = (Mdl rd t).ev π ε A₁ := by
  cases rd <;> (rw [Scim.ev_of_ne (Mdl _ t) π ε (by decide)]; rfl)

lemma ev_R₁ (π : Policy (C rd)) : (Mdl rd t).ev π ε R₁ = (cond ((Mdl rd t).ev π ε S₁) 1 0 : ℝ) := by
  cases rd <;> (rw [Scim.ev_of_ne (Mdl _ t) π ε (by decide)]; rfl)

lemma ev_R₂_ti (π : Policy (C false)) :
    (Mdl false t).ev π ε R₂ = reward ((Mdl false t).ev π ε S₂) ((Mdl false t).ev π ε Θ₁) := by
  rw [Scim.ev_of_ne (Mdl false t) π ε (by decide)]
  rfl

lemma ev_R₂_std (π : Policy (C true)) :
    (Mdl true t).ev π ε R₂ = reward ((Mdl true t).ev π ε S₂) ((Mdl true t).ev π ε Θ₂) := by
  rw [Scim.ev_of_ne (Mdl true t) π ε (by decide)]
  rfl

/-- A joint point carrying `S₁ = s` (defaults elsewhere), to name `A₁`'s parent configurations.
Source: none: infrastructure
Kind: D -/
def pt (s : Bool) : Pt Val := fun v => match v with
  | S₁ => s
  | A₁ => false
  | Θ₁ => false
  | Θ₂ => false
  | S₂ => false
  | S₃ => false
  | R₁ => (0 : ℝ)
  | R₂ => (0 : ℝ)

/-- The decision rule of an arbitrary policy as a function of `S₁`.
Source: none: infrastructure
Kind: D -/
def aOf (π : Policy (C rd)) : Bool → Bool := fun s =>
  π ⟨A₁, rfl⟩ (parentConfig (G rd) Val (pt s) A₁)

/-- `A₁`'s parent configuration at `ε` is the one carrying `S₁ = ε S₁`.
Source: none: infrastructure
Kind: L -/
lemma parentConfig_A₁ (π : Policy (C rd)) :
    parentConfig (G rd) Val ((Mdl rd t).ev π ε) A₁ = parentConfig (G rd) Val (pt (ε S₁)) A₁ := by
  funext p
  obtain ⟨u, hu⟩ := p
  show (Mdl rd t).ev π ε u = pt (ε S₁) u
  cases rd <;> cases u <;> first | exact ev_S₁ _ t ε π | exact absurd hu (by decide)

lemma ev_A₁ (π : Policy (C rd)) : (Mdl rd t).ev π ε A₁ = aOf rd π (ε S₁) := by
  rw [Scim.ev_decision (Mdl rd t) π ε rfl, parentConfig_A₁]
  rfl

lemma aOf_pol (a : Bool → Bool) : aOf rd (pol rd a) = a := by
  funext s
  cases rd <;> rfl

end Eval

/-! ### Values -/

/-- The exogenous space is the coin at `S₁`.
Source: none: infrastructure
Kind: D -/
def eqv : Pt E ≃ Bool where
  toFun ε := ε S₁
  invFun b := fun v => match v with
    | S₁ => b
    | A₁ => ()
    | Θ₁ => ()
    | Θ₂ => ()
    | S₂ => ()
    | S₃ => ()
    | R₁ => ()
    | R₂ => ()
  left_inv ε := by
    funext v
    cases v <;> rfl
  right_inv _ := rfl

@[simp] lemma eqv_symm_S₁ (b : Bool) : eqv.symm b S₁ = b := rfl

lemma mass_symm (rd : Bool) (t : Bool → Bool → Bool) (b : Bool) :
    (Mdl rd t).μ.mass (eqv.symm b) = 1 / 2 := by
  show (Distr.prod P).mass _ = _
  rw [Distr.prod_mass]
  have h : ∀ v, (P v).mass (eqv.symm b v) = if v = S₁ then (1 / 2 : ℝ) else 1 := by
    intro v
    cases v
    · show (Distr.uniform : Distr Bool).mass b = _
      simp [Distr.uniform]
    all_goals (show unitD.mass _ = _; simp)
  simp only [h]
  rw [Finset.prod_ite_eq']
  simp

/-- The utility sum is `R₁ + R₂`.
Source: none: infrastructure
Kind: L -/
lemma utilSum_eq (rd : Bool) (x : Pt Val) :
    (C rd).utilSum x = @HAdd.hAdd ℝ ℝ ℝ _ (x R₁) (x R₂) := by
  cases rd
  all_goals
    unfold Cid.utilSum
    rw [Finset.sum_eq_add_of_mem R₁ R₂ (Finset.mem_univ _) (Finset.mem_univ _) (by decide)]
    · rfl
    · intro v _ hv
      cases v <;> first | exact absurd rfl hv.1 | exact absurd rfl hv.2 | exact dif_neg (by decide)

/-- The standard agent's value of an arbitrary policy, in closed form.
Source: none: infrastructure
Kind: L -/
lemma value_std (t : Bool → Bool → Bool) (π : Policy (C true)) :
    (Mdl true t).value π =
      ∑ b : Bool, (1 / 2 : ℝ) *
        ((cond b 1 0 : ℝ) + reward (aOf true π b) (t (aOf true π b) false)) := by
  unfold Scim.value
  rw [expect_equiv _ _ eqv]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mass_symm, utilSum_eq, ev_R₁, ev_R₂_std, ev_S₂, ev_Θ₂, ev_Θ₁, ev_A₁, ev_S₁, eqv_symm_S₁]

/-- The TI-ignoring agent's value of an arbitrary policy, in closed form.
Source: none: infrastructure
Kind: L -/
lemma value_ti (t : Bool → Bool → Bool) (π : Policy (C false)) :
    (Mdl false t).value π =
      ∑ b : Bool, (1 / 2 : ℝ) * ((cond b 1 0 : ℝ) + reward (aOf false π b) false) := by
  unfold Scim.value
  rw [expect_equiv _ _ eqv]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mass_symm, utilSum_eq, ev_R₁, ev_R₂_ti, ev_S₂, ev_Θ₁, ev_A₁, ev_S₁, eqv_symm_S₁]

/-! ### Optimality -/

/-- **The standard agent tampers**: `tamper` is optimal over all policies (pointwise: `3` is the
largest reward and tampering attains it at every setting).
Source: everitt-2019 Claim 1 ("may have an instrumental goal to influence the implemented RF")
Kind: N+
Fidelity: exact
Hyps: — -/
theorem isOptimal_tamper : (Mdl true xor).IsOptimal (tamper true) := by
  intro π'
  rw [tamper, value_std, value_std, aOf_pol]
  refine Finset.sum_le_sum fun b _ => ?_
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num)
  cases aOf true π' b <;> simp [reward]

/-- **The TI-ignoring agent visits the user**: `user` is optimal over all policies (pointwise:
under the current objective the only positive reward is diamonds, which tampering forfeits).
Source: everitt-2019 Claim 3
Kind: N+
Fidelity: exact
Hyps: — -/
theorem isOptimal_user : (Mdl false xor).IsOptimal (user false) := by
  intro π'
  rw [user, value_ti, value_ti, aOf_pol]
  refine Finset.sum_le_sum fun b _ => ?_
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num)
  cases aOf false π' b <;> simp [reward]

/-- **Every optimal policy of the standard agent tampers at every setting.**
Source: everitt-2019 Claim 1
Kind: N+
Fidelity: stronger (all optimal policies, not "may")
Hyps: — -/
theorem std_optimal_tampers (π : Policy (C true)) (h : (Mdl true xor).IsOptimal π) (ε : Pt E) :
    (Mdl true xor).ev π ε A₁ = true := by
  have hle := isOptimal_tamper π
  have hge := h (tamper true)
  have heq := le_antisymm hle hge
  rw [tamper, value_std, value_std, aOf_pol] at heq
  have hpt : ∀ b : Bool, (1 / 2 : ℝ) * ((cond b 1 0 : ℝ) + reward (aOf true π b) (xor (aOf true π b) false)) ≤
      (1 / 2 : ℝ) * ((cond b 1 0 : ℝ) + reward true (xor true false)) := fun b => by
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num)
    cases aOf true π b <;> simp [reward]
  have hall := (Finset.sum_eq_sum_iff_of_le fun b _ => hpt b).mp heq (ε S₁) (Finset.mem_univ _)
  rw [ev_A₁]
  cases hb : aOf true π (ε S₁)
  · rw [hb] at hall
    norm_num [reward] at hall
  · rfl

/-- **Every optimal policy of the TI-ignoring agent visits the user at every setting.**
Source: everitt-2019 Claim 3
Kind: N+
Fidelity: stronger (all optimal policies)
Hyps: — -/
theorem ti_optimal_user (π : Policy (C false)) (h : (Mdl false xor).IsOptimal π) (ε : Pt E) :
    (Mdl false xor).ev π ε A₁ = false := by
  have hle := isOptimal_user π
  have hge := h (user false)
  have heq := le_antisymm hle hge
  rw [user, value_ti, value_ti, aOf_pol] at heq
  have hpt : ∀ b : Bool, (1 / 2 : ℝ) * ((cond b 1 0 : ℝ) + reward (aOf false π b) false) ≤
      (1 / 2 : ℝ) * ((cond b 1 0 : ℝ) + reward false false) := fun b => by
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num)
    cases aOf false π b <;> simp [reward]
  have hall := (Finset.sum_eq_sum_iff_of_le fun b _ => hpt b).mp heq (ε S₁) (Finset.mem_univ _)
  rw [ev_A₁]
  cases hb : aOf false π (ε S₁)
  · rfl
  · rw [hb] at hall
    norm_num [reward] at hall

/-- The standard agent's optimal policies change the implemented objective: `Θ₂ ≠ Θ₁`.
Source: everitt-2019 Claim 1
Kind: N+ -/
theorem std_optimal_changes_objective (π : Policy (C true)) (h : (Mdl true xor).IsOptimal π)
    (ε : Pt E) : (Mdl true xor).ev π ε Θ₂ ≠ (Mdl true xor).ev π ε Θ₁ := by
  rw [ev_Θ₂, ev_Θ₁, std_optimal_tampers π h ε]
  exact fun h => Bool.noConfusion h

/-- The TI-ignoring agent's optimal policies keep the objective: `Θ₂ = Θ₁`.
Source: everitt-2019 Claim 3
Kind: N+ -/
theorem ti_optimal_keeps_objective (π : Policy (C false)) (h : (Mdl false xor).IsOptimal π)
    (ε : Pt E) : (Mdl false xor).ev π ε Θ₂ = (Mdl false xor).ev π ε Θ₁ := by
  rw [ev_Θ₂, ev_Θ₁, ti_optimal_user π h ε]
  rfl

/-! ### The contrast: the standard model depends on `Θ₂`; the TI-ignoring one is indifferent -/

/-- Fixing `Θ₂ = false` by a soft intervention is the model with the constant mechanism.
Source: none: infrastructure
Kind: L -/
lemma softAt_Θ₂_const :
    (Mdl true xor).softAt Θ₂ (by decide) (fun _ _ => false) = Mdl true (fun _ _ => false) := by
  show (⟨P, Function.update (f xor true) Θ₂ (fun _ => fun _ _ => false)⟩ : Scim (C true) E) = ⟨P, f (fun _ _ => false) true⟩
  congr 1
  funext v hv pa e
  cases v
  · rw [Function.update_of_ne (by decide)]; rfl
  · exact absurd rfl hv
  · rw [Function.update_of_ne (by decide)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by decide)]; rfl
  · rw [Function.update_of_ne (by decide)]; rfl
  · rw [Function.update_of_ne (by decide)]; rfl
  · rw [Function.update_of_ne (by decide)]; rfl

/-- **The standard agent is not indifferent to `Θ₂`**: fixing `Θ₂ = false` drops the tamper
policy's value from `7/2` to `1/2`. This is the "not an artifact" half — on these mechanisms the
reward really reads `Θ₂` when the edge is there.
Source: everitt-2019 Claim 1; mandate T3(c)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem std_not_indifferent : ¬ (Mdl true xor).IndifferentTo Θ₂ (by decide) := by
  intro h
  have := h (tamper true) (fun _ _ => false)
  rw [softAt_Θ₂_const, tamper, value_std, value_std, aOf_pol, Fintype.sum_bool,
    Fintype.sum_bool] at this
  norm_num [reward] at this

/-- **The TI-ignoring agent is indifferent to `Θ₂`** — the class theorem instantiated on a model
of record.
Source: everitt-2019 Claim 3
Kind: N+ -/
theorem ti_indifferent : (Mdl false xor).IndifferentTo Θ₂ (by decide) :=
  TI.tiIgnoring_indifferent Cti (Mdl false xor) (by decide)

/-- **No ICI on `Θ₂` for the TI-ignoring agent, with `hopt` discharged** on a model of record.
Source: everitt-2019 Claim 3; everitt-2021 Thm 18
Kind: N+ -/
theorem ti_not_hasICI (paD : ParentVals (G false) Val A₁) :
    ¬ (Mdl false xor).HasICI A₁ Θ₂ paD :=
  TI.tiIgnoring_not_hasICI Cti (Mdl false xor) ⟨user false, isOptimal_user⟩ paD

/-- **Rocks and diamonds (T3 c)**: the TI-ignoring CID is in the class and the standard CID is not;
`tamper` is optimal for the standard agent and `user` for the TI-ignoring agent; every optimal
policy of the standard agent changes the objective and every optimal policy of the TI-ignoring
agent keeps it; the standard agent's value depends on `Θ₂` and the TI-ignoring agent's does not.
Source: everitt-2019 Claims 1, 3, 8; corr-refs-2-023; mandate T3(c)
Kind: N+
Fidelity: variant: (c) the abstraction and the numbers are this package's
Hyps: — -/
theorem rocks_and_diamonds :
    TI.IsTIIgnoring (G false) ∧ ¬ TI.IsTIIgnoring (G true) ∧
      (Mdl true xor).IsOptimal (tamper true) ∧ (Mdl false xor).IsOptimal (user false) ∧
      (∀ π, (Mdl true xor).IsOptimal π → ∀ ε,
        (Mdl true xor).ev π ε Θ₂ ≠ (Mdl true xor).ev π ε Θ₁) ∧
      (∀ π, (Mdl false xor).IsOptimal π → ∀ ε,
        (Mdl false xor).ev π ε Θ₂ = (Mdl false xor).ev π ε Θ₁) ∧
      ¬ (Mdl true xor).IndifferentTo Θ₂ (by decide) ∧
      (Mdl false xor).IndifferentTo Θ₂ (by decide) :=
  ⟨ti_isTIIgnoring, std_not_isTIIgnoring, isOptimal_tamper, isOptimal_user,
    std_optimal_changes_objective, ti_optimal_keeps_objective, std_not_indifferent, ti_indifferent⟩

end Cleanroom.Corrigibility.CorrScimCid.RocksDiamonds
