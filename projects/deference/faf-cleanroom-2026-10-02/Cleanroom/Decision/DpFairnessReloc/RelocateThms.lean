import Cleanroom.Decision.DpFairnessReloc.Relocate

/-!
# What relocation preserves (T4(a)–(c)): FR-7(a), SE-5(1), SE-7′, FR-6

Package `dp-fairness-reloc`, file 5. All over every finite tree unless said; root site;
`Rel := relocRoot U B`, `C̃ := lift U C`, `π := leafMap U B`.

* **Pre-drawing seeds on any set** (`leafLawSeed_eq_mixture_any`): the memoised walk from `env`
  is the `seedW`-mixture over the tuples `σ ∈ ∏_{d ∈ S} A_d` of the walk with those seeds filled
  in — `dp-core-tree`'s SE-1(a) generalised from `S ⊇ queried B` to arbitrary `S`.
* **SE-5(1)** (`push_leafLaw'`): `π_* μ'_{Rel, C̃} = μ'_{B, C}` for every `C` (Definition 6′ on
  both sides), on every tree.
* **FR-7(a)** (`push_leafLaw_ofFun`): for deterministic `C = ofFun π₀`,
  `π_* μ_{Rel, C̃} = μ_{B, C}` — nested fibers included.
* **Nesting transfer** (`nested_relocRoot`): a positively nested point of `Rel` is a survivor
  `inl d` with `d ∉ U` nested in `B`; so **SE-7′**: if `U` contains every nested point of `B`
  the output is nested nowhere, Definition 6 and 6′ agree on it, and
  `π_* μ_{Rel, C̃} = μ'_{B,C}`, `V_{Rel}(C̃) = V'_B(C)` for every `C` (`push_leafLaw`,
  `value_relocRoot`). Corollary **FR-6**: on almost-fair `B`, for any `U`, `V_{Rel}(C̃) = V_B(C)`
  and the `Ω`-marginal of `ν_{Rel, C̃}` is `ν_{B,C}`.
* `AlmostFair B → AlmostFair Rel` for every `U` (count-level), and `queried Rel` excludes
  `inl d` for `d ∈ U` (`not_mem_U_of_mem_queried_relocRoot`).
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-! ### Pre-drawing the seeds of an arbitrary set of points -/

section mixture

variable (C : Proc ι acts K) (S : Finset ι)

theorem fillEnv_update_of_mem (env : (d : ι) → Option (acts d)) (π : (d : ↥S) → acts d) {d : ι}
    (h : d ∈ S) (b : acts d) : fillEnv S (Function.update env d (some b)) π = fillEnv S env π := by
  funext d'
  unfold fillEnv
  by_cases hd' : d' ∈ S
  · simp [hd']
  · have hne : d' ≠ d := fun heq => hd' (heq ▸ h)
    simp [hd', Function.update_of_ne hne]

theorem fillEnv_update_of_not_mem (env : (d : ι) → Option (acts d)) (π : (d : ↥S) → acts d)
    {d : ι} (h : d ∉ S) (b : acts d) :
    fillEnv S (Function.update env d (some b)) π = Function.update (fillEnv S env π) d (some b) := by
  funext d'
  unfold fillEnv
  by_cases hdd : d' = d
  · subst hdd; simp [h]
  · by_cases hd' : d' ∈ S
    · simp [hd', Function.update_of_ne hdd]
    · simp [hd', Function.update_of_ne hdd]

/-- **Pre-drawing the seeds of any set `S`**: from any environment `env`, the memoised walk is
the mixture over the tuples `π ∈ ∏_{d ∈ S} A_d`, with weights `∏_{d ∈ S} seedW env d (π d)`, of
the memoised walk from `env` with the `S`-seeds filled to `π`.
Source: `seeds.md` SE-5 proof ("condition on the seed tuple"); `dp-core-tree`'s
`leafLawSeed_eq_mixture` (which needs `S ⊇ queried B`) generalised
Kind: P
Fidelity: exact -/
theorem leafLawSeed_eq_mixture_any :
    (B : Tree Ω ι acts K) → ∀ env ℓ,
      leafLawSeed C env B ℓ =
        ∑ π : (d : ↥S) → acts d,
          (∏ d : ↥S, seedW C env d (π d)) * leafLawSeed C (fillEnv S env π) B ℓ
  | .leaf _ _, env, _ => by
      simp only [leafLawSeed_leaf, mul_one]
      rw [sum_prod_pi]
      simp [sum_seedW]
  | .chance _ β child, env, ⟨i, ℓ⟩ => by
      simp only [leafLawSeed_chance, leafLawSeed_eq_mixture_any (child i) env ℓ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun π _ => by ring
  | .decision d child, env, ⟨b, ℓ⟩ => by
      by_cases hd : d ∈ S
      · -- the seed of `d` is among the pre-drawn ones
        have hprod : ∀ π : (d : ↥S) → acts d, ∀ env',
            (∏ d : ↥S, seedW C env' d (π d)) =
              seedW C env' d (π ⟨d, hd⟩) *
                ∏ d ∈ Finset.univ.erase (⟨d, hd⟩ : ↥S), seedW C env' d (π d) :=
          fun π env' => (Finset.mul_prod_erase Finset.univ (fun d : ↥S => seedW C env' d (π d))
            (Finset.mem_univ (⟨d, hd⟩ : ↥S))).symm
        have herase : ∀ π : (d : ↥S) → acts d, ∀ env₁ env₂ : (d : ι) → Option (acts d),
            (∀ d', d' ≠ d → env₁ d' = env₂ d') →
            (∏ d ∈ Finset.univ.erase (⟨d, hd⟩ : ↥S), seedW C env₁ d (π d)) =
              ∏ d ∈ Finset.univ.erase (⟨d, hd⟩ : ↥S), seedW C env₂ d (π d) := by
          intro π env₁ env₂ h
          refine Finset.prod_congr rfl fun d' hd' => ?_
          have hne : (d' : ι) ≠ d := by
            intro heq; apply Finset.ne_of_mem_erase hd'; exact Subtype.ext heq
          simp only [seedW, h d' hne]
        have hfill : ∀ π : (d : ↥S) → acts d, ∀ env' : (d : ι) → Option (acts d),
            leafLawSeed C (fillEnv S env' π) (.decision d child) ⟨b, ℓ⟩ =
              if π ⟨d, hd⟩ = b then leafLawSeed C (fillEnv S env' π) (child b) ℓ else 0 :=
          fun π env' => leafLawSeed_decision_of_some C (fillEnv_of_mem S env' π hd) child b ℓ
        rcases henv : env d with _ | a'
        · rw [leafLawSeed_decision_of_none C henv,
            leafLawSeed_eq_mixture_any (child b) _ ℓ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [hfill, fillEnv_update_of_mem S env π hd b, hprod π env, hprod π,
            herase π (Function.update env d (some b)) env
              (fun d' h => Function.update_of_ne h _ _)]
          rw [seedW_of_some C (show Function.update env d (some b) d = some b by simp) (π ⟨d, hd⟩),
            seedW_of_none C henv (π ⟨d, hd⟩)]
          by_cases hb : π ⟨d, hd⟩ = b
          · rw [hb]; simp only [if_true, one_mul, mul_assoc]
          · simp [hb, Ne.symm hb]
        · rw [leafLawSeed_decision_of_some C henv]
          split_ifs with hab
          · subst hab
            rw [leafLawSeed_eq_mixture_any (child a') env ℓ]
            refine Finset.sum_congr rfl fun π _ => ?_
            rw [hfill, hprod π env, seedW_of_some C henv (π ⟨d, hd⟩)]
            by_cases hb : π ⟨d, hd⟩ = a'
            · rw [hb]; simp only [if_true, one_mul]
            · simp [hb, Ne.symm hb]
          · symm
            apply Finset.sum_eq_zero
            intro π _
            rw [hfill, hprod π env, seedW_of_some C henv (π ⟨d, hd⟩)]
            by_cases hb : π ⟨d, hd⟩ = a'
            · rw [hb]; simp [hab]
            · simp [Ne.symm hb]
      · -- `d` is not pre-drawn: both walks treat it identically
        have hfill : ∀ π : (d : ↥S) → acts d, fillEnv S env π d = env d :=
          fun π => fillEnv_of_not_mem S env π hd
        have hseed : ∀ π : (d : ↥S) → acts d, ∀ b' : acts d,
            (∏ d' : ↥S, seedW C (Function.update env d (some b')) d' (π d')) =
              ∏ d' : ↥S, seedW C env d' (π d') := by
          intro π b'
          refine Finset.prod_congr rfl fun d' _ => ?_
          have hne : (d' : ι) ≠ d := fun heq => hd (heq ▸ d'.2)
          simp only [seedW, Function.update_of_ne hne]
        rcases henv : env d with _ | a'
        · rw [leafLawSeed_decision_of_none C henv,
            leafLawSeed_eq_mixture_any (child b) _ ℓ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun π _ => ?_
          have hf : fillEnv S env π d = none := by rw [hfill π, henv]
          rw [hseed, fillEnv_update_of_not_mem S env π hd b,
            leafLawSeed_decision_of_none C hf]
          ring
        · rw [leafLawSeed_decision_of_some C henv]
          have hR : ∀ π : (d : ↥S) → acts d,
              leafLawSeed C (fillEnv S env π) (.decision d child) ⟨b, ℓ⟩ =
                if a' = b then leafLawSeed C (fillEnv S env π) (child b) ℓ else 0 := fun π => by
            have hf : fillEnv S env π d = some a' := by rw [hfill π, henv]
            exact leafLawSeed_decision_of_some C hf child b ℓ
          simp only [hR]
          split_ifs with hab
          · subst hab
            exact leafLawSeed_eq_mixture_any (child a') env ℓ
          · simp

/-- Definition 6′ as the `U`-tuple mixture of the walks with the `U`-seeds filled in.
Source: `seeds.md` SE-5 proof
Kind: C -/
theorem leafLaw'_eq_sum_fill (U : Finset ι) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    leafLaw' C B ℓ =
      ∑ σ : (d : ↥U) → acts d,
        (∏ d : ↥U, (C d).w (σ d)) * leafLawSeed C (fillEnv U (fun _ => none) σ) B ℓ := by
  unfold leafLaw'
  rw [leafLawSeed_eq_mixture_any C U B (fun _ => none) ℓ]
  simp only [seedW_none]

end mixture

/-! ### The pushforward identities -/

section push

variable (U : Finset ι) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- The leaf map on a leaf of the root-site output, unfolded.
Source: none: infrastructure
Kind: L -/
@[simp] theorem leafMap_mk (σ : (d : ↥U) → acts d) (ℓ' : (resolve U σ B).Leaves) :
    leafMap U B ⟨σ, ℓ'⟩ = leafMapW U (fun ω => (ω, σ)) σ B ℓ' := rfl

/-- The shared-seed law of the relocated tree at a leaf: the product weight of the root draw
times the memoised walk on the resolved branch with the root seed recorded.
Source: `seeds.md` SE-5
Kind: L -/
theorem leafLaw'_relocRoot (σ : (d : ↥U) → acts d) (ℓ' : (resolve U σ B).Leaves) :
    leafLaw' (lift U C) (relocRoot U B) ⟨σ, ℓ'⟩ =
      (∏ d : ↥U, (C d).w (σ d)) *
        leafLawSeed (lift U C) (Function.update (fun _ => none) (.inr ()) (some σ))
          (resolve U σ B) ℓ' := by
  unfold leafLaw' relocRoot
  rw [leafLawSeed_decision_of_none (lift U C) rfl]
  rfl

/-- **SE-5(1): relocation preserves the Definition-6′ law of the input, on every tree.** For
every procedure `C` the canonical leaf map pushes `μ'_{Rel_U B, lift C}` forward to `μ'_{B,C}`
(nested fibers allowed, every `U`).
Source: `seeds.md` SE-5(1) ("For every `C` the canonical leaf map pushes `μ'_{B̃,C̃}`
(Definition 6′ on the output) forward to `μ'_{B,C}`")
Kind: P
Fidelity: exact (root site)
Hyps: none -/
theorem push_leafLaw' (ℓ : B.Leaves) :
    (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
      leafLaw' (lift U C) (relocRoot U B) ℓ' else 0) = leafLaw' C B ℓ := by
  rw [leafLaw'_eq_sum_fill C U B ℓ]
  unfold relocRoot
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hR := resolve_seed_sum U C (fun ω => (ω, σ)) σ B (fillEnv U (fun _ => none) σ)
    (Function.update (fun _ => none) (.inr ()) (some σ))
    (fun d hd => by rw [fillEnv_of_not_mem U _ σ hd]; simp)
    (fun d hd => fillEnv_of_mem U _ σ hd) ℓ
  rw [← hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  have hlaw : leafLaw' (lift U C) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ =
      (∏ d : ↥U, (C d).w (σ d)) *
        leafLawSeed (lift U C) (Function.update (fun _ => none) (.inr ()) (some σ))
          (resolve U σ B) ℓ' := leafLaw'_relocRoot U C B σ ℓ'
  rw [hlaw]
  show (if leafMapW U (fun ω => (ω, σ)) σ B ℓ' = ℓ then (∏ d : ↥U, (C d).w (σ d)) *
      leafLawSeed (lift U C) (Function.update (fun _ => none) (.inr ()) (some σ))
        (resolveW U (fun ω => (ω, σ)) σ B) ℓ' else 0) = _
  split_ifs <;> ring

/-- **FR-7(a): on pure profiles relocation preserves the outcome law always**, nested fibers
included: for deterministic `C = ofFun π₀` the leaf map pushes `μ_{Rel_U B, ofFun (liftFun π₀)}`
forward to `μ_{B, ofFun π₀}`.
Source: `fair-repair.md` FR-7(a) ("On pure profiles, product-root relocation preserves the
outcome law always, nested fibers included"); `adversary-repair.md` Claim F ("FR-7(a)
SURVIVE")
Kind: P
Fidelity: exact
Hyps: none -/
theorem push_leafLaw_ofFun [∀ d, Nonempty (acts d)] (π₀ : (d : ι) → acts d) (ℓ : B.Leaves) :
    (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
      leafLaw (Proc.ofFun (liftFun U π₀)) (relocRoot U B) ℓ' else 0) =
      leafLaw (Proc.ofFun π₀) B ℓ := by
  rw [← leafLaw'_ofFun π₀ B ℓ, ← push_leafLaw' U (Proc.ofFun π₀) B ℓ, lift_ofFun]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  rw [leafLaw'_ofFun]

/-! ### Leaf invariants of the root-site output -/

theorem world_relocRoot (σ : (d : ↥U) → acts d) (ℓ' : (resolve U σ B).Leaves) :
    world (relocRoot U B) ⟨σ, ℓ'⟩ = (world B (leafMap U B ⟨σ, ℓ'⟩), σ) :=
  world_resolveW U (fun ω => (ω, σ)) σ B ℓ'

theorem payoff_relocRoot (σ : (d : ↥U) → acts d) (ℓ' : (resolve U σ B).Leaves) :
    payoff (relocRoot U B) ⟨σ, ℓ'⟩ = payoff B (leafMap U B ⟨σ, ℓ'⟩) :=
  payoff_resolveW U (fun ω => (ω, σ)) σ B ℓ'

theorem chanceWeight_relocRoot (σ : (d : ↥U) → acts d) (ℓ' : (resolve U σ B).Leaves) :
    chanceWeight (relocRoot U B) ⟨σ, ℓ'⟩ = chanceWeight B (leafMap U B ⟨σ, ℓ'⟩) :=
  chanceWeight_resolveW U (fun ω => (ω, σ)) σ B ℓ'

theorem count_inl_relocRoot (d : ι) (σ : (d : ↥U) → acts d) (ℓ' : (resolve U σ B).Leaves) :
    count (.inl d) (relocRoot U B) ⟨σ, ℓ'⟩ =
      if d ∈ U then 0 else count d B (leafMap U B ⟨σ, ℓ'⟩) := by
  show (if (Sum.inr () : ι ⊕ Unit) = .inl d then 1 else 0) +
    count (.inl d) (resolveW U (fun ω => (ω, σ)) σ B) ℓ' = _
  rw [(count_resolveW U (fun ω => (ω, σ)) σ B ℓ').1 d]
  simp only [reduceCtorEq, if_false, zero_add]
  rfl

theorem count_inr_relocRoot (σ : (d : ↥U) → acts d) (ℓ' : (resolve U σ B).Leaves) :
    count (.inr ()) (relocRoot U B) ⟨σ, ℓ'⟩ = 1 := by
  show (if (Sum.inr () : ι ⊕ Unit) = .inr () then 1 else 0) +
    count (.inr ()) (resolveW U (fun ω => (ω, σ)) σ B) ℓ' = 1
  rw [(count_resolveW U (fun ω => (ω, σ)) σ B ℓ').2]
  simp

/-- **An almost-fair input relocates to an almost-fair output, for every `U`** (count level:
survivors' counts are preserved, relocated points vanish, `d̂` is met exactly once).
Source: `seeds.md` SE-5(2) ("the output is almost fair"); `fair-repair.md` FR-4 proof
Kind: P
Fidelity: exact
Hyps: none -/
theorem AlmostFair.reloc_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B) (U : Finset ι) :
    AlmostFair (relocRoot U B) := by
  rintro p ⟨σ, ℓ'⟩
  cases p with
  | inl d =>
      rw [count_inl_relocRoot]
      split_ifs
      · exact Nat.zero_le _
      · exact h d _
  | inr u => cases u; rw [count_inr_relocRoot]

/-- **Nesting transfer**: a positively nested point of `Rel_U B` is a survivor `inl d`, `d ∉ U`,
positively nested in `B`.
Source: `seeds.md` SE-5(2) ("a nested survivor fiber would have been nested in `B`")
Kind: P -/
theorem nested_relocRoot {p : ι ⊕ Unit} (h : Nested (relocRoot U B) p) :
    ∃ d, p = .inl d ∧ d ∉ U ∧ Nested B d := by
  obtain ⟨hcard, ⟨σ, ℓ'⟩, hpos, hc⟩ := h
  cases p with
  | inr u =>
      cases u
      rw [count_inr_relocRoot] at hc
      omega
  | inl d =>
      refine ⟨d, rfl, ?_, ?_⟩
      · intro hd
        rw [count_inl_relocRoot, if_pos hd] at hc
        omega
      · have hd : d ∉ U := by
          intro hd
          rw [count_inl_relocRoot, if_pos hd] at hc
          omega
        rw [count_inl_relocRoot, if_neg hd] at hc
        refine ⟨hcard, leafMap U B ⟨σ, ℓ'⟩, ?_, hc⟩
        unfold Positive at hpos ⊢
        rwa [chanceWeight_relocRoot] at hpos

/-- **SE-7′ (structural half)**: if `U` contains every positively nested point of `B`, the
output is positively nested nowhere.
Source: `seeds.md` SE-7′ ("`U` containing every nested fiber of `B`"), SE-5(2)
Kind: C -/
theorem not_nested_relocRoot (hU : ∀ d, Nested B d → d ∈ U) : ¬ ∃ p, Nested (relocRoot U B) p := by
  rintro ⟨p, hp⟩
  obtain ⟨d, -, hdU, hd⟩ := nested_relocRoot U B hp
  exact hdU (hU d hd)

/-- **SE-7′ / SE-5(2): with `U ⊇ {nested points}`, Definition 6 on the output pushes forward
to Definition 6′ on the input**: `π_* μ_{Rel_U B, lift C} = μ'_{B,C}` for every `C`.
Source: `seeds.md` SE-5(2) ("If `U` contains every nested fiber of `B`, the output is almost
fair, so `μ_{B̃,C̃} = μ'_{B̃,C̃}` (SE-2) and Definition 6 on the output pushes forward to
Definition 6′ on the input"); SE-7′
Kind: C
Fidelity: exact (root site; the hypothesis is the quantifier-repaired one of SE-7′)
Hyps: none -/
theorem push_leafLaw [∀ d, Nonempty (acts d)] (hU : ∀ d, Nested B d → d ∈ U) (ℓ : B.Leaves) :
    (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
      leafLaw (lift U C) (relocRoot U B) ℓ' else 0) = leafLaw' C B ℓ := by
  rw [← push_leafLaw' U C B ℓ]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  rw [leafLaw_eq_leafLaw'_of_not_nested (not_nested_relocRoot U B hU) (lift U C) ℓ']

/-- A payoff-preserving pushforward identity: the value of the output is the pushforward law
integrated against the input's payoffs.
Source: none: infrastructure
Kind: L -/
theorem value_eq_push (C' : Proc (ι ⊕ Unit) (actsR acts U) K) :
    value C' (relocRoot U B) =
      ∑ ℓ, (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
        leafLaw C' (relocRoot U B) ℓ' else 0) * payoff B ℓ := by
  unfold value
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  have hpay : payoff (relocRoot U B) ℓ' = payoff B (leafMap U B ℓ') := by
    obtain ⟨σ, ℓ'⟩ := ℓ'
    exact payoff_relocRoot U B σ ℓ'
  rw [hpay]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The same for the shared-seed value.
Source: none: infrastructure
Kind: L -/
theorem value'_eq_push (C' : Proc (ι ⊕ Unit) (actsR acts U) K) :
    value' C' (relocRoot U B) =
      ∑ ℓ, (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
        leafLaw' C' (relocRoot U B) ℓ' else 0) * payoff B ℓ := by
  unfold value'
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  have hpay : payoff (relocRoot U B) ℓ' = payoff B (leafMap U B ℓ') := by
    obtain ⟨σ, ℓ'⟩ := ℓ'
    exact payoff_relocRoot U B σ ℓ'
  rw [hpay]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **SE-5(1) at the value level**: `V'_{Rel_U B}(lift C) = V'_B(C)` on every tree.
Source: `seeds.md` SE-5(1)
Kind: C -/
theorem value'_relocRoot : value' (lift U C) (relocRoot U B) = value' C B := by
  rw [value'_eq_push]
  unfold value'
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [push_leafLaw']

/-- **SE-7′ at the value level**: with `U ⊇ {nested points}`,
`V_{Rel_U B}(lift C) = V'_B(C)` for every `C` — the relocated (Definition-6) value is the
shared-seed value of the input; the AMD's `4/3` is lost "by the choice of semantics, not by the
surgery".
Source: `seeds.md` SE-7′ ("`V_{Rel_U(B)}(C̃) − V_B(C) = V'_B(C) − V_B(C)`"), SE-5(2)
Kind: C
Fidelity: exact (root site)
Hyps: none -/
theorem value_relocRoot [∀ d, Nonempty (acts d)] (hU : ∀ d, Nested B d → d ∈ U) :
    value (lift U C) (relocRoot U B) = value' C B := by
  rw [value_eq_push]
  unfold value'
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [push_leafLaw U C B hU]

/-- **SE-7′ as a gap identity**: `V_{Rel}(C̃) − V_B(C) = V'_B(C) − V_B(C)`.
Source: `seeds.md` SE-7′
Kind: C -/
theorem value_relocRoot_sub [∀ d, Nonempty (acts d)] (hU : ∀ d, Nested B d → d ∈ U) :
    value (lift U C) (relocRoot U B) - value C B = value' C B - value C B := by
  rw [value_relocRoot U C B hU]

/-- The `Ω`-marginal statistic of the output: the mass of the runs whose (unstamped) world lies
in `X`.
Source: `fair-repair.md` FR-6 ("the `𝓔`-marginal of `ν_{B̃,C̃}`")
Kind: D -/
def nuMarginal [DecidableEq Ω] (C' : Proc (ι ⊕ Unit) (actsR acts U) K) (X : Finset Ω) : K :=
  mass C' (relocRoot U B) (Finset.univ.filter fun ℓ' => (world (relocRoot U B) ℓ').1 ∈ X)

/-- The marginal statistic is the pushforward law on `{λ ⊨ X}`.
Source: none: infrastructure
Kind: L -/
theorem nuMarginal_eq_push [DecidableEq Ω] (C' : Proc (ι ⊕ Unit) (actsR acts U) K) (X : Finset Ω) :
    nuMarginal U B C' X =
      ∑ ℓ ∈ worldEv B X, ∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
        leafLaw C' (relocRoot U B) ℓ' else 0 := by
  unfold nuMarginal mass worldEv
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  have hw : (world (relocRoot U B) ℓ').1 = world B (leafMap U B ℓ') := by
    obtain ⟨σ, ℓ'⟩ := ℓ'
    rw [world_relocRoot]
  rw [hw, Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **SE-7′ at the statistics level**: with `U ⊇ {nested points}`, the `Ω`-marginal of
`ν_{Rel, lift C}` is `ν'_{B,C}`.
Source: `seeds.md` SE-7′; `fair-repair.md` FR-6
Kind: C -/
theorem nuMarginal_relocRoot [DecidableEq Ω] [∀ d, Nonempty (acts d)]
    (hU : ∀ d, Nested B d → d ∈ U) (X : Finset Ω) :
    nuMarginal U B (lift U C) X = nu' C B X := by
  rw [nuMarginal_eq_push]
  unfold nu'
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [push_leafLaw U C B hU]

/-! ### FR-6: on almost-fair inputs relocation preserves everything -/

/-- **FR-6 (run-distribution preservation on almost-fair inputs)**: for `AlmostFair B` and any
`U`, `π_* μ_{Rel_U B, lift C} = μ_{B,C}` for every `C`.
Source: `fair-repair.md` FR-6 ("the pushforward of `μ_{B̃,C̃}` along the canonical leaf map …
equals `μ_{B,C}`"); `adversary-repair.md` Claim F ("FR-6 … SURVIVE")
Kind: C
Fidelity: exact (root site; the hypothesis is `AlmostFair`, the mandate's Definition 24)
Hyps: none -/
theorem AlmostFair.pushLaw_reloc [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (h : AlmostFair B)
    (U : Finset ι) (C : Proc ι acts K) (ℓ : B.Leaves) :
    (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
      leafLaw (lift U C) (relocRoot U B) ℓ' else 0) = leafLaw C B ℓ := by
  rw [push_leafLaw U C B (fun d hd => absurd hd (h.not_nested d)), h.leafLaw_eq_leafLaw' C ℓ]

/-- **FR-6 at the value level**: on almost-fair `B`, `V_{Rel_U B}(lift C) = V_B(C)` for every
`C` and `U`.
Source: `fair-repair.md` FR-6 ("hence `V_{B̃}(C̃) = V_B(C)`")
Kind: C
Fidelity: exact
Hyps: none -/
theorem AlmostFair.value_reloc [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : AlmostFair B) (U : Finset ι) (C : Proc ι acts K) :
    value (lift U C) (relocRoot U B) = value C B := by
  rw [value_relocRoot U C B (fun d hd => absurd hd (h.not_nested d)), h.value_eq_value' C]

/-- **FR-6 at the statistics level**: on almost-fair `B`, the `Ω`-marginal of `ν_{Rel, lift C}`
is `ν_{B,C}`, so surviving points' statistics are untouched.
Source: `fair-repair.md` FR-6 ("the `𝓔`-marginal of `ν_{B̃,C̃}` is `ν_{B,C}`")
Kind: C
Fidelity: exact
Hyps: none -/
theorem AlmostFair.nuMarginal_reloc [DecidableEq Ω] [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} (h : AlmostFair B) (U : Finset ι) (C : Proc ι acts K) (X : Finset Ω) :
    nuMarginal U B (lift U C) X = nu C B X := by
  rw [nuMarginal_relocRoot U C B (fun d hd => absurd hd (h.not_nested d)), h.nu_eq_nu' C X]

/-! ### The queried points of the output -/

/-- A survivor point queried in the output is not a relocated one (`queried_reloc`).
Source: mandate T4 ("`queried (Rel_U B)` must exclude `inl d` for `d ∈ U`")
Kind: L -/
theorem not_mem_U_of_mem_queried_relocRoot [∀ d, Nonempty (acts d)] {d : ι}
    (h : Sum.inl d ∈ queried (relocRoot U B)) : d ∉ U := by
  intro hd
  obtain ⟨⟨σ, ℓ'⟩, hc⟩ := (mem_queried_iff (Sum.inl d) (relocRoot U B)).mp h
  rw [count_inl_relocRoot, if_pos hd] at hc
  exact lt_irrefl _ hc

/-- A survivor point queried in the output is queried in the input.
Source: none: infrastructure
Kind: L -/
theorem mem_queried_of_mem_queried_relocRoot [∀ d, Nonempty (acts d)] {d : ι}
    (h : Sum.inl d ∈ queried (relocRoot U B)) : d ∈ queried B := by
  obtain ⟨⟨σ, ℓ'⟩, hc⟩ := (mem_queried_iff (Sum.inl d) (relocRoot U B)).mp h
  have hd := not_mem_U_of_mem_queried_relocRoot U B h
  rw [count_inl_relocRoot, if_neg hd] at hc
  exact (mem_queried_iff d B).mpr ⟨_, hc⟩

end push

end Cleanroom.Decision.DpFairnessReloc
