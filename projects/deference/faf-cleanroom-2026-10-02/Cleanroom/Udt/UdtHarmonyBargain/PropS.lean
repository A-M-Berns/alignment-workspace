import Cleanroom.Udt.UdtHarmonyBargain.Harmony
import Cleanroom.Udt.UdtHarmonyBargain.Support

/-!
# `udt-harmony-bargain` — Proposition S: homogeneous harmony is optimality as a value (T7)

In a common-payoff game (`commonGame V`, every player's utility `V`) with any welfare selection
rule, every trembling-hand outcome of the bargaining game is `V`-optimal (`harmonious_subset_optimal`,
HA-5′(a), re-derived); with no safe batna and `W` injective on the optima the outcome is unique
and `W`-maximal among the optima (`unique_without_safe_batna`, HA-5′). This is the route to
SC Thm 13.1(2) that avoids the false Theorem 11.1.

Grade: pure / shared-seed. Support form: "outcome of `p*`" means the outcome of every pure profile
of positive `profWeight` under `p*` (mandate §3).

Proof of (a) (HA-5′): fix an optimum `O†`. *Lemma A*: adding `O†` to one's acceptable set never
lowers the value against any pure profile (the outcome changes only from a batna profile or a deal
with `W < W(O†)` to a `W`-maximiser of a set containing `O†`, which is optimal since
Pareto-consistency with common utility puts every non-optimum strictly below every optimum in
`W`); against the profile where the others accept exactly `{O†}` with batnas completing a
non-optimal outcome, it is strict unless the batna is safe. *Lemma B*: hence in every perturbed
equilibrium such a proposal carries only the floor weight, so it has weight `0` in the limit: every
support proposal accepts `O†` or has a safe batna. *Conclusion*: if all accept `O†` the deal is a
`W`-maximiser of a set containing `O†`, hence optimal; otherwise a safe-batna player who does not
accept `O†` sees a non-optimal deal and improves strictly by `(bⱼ, ∅)`, contradicting
`THPE.isMixedNashEq`. Lemma B needs a second player; with one player the support strategy is
a best response (`THPE.support_isBestResponse`) and `(b, {O†})` beats a non-optimal outcome.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements StrategicGame Filter Topology

variable {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
variable {A : N → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- `O` is `V`-optimal (`O ∈ M`).
Source: [[superconditioning-mismatched-ontologies]] §13.1 Thm 13.1(2) (`argmax`); HA-5′ (`M`)
Kind: D -/
def IsOpt (V : Outcome A → ℝ) (O : Outcome A) : Prop := ∀ O', V O' ≤ V O

/-- A batna `b` of player `j` is **safe** if every outcome with `j`-coordinate `b` is optimal.
Source: HA-5′ ("safe batna")
Kind: D -/
def Safe (V : Outcome A → ℝ) (j : N) (b : A j) : Prop := ∀ O : Outcome A, O j = b → IsOpt V O

/-- The strategic form of the bargaining game of the common-payoff game `V`.
Source: none: infrastructure
Kind: D -/
abbrev BG (V : Outcome A → ℝ) (sel : Finset (Outcome A) → Outcome A) : StrategicGame N ℝ :=
  (bargain (commonGame V) sel).toStrategic

variable {V : Outcome A → ℝ} {sel : Finset (Outcome A) → Outcome A} {W : Outcome A → ℝ}

theorem BG_payoff (τ : (BG V sel).Profile) (j : N) :
    (BG V sel).payoff τ j =
      V (outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ)) := rfl

/-- Pareto-consistency with common utility puts every non-optimum strictly below every optimum.
Source: HA-5′ (Lemma A's key step)
Kind: P
Hyps: (a) `Nonempty N` -/
theorem nonopt_lt_opt_W (hW : IsWelfareSel (commonGame V) sel W) {O Od : Outcome A}
    (hO : ¬ IsOpt V O) (hOd : IsOpt V Od) : W O < W Od := by
  apply hW.1
  rw [paretoDom_commonGame_iff]
  unfold IsOpt at hO
  push_neg at hO
  obtain ⟨O', hO'⟩ := hO
  exact lt_of_lt_of_le hO' (hOd O')

theorem isOpt_of_W_ge (hW : IsWelfareSel (commonGame V) sel W) {O Od : Outcome A}
    (hOd : IsOpt V Od) (h : W Od ≤ W O) : IsOpt V O := by
  by_contra hO
  exact absurd h (not_le.mpr (nonopt_lt_opt_W hW hO hOd))

/-- If every player accepts an optimum, the realised deal is optimal.
Source: HA-5′
Kind: P -/
theorem isOpt_outcome_of_accept_all (hW : IsWelfareSel (commonGame V) sel W)
    {σ : ∀ i, Proposal A i} {Od : Outcome A} (hOd : IsOpt V Od) (hacc : ∀ i, Od ∈ (σ i).2) :
    IsOpt V (outcome sel σ) := by
  have hmem : Od ∈ inter σ := (mem_inter σ Od).mpr hacc
  exact isOpt_of_W_ge hW hOd (hW.outcome_max ⟨Od, hmem⟩ hmem)

/-- **Lemma A**: adding an optimum `O†` to one's acceptable set never lowers the common value
against any pure profile.
Source: HA-5′ (Lemma A)
Kind: P -/
theorem insert_opt_pointwise (hW : IsWelfareSel (commonGame V) sel W) {Od : Outcome A}
    (hOd : IsOpt V Od) (σ : ∀ i, Proposal A i) (j : N) (b : A j) (𝒜 : Finset (Outcome A)) :
    V (outcome sel (Function.update σ j (b, 𝒜))) ≤
      V (outcome sel (Function.update σ j (b, insert Od 𝒜))) := by
  by_cases hall : ∀ i, i ≠ j → Od ∈ (σ i).2
  · have hacc : ∀ i, Od ∈ (Function.update σ j (b, insert Od 𝒜) i).2 := by
      intro i
      rcases eq_or_ne i j with rfl | hi
      · simp
      · rw [Function.update_of_ne hi]; exact hall i hi
    exact isOpt_outcome_of_accept_all hW hOd hacc _
  · push_neg at hall
    obtain ⟨i₀, hi₀, hOi₀⟩ := hall
    have hinter : inter (Function.update σ j (b, insert Od 𝒜)) =
        inter (Function.update σ j (b, 𝒜)) := by
      ext O
      simp only [mem_inter]
      constructor
      · intro h i
        have hi₀' := h i₀
        rw [Function.update_of_ne hi₀] at hi₀'
        rcases eq_or_ne i j with rfl | hi
        · have hj := h i
          rw [Function.update_self] at hj ⊢
          rcases mem_insert.mp hj with rfl | hmem
          · exact absurd hi₀' hOi₀
          · exact hmem
        · rw [Function.update_of_ne hi]
          have := h i
          rwa [Function.update_of_ne hi] at this
      · intro h i
        rcases eq_or_ne i j with rfl | hi
        · have := h i
          rw [Function.update_self] at this ⊢
          exact mem_insert_of_mem this
        · rw [Function.update_of_ne hi]
          have := h i
          rwa [Function.update_of_ne hi] at this
    have hbatna : batna (Function.update σ j (b, insert Od 𝒜)) =
        batna (Function.update σ j (b, 𝒜)) := by
      funext i
      unfold batna
      rcases eq_or_ne i j with rfl | hi
      · simp
      · simp [Function.update_of_ne hi]
    unfold outcome
    rw [hinter, hbatna]

/-- **Lemma A, strict clause**: with a second player, a proposal `(b, 𝒜)` not accepting `O†`
whose batna `b` is not safe is strictly beaten by `(b, 𝒜 ∪ {O†})` against the profile where the
others accept exactly `{O†}` with batnas completing a non-optimal outcome.
Source: HA-5′ (Lemma A)
Kind: P -/
theorem exists_strict_of_unsafe (hW : IsWelfareSel (commonGame V) sel W) {Od : Outcome A}
    (hOd : IsOpt V Od) (j : N) (hex : ∃ i, i ≠ j) (b : A j) (𝒜 : Finset (Outcome A))
    (hnot : Od ∉ 𝒜) (hunsafe : ¬ Safe V j b) :
    ∃ σ : ∀ i, Proposal A i, V (outcome sel (Function.update σ j (b, 𝒜))) <
      V (outcome sel (Function.update σ j (b, insert Od 𝒜))) := by
  unfold Safe at hunsafe
  push_neg at hunsafe
  obtain ⟨O, hOj, hO⟩ := hunsafe
  obtain ⟨i₀, hi₀⟩ := hex
  refine ⟨fun i => (O i, {Od}), ?_⟩
  have h1 : inter (Function.update (fun i => (O i, {Od})) j (b, 𝒜)) = ∅ := by
    ext O'
    simp only [mem_inter, Finset.notMem_empty, iff_false]
    intro h
    have hi₀' := h i₀
    rw [Function.update_of_ne hi₀] at hi₀'
    simp only [mem_singleton] at hi₀'
    have hj := h j
    rw [Function.update_self] at hj
    subst hi₀'
    exact hnot hj
  have h1' : outcome sel (Function.update (fun i => (O i, {Od})) j (b, 𝒜)) = O := by
    rw [outcome_of_empty sel (by rw [h1]; exact Finset.not_nonempty_empty)]
    funext i
    unfold batna
    rcases eq_or_ne i j with rfl | hi
    · simp [hOj]
    · simp [Function.update_of_ne hi]
  have h2 : inter (Function.update (fun i => (O i, {Od})) j (b, insert Od 𝒜)) = {Od} := by
    ext O'
    simp only [mem_inter, mem_singleton]
    constructor
    · intro h
      have := h i₀
      rw [Function.update_of_ne hi₀] at this
      simpa using this
    · rintro rfl
      intro i
      rcases eq_or_ne i j with rfl | hi
      · simp
      · rw [Function.update_of_ne hi]; simp
  have h2' : outcome sel (Function.update (fun i => (O i, {Od})) j (b, insert Od 𝒜)) = Od := by
    rw [outcome_of_nonempty sel (by rw [h2]; exact singleton_nonempty _), h2]
    have := (hW.2 {Od} (singleton_nonempty _)).1
    simpa using this
  rw [h1', h2']
  unfold IsOpt at hO
  push_neg at hO
  obtain ⟨O', hO'⟩ := hO
  exact lt_of_lt_of_le hO' (hOd O')

/-- **Lemma B**: with a second player, in every perturbed equilibrium a proposal that does not
accept the optimum `O†` and whose batna is not safe carries only the floor weight.
Source: HA-5′ (Lemma B)
Kind: P -/
theorem IsPerturbedNash.val_le_of_not_accept (hW : IsWelfareSel (commonGame V) sel W)
    {Od : Outcome A} (hOd : IsOpt V Od) {ε : ℝ} (hε : 0 < ε) {p : MixedProfile (BG V sel)}
    (hp : IsPerturbedNash ε p) (j : N) (hex : ∃ i, i ≠ j) (s : (BG V sel).strategy j)
    (hnot : Od ∉ (s : Proposal A j).2) (hunsafe : ¬ Safe V j (s : Proposal A j).1) :
    (p j).val s ≤ ε := by
  refine hp.val_le_of_dominated hε j
    (s' := ⟨((s : Proposal A j).1, insert Od (s : Proposal A j).2), mem_univ _⟩) ?_ ?_
  · intro τ
    rw [BG_payoff, BG_payoff, ofStrategicProfile_update, ofStrategicProfile_update]
    have := insert_opt_pointwise hW hOd ((bargain (commonGame V) sel).ofStrategicProfile τ) j
      (s : Proposal A j).1 (s : Proposal A j).2
    simpa using this
  · obtain ⟨σ₀, hσ₀⟩ := exists_strict_of_unsafe hW hOd j hex (s : Proposal A j).1
      (s : Proposal A j).2 hnot hunsafe
    refine ⟨toStrat _ _ σ₀, ?_⟩
    rw [BG_payoff, BG_payoff, ofStrategicProfile_update, ofStrategicProfile_update,
      ofStrategicProfile_toStrat]
    simpa using hσ₀

/-- With a second player, every support proposal of a trembling-hand equilibrium accepts the
optimum `O†` or has a safe batna.
Source: HA-5′ (Lemma B, limit form)
Kind: C -/
theorem THPE.accept_or_safe (hW : IsWelfareSel (commonGame V) sel W) {Od : Outcome A}
    (hOd : IsOpt V Od) {p : MixedProfile (BG V sel)} (hp : THPE p) (j : N) (hex : ∃ i, i ≠ j)
    (s : (BG V sel).strategy j) (hs : 0 < (p j).val s) :
    Od ∈ (s : Proposal A j).2 ∨ Safe V j (s : Proposal A j).1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ε, pk, hpos, hε, hnash, hconv⟩ := hp
  have hle : ∀ k, (pk k j).val s ≤ ε k := fun k =>
    IsPerturbedNash.val_le_of_not_accept hW hOd (hpos k) (hnash k) j hex s hcon.1 hcon.2
  have := THPE.val_eq_zero_of_forall_le j s ε pk hε hconv hle
  rw [this] at hs
  exact lt_irrefl _ hs

/-- Some optimum exists (finitely many outcomes).
Source: none: infrastructure
Kind: L -/
theorem exists_isOpt (V : Outcome A → ℝ) : ∃ Od, IsOpt V Od := by
  obtain ⟨Od, -, h⟩ := Finset.exists_max_image (univ : Finset (Outcome A)) V univ_nonempty
  exact ⟨Od, fun O' => h O' (mem_univ _)⟩

/-- **Proposition S(a): every trembling-hand outcome of the homogeneous bargaining game is
`V`-optimal** — for every common-payoff game, every welfare selection rule, every trembling-hand
equilibrium `p*` and every pure profile in its support. Pure / shared-seed grade.
Source: HA-5′(a); [[superconditioning-mismatched-ontologies]] §13.1 Thm 13.1(2) (corrected form)
Kind: P
Fidelity: exact (support form; the pure form is `harmoniousPure_isOpt`)
Hyps: (a) all -/
theorem harmonious_subset_optimal (hW : IsWelfareSel (commonGame V) sel W)
    {p : MixedProfile (BG V sel)} (hp : THPE p) (τ : (BG V sel).Profile)
    (hτ : 0 < profWeight p τ) :
    IsOpt V (outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ)) := by
  classical
  set σ := (bargain (commonGame V) sel).ofStrategicProfile τ with hσ
  obtain ⟨Od, hOd⟩ := exists_isOpt V
  have hsupp : ∀ i, 0 < (p i).val (τ i) := (profWeight_pos_iff p τ).mp hτ
  by_contra hnot
  have hlt : V (outcome sel σ) < V Od := by
    unfold IsOpt at hnot
    push_neg at hnot
    obtain ⟨O', h⟩ := hnot
    exact lt_of_lt_of_le h (hOd O')
  rcases subsingleton_or_nontrivial N with hN | hN
  · -- one player: the support proposal is a best response, but `(b, {O†})` beats it
    let j : N := Classical.arbitrary N
    have hbr := hp.support_isBestResponse j (τ j) (hsupp j)
    have hcollapse : ∀ s'' : (BG V sel).strategy j,
        pureDev p j s'' = (BG V sel).payoff (Function.update τ j s'') j := by
      intro s''
      unfold pureDev
      have : ∀ τ' : (BG V sel).Profile, Function.update τ' j s'' = Function.update τ j s'' := by
        intro τ'
        funext i
        have hi : i = j := Subsingleton.elim i j
        subst hi
        simp
      simp_rw [this]
      rw [← sum_mul, sum_profWeight, one_mul]
    let s' : (BG V sel).strategy j := ⟨((σ j).1, {Od}), mem_univ _⟩
    have h1 := hbr s'
    rw [hcollapse, hcollapse, Function.update_eq_self, BG_payoff, BG_payoff,
      ofStrategicProfile_update, ← hσ] at h1
    have hopt : IsOpt V (outcome sel (Function.update σ j ((σ j).1, {Od}))) := by
      refine isOpt_outcome_of_accept_all hW hOd fun i => ?_
      have hi : i = j := Subsingleton.elim i j
      subst hi
      simp
    have := hopt Od
    linarith [h1, hlt, this]
  · -- at least two players: Lemma B, then the safe-batna player's veto
    have hB : ∀ j, Od ∈ (σ j).2 ∨ Safe V j (σ j).1 := fun j =>
      hp.accept_or_safe hW hOd j (exists_ne j) (τ j) (hsupp j)
    by_cases hall : ∀ j, Od ∈ (σ j).2
    · exact hnot (isOpt_outcome_of_accept_all hW hOd hall)
    · push_neg at hall
      obtain ⟨j, hj⟩ := hall
      have hsafe : Safe V j (σ j).1 := (hB j).resolve_left hj
      let s'' : (BG V sel).strategy j := ⟨((σ j).1, ∅), mem_univ _⟩
      have hdev : pureDev p j s'' = V Od := by
        unfold pureDev
        have hpt : ∀ τ' : (BG V sel).Profile,
            (BG V sel).payoff (Function.update τ' j s'') j = V Od := by
          intro τ'
          rw [BG_payoff, ofStrategicProfile_update]
          have hempty : inter (Function.update
              ((bargain (commonGame V) sel).ofStrategicProfile τ') j ((σ j).1, ∅)) = ∅ := by
            ext O
            simp only [mem_inter, Finset.notMem_empty, iff_false]
            intro h
            have := h j
            simp at this
          rw [outcome_of_empty sel (by rw [hempty]; exact Finset.not_nonempty_empty)]
          have hb : batna (Function.update
              ((bargain (commonGame V) sel).ofStrategicProfile τ') j ((σ j).1, ∅)) j = (σ j).1 := by
            show (Function.update ((bargain (commonGame V) sel).ofStrategicProfile τ') j
              ((σ j).1, ∅) j).1 = (σ j).1
            rw [Function.update_self]
          exact le_antisymm (hOd _) (hsafe _ hb Od)
        calc ∑ σ', profWeight p σ' * (BG V sel).payoff (Function.update σ' j s'') j
            = ∑ σ', profWeight p σ' * V Od := sum_congr rfl (fun τ' _ => by rw [hpt τ'])
          _ = V Od := by rw [← sum_mul, sum_profWeight, one_mul]
      have hEU : expectedPayoff (BG V sel) p j < V Od := by
        rw [expectedPayoff_eq_sum_profWeight]
        calc ∑ τ', profWeight p τ' * (BG V sel).payoff τ' j
            < ∑ τ', profWeight p τ' * V Od :=
              sum_lt_sum (fun τ' _ => mul_le_mul_of_nonneg_left (hOd _) (profWeight_nonneg _ _))
                ⟨τ, mem_univ _, mul_lt_mul_of_pos_left hlt hτ⟩
          _ = V Od := by rw [← sum_mul, sum_profWeight, one_mul]
      have := IsMixedNashEq.pureDev_le hp.isMixedNashEq j s''
      rw [hdev] at this
      exact absurd this (not_le.mpr hEU)

/-- Proposition S(a), pure form: the outcome of a pure harmonious profile is optimal.
Source: HA-5′(a)
Kind: C -/
theorem harmoniousPure_isOpt (hW : IsWelfareSel (commonGame V) sel W)
    {σ : ∀ i, Proposal A i} (h : HarmoniousPure (commonGame V) sel σ) :
    IsOpt V (outcome sel σ) := by
  have := harmonious_subset_optimal hW h (toStrat (commonGame V) sel σ) (by
    rw [profWeight_pureProfileToMixed, if_pos rfl]; exact one_pos)
  rwa [ofStrategicProfile_toStrat] at this

/-- **Proposition S(c): with no safe batna, every support proposal accepts every optimum, the
outcome is optimal, and it is `W`-maximal among the optima.** Needs a second player (with one
player "no safe batna" is contradictory: the batna profile is the only outcome with that
coordinate, so some batna is safe).
Source: HA-5′ (uniqueness and `W`-selection); [[superconditioning-mismatched-ontologies]] §13.1
Thm 13.1(2) ("the unique outcome … `argmax`")
Kind: C
Fidelity: exact (support form; uniqueness across equilibria is `outcome_eq_of_injOn`)
Hyps: (a) all -/
theorem unique_without_safe_batna [Nontrivial N] (hW : IsWelfareSel (commonGame V) sel W)
    (hns : ∀ j (b : A j), ¬ Safe V j b) {p : MixedProfile (BG V sel)} (hp : THPE p)
    (τ : (BG V sel).Profile) (hτ : 0 < profWeight p τ) :
    (∀ O, IsOpt V O → O ∈ inter ((bargain (commonGame V) sel).ofStrategicProfile τ)) ∧
      IsOpt V (outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ)) ∧
      ∀ O, IsOpt V O →
        W O ≤ W (outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ)) := by
  have hsupp : ∀ i, 0 < (p i).val (τ i) := (profWeight_pos_iff p τ).mp hτ
  have hacc : ∀ O, IsOpt V O → O ∈ inter ((bargain (commonGame V) sel).ofStrategicProfile τ) := by
    intro O hO
    rw [mem_inter]
    intro j
    exact (hp.accept_or_safe hW hO j (exists_ne j) (τ j) (hsupp j)).resolve_right (hns j _)
  refine ⟨hacc, harmonious_subset_optimal hW hp τ hτ, fun O hO => ?_⟩
  exact hW.outcome_max ⟨O, hacc O hO⟩ (hacc O hO)

/-- Uniqueness across equilibria: with no safe batna and `W` injective on the optima, any two
support profiles of any two trembling-hand equilibria realise the same outcome.
Source: HA-5′; [[superconditioning-mismatched-ontologies]] §13.1 Thm 13.1(2) ("the unique outcome")
Kind: C -/
theorem outcome_eq_of_injOn [Nontrivial N] (hW : IsWelfareSel (commonGame V) sel W)
    (hns : ∀ j (b : A j), ¬ Safe V j b)
    (hinj : ∀ O O', IsOpt V O → IsOpt V O' → W O = W O' → O = O')
    {p p' : MixedProfile (BG V sel)} (hp : THPE p) (hp' : THPE p')
    (τ τ' : (BG V sel).Profile) (hτ : 0 < profWeight p τ) (hτ' : 0 < profWeight p' τ') :
    outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ) =
      outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ') := by
  obtain ⟨-, h1, h2⟩ := unique_without_safe_batna hW hns hp τ hτ
  obtain ⟨-, h1', h2'⟩ := unique_without_safe_batna hW hns hp' τ' hτ'
  exact hinj _ _ h1 h1' (le_antisymm (h2' _ h1) (h2 _ h1'))

end Cleanroom.Udt.UdtHarmonyBargain
