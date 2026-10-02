import Cleanroom.Lit.LitShutdownPrefs.SIS
import Cleanroom.Lit.LitShutdownPrefs.Traj

/-!
# The Second and Third Theorems (Targets 5(a)(b), 6) and the price lemma

* **Second Theorem** (2023 §7, framework W): under Transitivity and Completeness a lack of
  preference between `X` and `Y` is indifference, so PI/IP-transitivity transfer every strict
  preference involving `X` to `Y` and back (`second_theorem`, kind L — the paper's proof is four
  applications of Sen's corollaries).
* **Thin classes** (`lacks_chain_card_le_one`): along a strict chain `l₀ ≺ l₁ ≺ …` a lottery
  `s` can lack a preference with at most one link. This is the content of the "at most 6 of 36
  pairs" illustration (ll. 224–234), stated as the headline instead of the 36-pair arithmetic.
* **Third Theorem** (2023 §8, over `Traj = List ℝ` as Dirac lotteries; Pareto Indifference is
  absorbed by the carrier): `Patience` at `(a, b, c, i, j, e, k, l)` plus Transitivity and
  Completeness force the agent to prefer the early-sacrifice vector to the shutdown-after-`b`
  vector, or the shutdown vector to the late-sacrifice one (`third_theorem`; trichotomy + PP/PI/IP).
  `MinimalPatience` gives the headline form. The comparative-statics remark ("the more patient,
  the larger `e`", l. 355) is *not* stated as a theorem — it is a remark (findings).
* **Price lemma** (stretch; critique/thornley.md §2.3 items 6–7): for the EU agent whose utility
  charges Prevent a cost `c ≥ 0` at timestep 1 (so IABM fails by exactly `c`), Prevent is
  preferred to Leave iff `c < (g − f) · (E_{U₀} u₀ − E_{P₀} u₀)`. (The mandate wrote the
  left-hand side as `lt (act Leave) (act Prevent)`; that is a sign slip — the condition is for
  *Prevent* to win — recorded in the findings.)
-/

namespace Cleanroom.Lit.LitShutdownPrefs

open Lottery Weak

section SecondTheorem

variable {T : Type} {le : Lottery T → Lottery T → Prop}

/-- **Second Theorem** (Thornley 2023 §7): under Transitivity and Completeness, if the agent lacks
a preference between `X` and `Y`, then (1) anything preferred to `X` is preferred to `Y`, (2)
anything dispreferred to `X` is dispreferred to `Y`, (3) anything preferred to `Y` is preferred
to `X`, (4) anything dispreferred to `Y` is dispreferred to `X`.
Source: Thornley 2023 §7 ll. 195–223; corr-refs-050
Kind: L
Fidelity: variant: OSI is definitional (menu-free relation)
Hyps: (a) all -/
theorem second_theorem (hT : Weak.Transitive le) (hC : Complete le) {X Y : Lottery T}
    (h : lacks le X Y) :
    (∀ Xp, lt le Xp X → lt le Xp Y) ∧ (∀ Xm, lt le X Xm → lt le Y Xm) ∧
      (∀ Yp, lt le Yp Y → lt le Yp X) ∧ (∀ Ym, lt le Y Ym → lt le X Ym) := by
  have hi : indiff le X Y := (lacks_iff_indiff_of_complete hC).mp h
  exact ⟨fun _ h' => pi_trans hT h' hi, fun _ h' => ip_trans hT (indiff_symm hi) h',
    fun _ h' => pi_trans hT h' (indiff_symm hi), fun _ h' => ip_trans hT hi h'⟩

open Classical in
/-- **Thin classes**: along a strictly increasing chain `l : Fin n → Lottery T`, any lottery `s`
lacks a preference with at most one link (Transitivity + Completeness). This is the content of
the "at most 6 of the 36 pairs" illustration.
Source: Thornley 2023 §7 ll. 224–234; corr-refs-050
Kind: L
Fidelity: variant: the illustration's count `6 ≤ 36` is replaced by its general cause
Hyps: (a) all -/
theorem lacks_chain_card_le_one (hT : Weak.Transitive le) (hC : Complete le) {n : ℕ}
    (l : Fin n → Lottery T) (hl : ∀ i j, i < j → lt le (l i) (l j)) (s : Lottery T) :
    (Finset.univ.filter (fun i => lacks le s (l i))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [Finset.mem_filter] at hi hj
  have hi' : indiff le s (l i) := (lacks_iff_indiff_of_complete hC).mp hi.2
  have hj' : indiff le s (l j) := (lacks_iff_indiff_of_complete hC).mp hj.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hij
  · exact (hl i j hij).2 (ii_trans hT (indiff_symm hj') hi').1
  · exact (hl j i hij).2 (ii_trans hT (indiff_symm hi') hj').1

end SecondTheorem

section ThirdTheorem

variable {le : Lottery Traj → Lottery Traj → Prop}

/-- **Patience** at the data `(a, b, c, i, j, e, k, l)`: the agent prefers `⟨a, i−e, b, j+ke, c⟩`
to `⟨a, i, b, j, c⟩` and `⟨a, i, b, j, c⟩` to `⟨a, i+e, b, j−le, c⟩` (Thornley's schematic
version with all quantifiers left open). `0 < e` is not part of this schematic condition (it
sits in `MinimalPatience`); with `e = 0` the condition is unsatisfiable for an irreflexive `lt`,
so `third_theorem` is correct without it (audit round 1, adversarial N5).
Source: Thornley 2023 §8 ll. 341–347 (Patience)
Kind: D
Fidelity: exact -/
def Patience (le : Lottery Traj → Lottery Traj → Prop) (a b c : List ℝ) (i j e k l : ℝ) : Prop :=
  lt le (dirac (a ++ [i - e] ++ b ++ [j + k * e] ++ c)) (dirac (a ++ [i] ++ b ++ [j] ++ c)) ∧
    lt le (dirac (a ++ [i] ++ b ++ [j] ++ c)) (dirac (a ++ [i + e] ++ b ++ [j - l * e] ++ c))

/-- **Minimal Patience**: Patience holds for some data with `e > 0`.
Source: Thornley 2023 §8 ll. 306–312 (Minimal Patience)
Kind: D
Fidelity: exact -/
def MinimalPatience (le : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∃ (a b c : List ℝ) (i j e k l : ℝ), 0 < e ∧ Patience le a b c i j e k l

/-- **Third Theorem** (Thornley 2023 §8): for any data of which Patience is true, under
Transitivity and Completeness, either the agent prefers `⟨a, i−e, b, j+ke, c⟩` to the
shutdown-after-`b` trajectory `⟨a, i, b⟩` (it will pay `e` earlier to prevent a later press), or it
prefers `⟨a, i, b⟩` to `⟨a, i+e, b, j−le, c⟩` (it will pay `e` earlier to cause a later press).
Proof: trichotomy on `⟨a, i, b, j, c⟩` versus `⟨a, i, b⟩`, then PP-, PP-, PI-transitivity.
Source: Thornley 2023 §8 ll. 313–352 (Third Theorem); corr-refs-051
Kind: L
Fidelity: variant: OSI definitional; Pareto Indifference absorbed (trajectories are utility
vectors); `e > 0` not needed for this step
Hyps: (a) all -/
theorem third_theorem (hT : Weak.Transitive le) (hC : Complete le) (a b c : List ℝ) (i j e k l : ℝ)
    (hP : Patience le a b c i j e k l) :
    lt le (dirac (a ++ [i - e] ++ b ++ [j + k * e] ++ c)) (dirac (a ++ [i] ++ b)) ∨
      lt le (dirac (a ++ [i] ++ b)) (dirac (a ++ [i + e] ++ b ++ [j - l * e] ++ c)) := by
  obtain ⟨h1, h2⟩ := hP
  rcases trichotomy_of_complete hC (dirac (a ++ [i] ++ b ++ [j] ++ c)) (dirac (a ++ [i] ++ b))
    with h | h | h
  · exact Or.inl (pp_trans hT h1 h)
  · exact Or.inr (pp_trans hT h h2)
  · exact Or.inl (pi_trans hT h1 h)

/-- **Third Theorem, headline form**: a minimally patient agent (Weak.Transitive, Complete) is in some
case willing to sacrifice `e > 0` at an earlier timestep to prevent, or to cause, a later press.
Source: Thornley 2023 §8 ll. 282–286 (rough statement), 349–352
Kind: L
Fidelity: variant: as `third_theorem`
Hyps: (a) all -/
theorem third_theorem_minimal (hT : Weak.Transitive le) (hC : Complete le) (hM : MinimalPatience le) :
    ∃ (a b c : List ℝ) (i j e k l : ℝ), 0 < e ∧
      (lt le (dirac (a ++ [i - e] ++ b ++ [j + k * e] ++ c)) (dirac (a ++ [i] ++ b)) ∨
        lt le (dirac (a ++ [i] ++ b)) (dirac (a ++ [i + e] ++ b ++ [j - l * e] ++ c))) := by
  obtain ⟨a, b, c, i, j, e, k, l, he, hP⟩ := hM
  exact ⟨a, b, c, i, j, e, k, l, he, third_theorem hT hC a b c i j e k l hP⟩

/-- **N+ witness for the Third Theorem**: the `δ = 1/2` discounted-sum EU agent with
`a = b = c = []`, `i = j = 0`, `e = 1`, `k = l = 3`. Patience holds (`−1 + 3/2 > 0 > 1 − 3/2`), the
relation is transitive and complete, and the realised disjunct is the first
(`−1 + 3/2 > 0 = u [0]`), checked directly.
Source: [[lit-shutdown-prefs-mandate]] Target 6 (Witness N+)
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem third_theorem_witness :
    Weak.Transitive (euLe (discSum (1/2))) ∧ Complete (euLe (discSum (1/2))) ∧
      Patience (euLe (discSum (1/2))) [] [] [] 0 0 1 3 3 ∧
      lt (euLe (discSum (1/2))) (dirac ([] ++ [0 - 1] ++ [] ++ [0 + 3 * 1] ++ []))
        (dirac ([] ++ [(0 : ℝ)] ++ [])) := by
  refine ⟨euLe_transitive _, euLe_complete _, ⟨?_, ?_⟩, ?_⟩ <;>
    (rw [euLe_lt_iff]; simp [discSum]; norm_num)

end ThirdTheorem

/-! ## The price lemma (stretch) -/

namespace SIS

variable {R : Type} (S : SIS R)

/-- Expectation of `P a` in terms of the base lottery.
Source: none: infrastructure
Kind: L -/
theorem expect_P (u : Act × R → ℝ) (a : Act) : (S.P a).expect u = S.P₀.expect (fun r => u (a, r)) :=
  expect_map _ _ _

/-- Expectation of `U a` in terms of the base lottery.
Source: none: infrastructure
Kind: L -/
theorem expect_U (u : Act × R → ℝ) (a : Act) : (S.U a).expect u = S.U₀.expect (fun r => u (a, r)) :=
  expect_map _ _ _

/-- The utility that charges the action Prevent a cost `c` at timestep 1 and is otherwise the
label-blind `u₀`: `u (Prevent, r) = u₀ r − c`, `u (a, r) = u₀ r` for `a ≠ Prevent`.
Source: critique/thornley.md §2.3 items 6–7; corr-wf13-2-070
Kind: D
Fidelity: exact -/
def chargePrevent (u₀ : R → ℝ) (c : ℝ) : Act × R → ℝ :=
  fun x => if x.1 = Act.Prevent then u₀ x.2 - c else u₀ x.2

/-- `E_X[g − c] = E_X[g] − c`.
Source: none: infrastructure
Kind: L -/
theorem expect_sub_const {T : Type} (X : Lottery T) (g : T → ℝ) (c : ℝ) :
    X.expect (fun t => g t - c) = X.expect g - c := by
  have := X.expect_add g (fun _ => -c)
  rw [X.expect_const (-c)] at this
  simp only [sub_eq_add_neg]
  exact this

/-- **Price lemma**: for the EU agent with utility `chargePrevent u₀ c`, Prevent is strictly
preferred to Leave iff the cost is below the price `(g − f) · (E_{U₀} u₀ − E_{P₀} u₀)`. IABM
fails for this utility by exactly `c` (`chargePrevent_iabm_iff`).
Source: critique/thornley.md §2.3 items 6–7 (`[derived]`); corr-wf13-2-070; [[lit-shutdown-prefs-mandate]] Target 6 (price lemma; the mandate's `lt (act Leave) (act Prevent)` is a sign slip)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem price_lemma (u₀ : R → ℝ) (c : ℝ) :
    lt (euLe (chargePrevent u₀ c)) (S.act .Prevent) (S.act .Leave) ↔
      c < (S.g - S.f) * (S.U₀.expect u₀ - S.P₀.expect u₀) := by
  rw [euLe_lt_iff]
  simp only [act, expect_mix, expect_P, expect_U, prob]
  have hP : S.P₀.expect (fun r => chargePrevent u₀ c (Act.Prevent, r)) = S.P₀.expect u₀ - c := by
    rw [← expect_sub_const]; rfl
  have hU : S.U₀.expect (fun r => chargePrevent u₀ c (Act.Prevent, r)) = S.U₀.expect u₀ - c := by
    rw [← expect_sub_const]; rfl
  have hP' : S.P₀.expect (fun r => chargePrevent u₀ c (Act.Leave, r)) = S.P₀.expect u₀ := rfl
  have hU' : S.U₀.expect (fun r => chargePrevent u₀ c (Act.Leave, r)) = S.U₀.expect u₀ := rfl
  rw [hP, hU, hP', hU']
  constructor <;> intro h <;> nlinarith

/-- `chargePrevent u₀ c` satisfies IABM iff `c = 0` (given some `r : R`): IABM fails by exactly `c`.
Source: critique/thornley.md §2.3 item 6
Kind: L -/
theorem chargePrevent_iabm_iff (u₀ : R → ℝ) (c : ℝ) (r₀ : R) :
    IABM (euLe (chargePrevent u₀ c)) ↔ c = 0 := by
  rw [euLe_iabm_iff]
  constructor
  · intro h
    have := h Act.Prevent Act.Leave r₀
    simp [chargePrevent] at this
    linarith
  · rintro rfl a a' r
    simp [chargePrevent]

end SIS

end Cleanroom.Lit.LitShutdownPrefs
