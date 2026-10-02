import Cleanroom.Udt.UdtInfluence101.Omega

/-!
# Assumption 5 holds in the Omega instance (`Omega.A5_asp`, formerly OPEN)

Repair round 2 (2026-10-02). Closes the open statement `Omega.A5_asp` of repair round 1: Post 8's
Assumption 5 in the time-`n`-precommitment form (`PlaySpace.A5 hT`) holds in `Omega.aspModel`, so
`Omega.not_CEI` (the failure of Conservation of Expected Influence) sits inside the full hypothesis
package of `theorem1` — the mandate's T6(b) trap is honoured completely.

**Time `1`** (`IP_one_eq_zero`, `IEo_one_eq_zero`): both influences of *every* algorithm vanish at
every positive world. The step-`1` ε-factor is the ε-mixed action weight times `1/2` times the type
report's row (`F_node1_eq`), so its marginal against "the second observation is `o`" is `1/2`
independently of Omega's type, of `ε` and of the algorithm (`F_node1_sum_obs`); hence
`ℙ^ε_{h₁}(o₁ = o) = 1/2` wherever the atom has mass (`pr_one_eq`), and `U = [ξ₁]` is constant on the
atom. (The root factor is *not* constant on the time-`1` atom — it depends on the type `w`, audit r2
probe `OmegaRootFactor.lean` — which is why the repair-round-1 docstring's "atom cancellation" was
the wrong reason; this is the right one.)

**Time `0`** (`IP_zero_eq`, `IEo_zero_eq`): every positive world has `ξ₀ = false`, so the time-`0`
atom of a positive world is the whole support and a time-`0` precommitment `A` has `prof A hT =
A(hT, S̄)` (`prof_eq_play`). The root step factor is affine in `ε` with slope linear in
`p := prof(A)(o)` (`F_node0_eq'`); summing the second letter out, `ℙ^ε_∅(o₀ = o) = 1/2 + ε(p/2 −
1/4)` (`den_eq'`, with the atom of mass one, `mass_atom0`) and `Σ law·U = 1/4 + ε(3p/8 − 3/16)`
(`num_eq'`), so `𝕀^ℙ_∅(A, hT, o) = p/2 − 1/4` and `𝕀^𝔼_∅(A, hT, o) = p/4 − 1/8` — both affine in
`p`, hence the `A(hT, S̄)`-average of the pure-action values (`prof (ofAct a) hT = δ a`).

`A5_asp` assembles the two times. Namespace `Omega` (continued).
-/

namespace Cleanroom.Udt.UdtInfluence101

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Home (fair fair_w coin coin_w hT hH root root_ne_hT root_ne_hH hT_ne_hH leafExt_hT_iff)
open ProfileModel

namespace Omega

noncomputable section

/-! ### Time `1`: the time-`1` atom and the step-`1` factor -/

/-- Supporting lemma `mem_atom1_iff` (the time-`1` atom fixes the root state, the box and the report,
not Omega's type).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_atom1_iff (ω' ω : PWorld Bool Bool Bool Bool 2) :
    ω ∈ S.atom 1 ω' ↔
      ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2 := by
  rw [S.mem_atom]
  constructor
  · intro hat
    exact ⟨(hat.2 0 (Nat.zero_le _)).symm, (hat.1 0 (by decide)).symm, (hat.2 1 le_rfl).symm⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi0 : i = 0 := Fin.ext (Nat.lt_one_iff.1 hi)
      subst hi0
      exact h1.symm
    · fin_cases i
      · exact h0.symm
      · exact h2.symm
      · simp at hi

/-- Supporting lemma `mem_nextObs1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_nextObs1 (ω : PWorld Bool Bool Bool Bool 2) (o : Bool) :
    ω ∈ S.nextObs 1 o ↔ (ω.2 1).2.1 = o := by
  rw [S.mem_nextObs (show (1 : ℕ) < 2 by norm_num)]
  rfl

/-- Supporting lemma `atom1_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom1_eq (ω' : PWorld Bool Bool Bool Bool 2) : S.atom 1 ω' =
    univ.filter (fun ω : PWorld Bool Bool Bool Bool 2 =>
      ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2) := by
  ext ω
  rw [Finset.mem_filter, mem_atom1_iff]
  simp only [Finset.mem_univ, true_and]

/-- Supporting lemma `atom1_obs_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom1_obs_eq (ω' : PWorld Bool Bool Bool Bool 2) (o : Bool) :
    S.nextObs 1 o ∩ S.atom 1 ω' =
    univ.filter (fun ω : PWorld Bool Bool Bool Bool 2 => (ω.2 1).2.1 = o ∧
      (ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2)) := by
  ext ω
  rw [Finset.mem_inter, Finset.mem_filter, mem_atom1_iff, mem_nextObs1]
  simp only [Finset.mem_univ, true_and]

/-- Indicator summand of the time-`1` atom of `ω'`, as a function of the root draw and the first letter.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Gq (ω' : PWorld Bool Bool Bool Bool 2) (r : Bool × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if r.2 = ω'.1.2 ∧ x.2.1 = (ω'.2 0).2.1 ∧ x.2.2 = (ω'.2 0).2.2 then 1 else 0

/-- Indicator of "the second observation is `o`", as a function of the second letter.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def obsInd (o : Bool) (y : Letter Bool Bool Bool) : ℝ := if y.2.1 = o then 1 else 0

/-- **The step-`1` ε-factor** at a depth-one node: the ε-mixed action weight, times `1/2` (the second
observation is a fair coin: `eA` at step `1` is fair), times the type report's row.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node1_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (w ξ₀ : Bool) (x : Letter Bool Bool Bool)
    (a o' ξ : Bool) :
    aspModel.F A hT ε (w, ξ₀) (node1 x) (a, o', ξ) =
      aspModel.algW A hT ε (oNode (node1 x)) (statePre ξ₀ (node1 x)) a * (1 / 2) *
        (aspModel.κ w (node1 x).1 (obsPre (node1 x)) (statePre ξ₀ (node1 x)) a o').w ξ := by
  have heA : ∀ (a a' : Bool),
      aspModel.eA w (node1 x).1 (obsPre (node1 x)) (actPre (node1 x)) a a' = fair := by
    intro a a'
    show (if ((node1 x).1).val = 0 then (if w then FinDist.delta a' else fair) else fair) = fair
    exact if_neg (by simp [node1])
  simp only [ProfileModel.F, heA, fair_w, ← Finset.sum_mul, aspModel.profW_sum]
  ring

/-- **The step-`1` factor summed against "the second observation is `o`" is `1/2`**, for every
algorithm, `ε`, type and first letter (the type report's row sums to one).
Source: none: infrastructure (audit r2 N2/N3: the right reason for the `n = 1` clause)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node1_sum_obs (A : Alg Bool Bool Bool 2) (ε : ℝ) (w ξ₀ : Bool) (x : Letter Bool Bool Bool)
    (o : Bool) :
    ∑ y, aspModel.F A hT ε (w, ξ₀) (node1 x) y * obsInd o y = 1 / 2 := by
  rw [sum_letter]
  have h : ∀ a o' ξ : Bool, aspModel.F A hT ε (w, ξ₀) (node1 x) (a, o', ξ) * obsInd o (a, o', ξ) =
      aspModel.algW A hT ε (oNode (node1 x)) (statePre ξ₀ (node1 x)) a *
        ((1 / 2) * if o' = o then 1 else 0) *
        (aspModel.κ w (node1 x).1 (obsPre (node1 x)) (statePre ξ₀ (node1 x)) a o').w ξ := by
    intro a o' ξ
    rw [F_node1_eq, obsInd]
    ring
  simp only [h, ← Finset.mul_sum, FinDist.sum_one, mul_one]
  rw [← Finset.sum_mul, aspModel.algW_sum, one_mul]
  simp only [Fintype.sum_bool]
  cases o <;> norm_num

/-- **Both letters marginalized**: the ε-mass of a product of a function of the root draw and the
first letter with a function of the second letter.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_lawW_mul_both (A : Alg Bool Bool Bool 2) (ε : ℝ)
    (G : Bool × Bool → Letter Bool Bool Bool → ℝ) (H : Letter Bool Bool Bool → ℝ) :
    ∑ ω, aspModel.lawW A hT ε ω * (G ω.1 (ω.2 0) * H (ω.2 1)) =
      ∑ r, ∑ x, aspModel.root.w r * aspModel.F A hT ε r (node0 _) x * G r x *
        ∑ y, aspModel.F A hT ε r (node1 x) y * H y := by
  rw [sum_pworld_two]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [lawW_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **The ε-mass of the time-`1` atom** as a sum over the root draw and the first letter.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom1 (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω' : PWorld Bool Bool Bool Bool 2) :
    mass (aspModel.lawW A hT ε) (S.atom 1 ω') =
      ∑ r, ∑ x, aspModel.root.w r * aspModel.F A hT ε r (node0 _) x * Gq ω' r x := by
  unfold mass
  rw [atom1_eq, Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Bool 2,
      (if ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2 then
        aspModel.lawW A hT ε ω else 0) = aspModel.lawW A hT ε ω * Gq ω' ω.1 (ω.2 0) := by
    intro ω
    by_cases hB : ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2
    · rw [if_pos hB, Gq, if_pos hB]; ring
    · rw [if_neg hB, Gq, if_neg hB]; ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, aspModel.sum_lawW_mul_fst A hT ε (Gq ω')]

/-- **The ε-mass of "second observation `o` on the time-`1` atom" is half the atom's mass**, for
every algorithm and `ε`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom1_obs (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω' : PWorld Bool Bool Bool Bool 2)
    (o : Bool) :
    mass (aspModel.lawW A hT ε) (S.nextObs 1 o ∩ S.atom 1 ω') =
      (1 / 2) * ∑ r, ∑ x, aspModel.root.w r * aspModel.F A hT ε r (node0 _) x * Gq ω' r x := by
  unfold mass
  rw [atom1_obs_eq, Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Bool 2,
      (if (ω.2 1).2.1 = o ∧
          (ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2) then
        aspModel.lawW A hT ε ω else 0) =
      aspModel.lawW A hT ε ω * (Gq ω' ω.1 (ω.2 0) * obsInd o (ω.2 1)) := by
    intro ω
    by_cases hA : (ω.2 1).2.1 = o
    · by_cases hB : ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2
      · rw [if_pos ⟨hA, hB⟩, Gq, obsInd, if_pos hB, if_pos hA]; ring
      · rw [if_neg (fun h => hB h.2), Gq, if_neg hB]; ring
    · rw [if_neg (fun h => hA h.1), obsInd, if_neg hA]; ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, sum_lawW_mul_both]
  have hin : ∀ (r : Bool × Bool) (x : Letter Bool Bool Bool),
      ∑ y, aspModel.F A hT ε r (node1 x) y * obsInd o y = 1 / 2 := fun r x => by
    obtain ⟨w, ξ₀⟩ := r
    exact F_node1_sum_obs A ε w ξ₀ x o
  simp only [hin]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **`ℙ^ε_{h₁}(o₁ = o) = 1/2`** along the ε-family of every algorithm, wherever the time-`1` atom
has non-zero ε-mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pr_one_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω' : PWorld Bool Bool Bool Bool 2) (o : Bool)
    (hne : mass (aspModel.lawW A hT ε) (S.atom 1 ω') ≠ 0) :
    S.pr (aspModel.lawW A hT ε) 1 (S.nextObs 1 o) ω' = 1 / 2 := by
  unfold PlaySpace.pr condProbJunk
  rw [if_neg hne, mass_atom1_obs]
  rw [mass_atom1] at hne ⊢
  rw [mul_div_assoc, div_self hne, mul_one]

/-- **The time-`1` influence of every algorithm on the probability of the second observation is `0`**
at every positive world.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (the `n = 1` `IP` clause in the Omega instance)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IP_one_eq_zero (A : Alg Bool Bool Bool 2) {ω' : PWorld Bool Bool Bool Bool 2}
    (hω' : 0 < aspModel.baseW ω') (o : Bool) : S.IP 1 A hT o ω' = 0 := by
  unfold PlaySpace.IP
  have hpos : 0 < mass S.ℙ.w (S.atom 1 ω') :=
    mass_pos_of_mem aspModel.baseW_nonneg (S.self_mem_atom 1 ω') hω'
  have hev := S.eventually_mass_pos aspModel.smoothLaw A hT hpos
  have heq : (fun ε => S.pr (S.law A hT ε) 1 (S.nextObs 1 o) ω') =ᶠ[nhds 0] fun _ => (1 / 2 : ℝ) := by
    filter_upwards [hev] with ε hε
    exact pr_one_eq A ε ω' o hε.ne'
  rw [heq.deriv_eq, deriv_const]

/-- **The time-`1` influence of every algorithm on conditional expected utility is `0`** at every
positive world and observation: the payoff `[ξ₁ = true]` is fixed by the time-`1` state.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (the `n = 1` `IEo` clause in the Omega instance)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IEo_one_eq_zero (A : Alg Bool Bool Bool 2) {ω' : PWorld Bool Bool Bool Bool 2}
    (hω' : 0 < aspModel.baseW ω') (o : Bool) : S.IEo 1 A hT o ω' = 0 := by
  unfold PlaySpace.IEo
  have hpos : 0 < mass S.ℙ.w (S.atom 1 ω' ∩ S.nextObs 1 o) := hall 1 (by norm_num) ω' hω' o
  have hconst : ∀ ω'' ∈ S.atom 1 ω' ∩ S.nextObs 1 o, S.U ω'' = S.U ω' := by
    intro ω'' h
    have hat := S.mem_atom.1 (Finset.mem_inter.1 h).1
    have hs : (ω''.2 0).2.2 = (ω'.2 0).2.2 := (hat.2 1 le_rfl).symm
    show (if (ω''.2 0).2.2 then (1 : ℝ) else 0) = if (ω'.2 0).2.2 then 1 else 0
    rw [hs]
  have hev := S.eventually_mass_pos aspModel.smoothLaw A hT hpos
  have heq : (fun ε => S.cexp (S.law A hT ε) 1 (S.nextObs 1 o) S.U ω') =ᶠ[nhds 0]
      fun _ => S.U ω' := by
    filter_upwards [hev] with ε hε
    exact condExpJunk_const_on hconst hε
  rw [heq.deriv_eq, deriv_const]

/-! ### Time `0`: the time-`0` atom of a positive world is the whole support -/

/-- Supporting lemma `mem_atom0_iff` (the time-`0` atom of `ω₀` is "root state `false`").
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_atom0_iff (ω : PWorld Bool Bool Bool Bool 2) : ω ∈ S.atom 0 ω₀ ↔ ω.1.2 = false := by
  rw [S.mem_atom]
  constructor
  · intro hat
    exact (hat.2 0 le_rfl).symm
  · intro h1
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_⟩
    have hi0 : i = 0 := Fin.ext (Nat.le_zero.1 hi)
    subst hi0
    exact h1.symm

/-- Supporting lemma `atomEq_zero_of_pos` (every positive world shares `ω₀`'s time-`0` state).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_zero_of_pos {ω : PWorld Bool Bool Bool Bool 2} (hω : 0 < aspModel.baseW ω) :
    S.AtomEq 0 ω ω₀ :=
  S.atomEq_symm (S.mem_atom.1 ((mem_atom0_iff ω).2 ((baseW_pos_iff ω).1 hω)))

/-- Supporting lemma `E_eq'` (the time-`0` atom of `ω₀` and the next observation `o`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem E_eq' (o : Bool) : S.atom 0 ω₀ ∩ S.nextObs 0 o =
    univ.filter (fun ω : PWorld Bool Bool Bool Bool 2 => ω.1.2 = false ∧ (ω.2 0).2.1 = o) := by
  ext ω
  rw [Finset.mem_inter, Finset.mem_filter, mem_atom0_iff, mem_nextObs0]
  simp only [Finset.mem_univ, true_and]

/-- Supporting lemma `lawW_eq_zero_of_root_true` (worlds with root state `true` have no mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem lawW_eq_zero_of_root_true (A : Alg Bool Bool Bool 2) (ε : ℝ)
    {ω : PWorld Bool Bool Bool Bool 2} (h : ω.1.2 = true) : aspModel.lawW A hT ε ω = 0 := by
  unfold ProfileModel.lawW
  rw [root_w, if_pos h, zero_mul]

/-- **The time-`0` atom of `ω₀` carries all the ε-mass**: `ℙ^ε(atom_0(ω₀)) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom0 (A : Alg Bool Bool Bool 2) (ε : ℝ) : mass (aspModel.lawW A hT ε) (S.atom 0 ω₀) = 1 := by
  unfold mass
  rw [Finset.sum_subset (Finset.subset_univ _) (fun ω _ hω => ?_)]
  · exact S.law_sum A hT ε
  · rw [mem_atom0_iff] at hω
    exact lawW_eq_zero_of_root_true A ε (by simpa using hω)

/-- **The root observation factor for an arbitrary algorithm**: a smart Omega fills the box with the
ε-mixed global profile's one-boxing rate, a dumb one with `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem obsFactor0_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (w : Bool)
    (obs : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool)
    (acts : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool) (a o : Bool) :
    ∑ a', aspModel.profW A hT ε (aspModel.pn root) a' *
        (aspModel.eA w (node0 (Letter Bool Bool Bool)).1 obs acts a a').w o =
      if w then (1 - ε) / 2 + ε * (aspModel.prof A hT).w o else 1 / 2 := by
  have hpn : aspModel.pn root = hT := by
    show (if root = root then hT else root) = hT
    rw [if_pos rfl]
  have heA : ∀ (a a' : Bool), aspModel.eA w (node0 (Letter Bool Bool Bool)).1 obs acts a a' =
      if w then FinDist.delta a' else fair := fun a a' => by
    show (if ((node0 (Letter Bool Bool Bool)).1).val = 0 then (if w then FinDist.delta a' else fair)
      else fair) = _
    exact if_pos rfl
  have hπ : ∀ (a : Bool), (aspModel.π₀ hT).w a = 1 / 2 := fun a => fair_w a
  rw [hpn]
  cases w
  · simp only [heA, Bool.false_eq_true, if_false, fair_w, ← Finset.sum_mul, aspModel.profW_sum]
    norm_num
  · simp only [heA, if_true, FinDist.delta_w, Fintype.sum_bool, ProfileModel.profW, hπ]
    cases o <;> simp <;> ring

/-- **The root step factor under ε-play of any `A` at `hT`**: `(1/2)·obs·κ`, with the observation
factor of `obsFactor0_eq` and the type report's row.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node0_eq' (A : Alg Bool Bool Bool 2) (ε : ℝ) (w ξ₀ a₀ o₀ ξ₁ : Bool) :
    aspModel.F A hT ε (w, ξ₀) (node0 _) (a₀, o₀, ξ₁) =
      (1 / 2) * (if w then ((1 - ε) / 2 + ε * (aspModel.prof A hT).w o₀) else 1 / 2) *
        (if ξ₁ then (if w then 3 / 4 else 1 / 4) else (1 - (if w then 3 / 4 else 1 / 4))) := by
  have h0 : oNode (node0 (Letter Bool Bool Bool)) = root := oNode_node0
  have hB : ∀ (m : Node Bool 2) (s : Fin (m.1.val + 1) → Bool) (a : Bool),
      (aspModel.B m s).w a = 1 / 2 := fun _ _ a => fair_w a
  have hκ : ∀ (k : Fin 2) (obs : Fin k.val → Bool) (s : Fin (k.val + 1) → Bool) (a o ξ : Bool),
      (aspModel.κ w k obs s a o).w ξ =
        if ξ then (if w then 3 / 4 else 1 / 4) else (1 - (if w then 3 / 4 else 1 / 4)) :=
    fun _ _ _ _ _ ξ => by simp only [aspModel, coin_w]
  simp only [ProfileModel.F, ProfileModel.algW, h0, if_neg root_ne_hT, hB, obsFactor0_eq, hκ]

/-- Summand of the ε-mass of "root state `false`, box `o`", as a function of the root draw and the
first letter.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def G₂' (o : Bool) (r : Bool × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if r.2 = false ∧ x.2.1 = o then 1 else 0

/-- Summand of the ε-weighted utility on "root state `false`, box `o`".
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def G₁' (o : Bool) (r : Bool × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if r.2 = false ∧ x.2.1 = o then (if x.2.2 then 1 else 0) else 0

/-- **`ℙ^ε_∅(o₀ = o)` for an arbitrary algorithm**: `1/2 + ε·(prof(A)(o)/2 − 1/4)`.
Source: none: infrastructure (generalizes `den_eq`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem den_eq' (A : Alg Bool Bool Bool 2) (ε : ℝ) (o : Bool) :
    mass (aspModel.lawW A hT ε) (S.atom 0 ω₀ ∩ S.nextObs 0 o) =
      1 / 2 + ε * ((aspModel.prof A hT).w o / 2 - 1 / 4) := by
  unfold mass
  rw [E_eq', Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Bool 2,
      (if ω.1.2 = false ∧ (ω.2 0).2.1 = o then aspModel.lawW A hT ε ω else 0) =
      aspModel.lawW A hT ε ω * G₂' o ω.1 (ω.2 0) := by
    intro ω
    simp only [G₂']
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, aspModel.sum_lawW_mul_fst A hT ε (G₂' o)]
  simp only [G₂', Fintype.sum_prod_type, Fintype.sum_bool, F_node0_eq', root_w]
  cases o <;> norm_num <;> ring

/-- **The ε-weighted utility on "box `o`" for an arbitrary algorithm**: `1/4 + ε·(3·prof(A)(o)/8 − 3/16)`.
Source: none: infrastructure (generalizes `num_eq`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem num_eq' (A : Alg Bool Bool Bool 2) (ε : ℝ) (o : Bool) :
    ∑ ω ∈ S.atom 0 ω₀ ∩ S.nextObs 0 o, aspModel.lawW A hT ε ω * aspModel.U ω =
      1 / 4 + ε * (3 * (aspModel.prof A hT).w o / 8 - 3 / 16) := by
  rw [E_eq', Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Bool 2,
      (if ω.1.2 = false ∧ (ω.2 0).2.1 = o then aspModel.lawW A hT ε ω * aspModel.U ω else 0) =
      aspModel.lawW A hT ε ω * G₁' o ω.1 (ω.2 0) := by
    intro ω
    simp only [G₁', aspModel]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, aspModel.sum_lawW_mul_fst A hT ε (G₁' o)]
  simp only [G₁', Fintype.sum_prod_type, Fintype.sum_bool, F_node0_eq', root_w]
  cases o <;> norm_num <;> ring

/-- Supporting lemma `pr_eq'` (`ℙ^ε_∅(o₀ = o)` along the ε-family of any `A` at `ω₀`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pr_eq' (A : Alg Bool Bool Bool 2) (ε : ℝ) (o : Bool) :
    S.pr (aspModel.lawW A hT ε) 0 (S.nextObs 0 o) ω₀ =
      1 / 2 + ε * ((aspModel.prof A hT).w o / 2 - 1 / 4) := by
  unfold PlaySpace.pr condProbJunk
  rw [mass_atom0, Finset.inter_comm, den_eq', if_neg one_ne_zero, div_one]

/-- Supporting lemma `hasDerivAt_lin` (the derivative at `0` of `c₀ + ε·c`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hasDerivAt_lin (c₀ c : ℝ) : HasDerivAt (fun ε : ℝ => c₀ + ε * c) (1 * c) 0 :=
  ((hasDerivAt_id' (x := (0 : ℝ))).mul_const c).const_add c₀

/-- **The time-`0` influence of any `A` on the probability of `o₀ = o` is `prof(A)(o)/2 − 1/4`** at
`ω₀`: affine in the global profile.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (the `n = 0` `IP` clause in the Omega instance)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IP_zero_eq (A : Alg Bool Bool Bool 2) (o : Bool) :
    S.IP 0 A hT o ω₀ = (aspModel.prof A hT).w o / 2 - 1 / 4 := by
  unfold PlaySpace.IP
  have hf : (fun ε => S.pr (S.law A hT ε) 0 (S.nextObs 0 o) ω₀) =
      fun ε => 1 / 2 + ε * ((aspModel.prof A hT).w o / 2 - 1 / 4) := funext fun ε => pr_eq' A ε o
  rw [hf, (hasDerivAt_lin _ _).deriv, one_mul]

/-- Supporting lemma `cexp_eq'` (the conditional expected utility given `o₀ = o` along the ε-family,
where the denominator does not vanish).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_eq' (A : Alg Bool Bool Bool 2) (ε : ℝ) (o : Bool)
    (hne : (1 / 2 + ε * ((aspModel.prof A hT).w o / 2 - 1 / 4) : ℝ) ≠ 0) :
    S.cexp (aspModel.lawW A hT ε) 0 (S.nextObs 0 o) aspModel.U ω₀ =
      (1 / 4 + ε * (3 * (aspModel.prof A hT).w o / 8 - 3 / 16)) /
        (1 / 2 + ε * ((aspModel.prof A hT).w o / 2 - 1 / 4)) := by
  unfold PlaySpace.cexp condExpJunk
  rw [den_eq', num_eq', if_neg hne]

/-- **The time-`0` influence of any `A` on the conditional expected utility given `o₀ = o` is
`prof(A)(o)/4 − 1/8`** at `ω₀`: affine in the global profile (for `A = δ one-box`, `o = full` this
is `IEo_eq`'s `1/8`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (the `n = 0` `IEo` clause in the Omega instance)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IEo_zero_eq (A : Alg Bool Bool Bool 2) (o : Bool) :
    S.IEo 0 A hT o ω₀ = (aspModel.prof A hT).w o / 4 - 1 / 8 := by
  unfold PlaySpace.IEo
  set p := (aspModel.prof A hT).w o with hp
  have hev : ∀ᶠ ε in nhds (0 : ℝ), (1 / 2 + ε * (p / 2 - 1 / 4) : ℝ) ≠ 0 :=
    ContinuousAt.eventually_ne (by fun_prop) (by norm_num)
  have heq : (fun ε => S.cexp (S.law A hT ε) 0 (S.nextObs 0 o) S.U ω₀) =ᶠ[nhds 0]
      fun ε => (1 / 4 + ε * (3 * p / 8 - 3 / 16)) / (1 / 2 + ε * (p / 2 - 1 / 4)) := by
    filter_upwards [hev] with ε hε
    show S.cexp (aspModel.lawW A hT ε) 0 (S.nextObs 0 o) aspModel.U ω₀ = _
    rw [cexp_eq' A ε o hε]
  rw [heq.deriv_eq]
  have hN := hasDerivAt_lin (1 / 4) (3 * p / 8 - 3 / 16)
  have hD := hasDerivAt_lin (1 / 2) (p / 2 - 1 / 4)
  have hq : HasDerivAt (fun ε : ℝ => (1 / 4 + ε * (3 * p / 8 - 3 / 16)) / (1 / 2 + ε * (p / 2 - 1 / 4)))
      ((1 * (3 * p / 8 - 3 / 16) * (1 / 2 + (0 : ℝ) * (p / 2 - 1 / 4)) -
        (1 / 4 + (0 : ℝ) * (3 * p / 8 - 3 / 16)) * (1 * (p / 2 - 1 / 4))) /
        (1 / 2 + (0 : ℝ) * (p / 2 - 1 / 4)) ^ 2) 0 :=
    hN.div hD (by norm_num)
  rw [hq.deriv]
  ring

/-! ### A time-`0` precommitment has the profile of its action -/

/-- **A time-`0` precommitment reads as its action**: if `A`'s action at `hT` is constant on the
time-`0` atom of a positive world `ω` (the whole support), its global profile is `A(hT, S̄)(ω)`.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (why the precommitment form holds here); F4
Kind: L
Fidelity: exact
Hyps: none -/
theorem prof_eq_play {A : Alg Bool Bool Bool 2} {ω : PWorld Bool Bool Bool Bool 2}
    (hω : 0 < aspModel.baseW ω) (hconst : S.ConstOnAtom 0 A hT ω) :
    aspModel.prof A hT = S.play A hT ω := by
  apply FinDist.ext
  intro b
  rw [aspModel.prof_w_of_pos _ hreach]
  refine condExpJunk_const_on_pos aspModel.baseW_nonneg hreach (fun ω' _ hpos => ?_)
  have hmem : ω' ∈ S.atom 0 ω :=
    S.mem_atom.2 (S.atomEq_trans (atomEq_zero_of_pos hω) (S.atomEq_symm (atomEq_zero_of_pos hpos)))
  show (S.play A hT ω').w b = _
  rw [hconst ω' hmem]

/-! ### Assumption 5 -/

/-- **Assumption 5 (precommitment form) at time `0`** in the Omega model: for a time-`0` precommitment
`A` at a positive world, both influences are the `A(hT, S̄)`-average of the pure-action influences —
because they are affine in the global profile (`IP_zero_eq`, `IEo_zero_eq`) and the profile is the
action (`prof_eq_play`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5
Kind: P
Fidelity: exact
Hyps: none -/
theorem A5_at_zero {A : Alg Bool Bool Bool 2} {ω : PWorld Bool Bool Bool Bool 2}
    (hω : 0 < aspModel.baseW ω) (hconst : S.ConstOnAtom 0 A hT ω) (o : Bool) :
    S.IP 0 A hT o ω = ∑ a, (S.play A hT ω).w a * S.IP 0 (ofAct a) hT o ω ∧
      S.IEo 0 A hT o ω = ∑ a, (S.play A hT ω).w a * S.IEo 0 (ofAct a) hT o ω := by
  have hat : S.AtomEq 0 ω ω₀ := atomEq_zero_of_pos hω
  have hmP : ∀ A' : Alg Bool Bool Bool 2, S.IP 0 A' hT o ω = S.IP 0 A' hT o ω₀ :=
    fun A' => S.IP_measAt 0 A' hT o ω ω₀ hat
  have hmE : ∀ A' : Alg Bool Bool Bool 2, S.IEo 0 A' hT o ω = S.IEo 0 A' hT o ω₀ :=
    fun A' => S.IEo_measAt 0 A' hT o ω ω₀ hat
  have hprof : aspModel.prof A hT = S.play A hT ω := prof_eq_play hω hconst
  have hsum : (S.play A hT ω).w true + (S.play A hT ω).w false = 1 := by
    have := (S.play A hT ω).sum_one
    simpa [Fintype.sum_bool] using this
  constructor
  · simp only [hmP, IP_zero_eq, hprof, aspModel.prof_ofAct hreach, FinDist.delta_w, Fintype.sum_bool]
    cases o <;> norm_num <;> linear_combination (1 / 4) * hsum
  · simp only [hmE, IEo_zero_eq, hprof, aspModel.prof_ofAct hreach, FinDist.delta_w, Fintype.sum_bool]
    cases o <;> norm_num <;> linear_combination (1 / 8) * hsum

/-- **Assumption 5 holds in the Omega model** (closing the open statement of repair round 1): at time
`0` by `A5_at_zero`, at time `1` because both influences of every algorithm vanish (`IP_one_eq_zero`,
`IEo_one_eq_zero`). `A5_model` did not apply because `OneEps hT` fails (the root profile read and the
action at `hT` are two ε-sensitive steps); the proof here is the two-factor computation directly.
With it, `not_CEI` refutes Conservation of Expected Influence inside the full hypothesis package of
`theorem1` (`A1`, `A3`, `A4`, `A5`, `AllPosObs`, `ReachPos hT`), as the mandate's T6(b) asked. The
precommitment form holds here only because `ξ₀` is deterministic (the time-`0` atom is the support):
with a fair private `ξ₀` it fails (`Priv.not_A5`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5; mandate T6(b) (the trap: CEI's failure exhibited inside Theorem 1's scope)
Kind: P
Fidelity: exact
Hyps: none -/
theorem A5_asp : S.A5 hT := by
  intro n hn A ω hω _ hconst o
  have hn' : n ≤ 1 := hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · exact A5_at_zero hω hconst o
  · simp only [(fun A' => IP_one_eq_zero A' hω), (fun A' => IEo_one_eq_zero A' hω), mul_zero,
      Finset.sum_const_zero, and_self]

end

end Omega

end Cleanroom.Udt.UdtInfluence101
