import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Uea.UeaSelfGame.TablesMixed

/-!
# Chosen versus enacted: reading C1 (Theorem E, the near-tie instance), reading C2, C0

**Reading C1** (belief about the *enacted* policy, independent corruption at rate `δ` per situation,
conditioning on the enacted action): the belief is the product measure `prodW (kappa)` of the corruption
kernel `kappa s b := (1−δ)[b = π*(s)] + δ/(|A|−1)[b ≠ π*(s)]`, so the evidential conditional collapses to
the interventional value `Ucoord kappa s a = E_{κ_{-s}}[U(a, π'_{-s})]` — that is `cond_prodW`, already
proved. **Theorem E**: with `ρ := 1 − (1−δ)^{|S|−1}` and margin `m_s := U* − max_{a ≠ π*(s)} U(a, π*_{-s})
> 2ρ` at every `s`, the chosen policy is exactly `π*` (`theoremE`, `theoremE_realizes`); `ρ ≤ (|S|−1) δ`
(`rho_le`). Without a margin the loss is `1 − ε` at every `δ < 1/2` (`NearTie`): `U ≡ 1` except
`U(aab) = 0`, `U(bba) = ε`; the chosen policy is `bba` because each situation hedges separately and the
hedges jointly land on the worst policy. **Reading C2** (belief about the *chosen* policy, enactment noise
`ν` on top, conditioning on the chosen action) is the pointwise model with `U` replaced by the expected
enacted utility `Ut ν π := E[U(corrupt_ν π)] = Umix (kappaOf ν π)` — a definitional identity (`gameC2`,
`cond_gameC2`); Theorem A's witness survives small `ν` (not formalized, `stretch`). **C0** (certainty,
conditioning on the chosen action): every deviation is unavailable, so `π*` is trivially realized
(`C0_realizes`).

Also the earlier lab's Prop 2 threshold: in the C1 model with the *player's* Stag Hunt payoff (`S` gets
`b` if the partner plays `S`, else `0`; `H` gets `c`), Stag is the best response iff `(1−δ) b ≥ c`, i.e.
`δ ≤ 1/4` at `b = 4`, `c = 3` (`StagC1.player_threshold`); with the self-game's symmetrized `U` of
`StagHunt.lean` the C1 threshold is `δ ≤ 5/8` instead (`StagC1.symmetrized_threshold`) — the mandate's
"`δ ≤ 1/4` with `U` normalized as above" conflates the two (findings).

Scope: finite updateless self-game — pointwise conditional on one's own action with a product (C1) or
static (C2) belief; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

section C1Kernel

variable {S A : Type*} [Fintype A] [DecidableEq A]

/-- The corruption kernel of reading C1: `kappaOf δ π s b = 1−δ` if `b = π s`, else `δ/(|A|−1)`.
Source: [[updateless-self-game]] §8 (Reading C1); `corruption_belief`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def kappaOf (ν : ℝ) (π : S → A) : S → A → ℝ :=
  fun s b => if b = π s then 1 - ν else ν / ((Fintype.card A : ℝ) - 1)

omit [DecidableEq A] in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem card_sub_one_pos (hA : 2 ≤ Fintype.card A) : (0 : ℝ) < (Fintype.card A : ℝ) - 1 := by
  have : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hA
  linarith

/-- The corruption kernel is a mixed policy when `2 ≤ |A|` and `0 ≤ ν ≤ 1`.
Source: [[updateless-self-game]] §8
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem isMixed_kappaOf (hA : 2 ≤ Fintype.card A) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (π : S → A) :
    IsMixed (kappaOf ν π) := by
  have hc := card_sub_one_pos hA
  intro s
  refine ⟨fun b => ?_, ?_⟩
  · unfold kappaOf; split_ifs
    · linarith
    · positivity
  · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (π s))]
    have h1' : kappaOf ν π s (π s) = 1 - ν := by simp [kappaOf]
    have h2 : ∑ b ∈ Finset.univ.erase (π s), kappaOf ν π s b =
        ∑ b ∈ Finset.univ.erase (π s), ν / ((Fintype.card A : ℝ) - 1) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      have : b ≠ π s := Finset.ne_of_mem_erase hb
      simp [kappaOf, this]
    rw [h1', h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      nsmul_eq_mul]
    have hcard : ((Fintype.card A - 1 : ℕ) : ℝ) = (Fintype.card A : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcard, mul_div_cancel₀ _ (ne_of_gt hc)]
    ring

end C1Kernel

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-! ### Reading C1 -/

/-- **The C1 belief** `μ = ⊗_s [(1−δ) δ_{π*(s)} + δ Unif(A ∖ {π*(s)})]`, as the product measure of the
corruption kernel at `π*` and rate `δ`.
Source: [[updateless-self-game]] §8 (Reading C1); `corruption_belief`
Kind: D
Fidelity: exact (needs `2 ≤ |A|` to be a probability: `isMixed_kappaOf`)
Hyps: n/a -/
noncomputable def muC1 : (S → A) → ℝ := prodW (kappaOf G.δ G.piStar)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem isMixed_kappa (hA : 2 ≤ Fintype.card A) : IsMixed (kappaOf G.δ G.piStar) :=
  isMixed_kappaOf hA G.δ_nonneg G.δ_lt_one.le G.piStar

/-- **The product-measure identity of reading C1**: the evidential conditional of the C1 belief at an
available action is the interventional value `E_{κ_{-s}}[U(a, π'_{-s})] = Ucoord kappa s a`.
Source: [[updateless-self-game]] §8 ("the evidential conditional collapses to an interventional one")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem cond_muC1 (hA : 2 ≤ Fintype.card A) {s : S} {a : A} (ha : 0 < kappaOf G.δ G.piStar s a) :
    G.cond G.muC1 s a = G.Ucoord (kappaOf G.δ G.piStar) s a :=
  G.cond_prodW (G.isMixed_kappa hA) ha
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem avail_muC1_iff (hA : 2 ≤ Fintype.card A) (s : S) (a : A) :
    avail G.muC1 s a ↔ 0 < kappaOf G.δ G.piStar s a := by
  unfold avail muC1; rw [condDen_prodW (G.isMixed_kappa hA)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem kappa_self_pos (s : S) : 0 < kappaOf G.δ G.piStar s (G.piStar s) := by
  simp [kappaOf, G.one_sub_δ_pos]

/-- **The `(−s)`-marginal bound**: for a mixed `κ` and any `π₀` with `π₀ s = a`, `Ucoord κ s a` is within
`1 − w₀` of `U π₀`, where `w₀ := ∏_{t ≠ s} κ t (π₀ t)` is the marginal mass of `π₀`'s other coordinates
(`U ∈ [0,1]`).
Source: [[updateless-self-game]] §8 (Theorem E proof, "`|E[U(a, π'_{-s})] − U(a, π*_{-s})| ≤ ρ`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem abs_Ucoord_sub_le {κ : S → A → ℝ} (hκ : IsMixed κ) {s : S} {a : A} {π₀ : S → A}
    (hπ₀ : π₀ s = a) :
    |G.Ucoord κ s a - G.U π₀| ≤ 1 - ∏ t ∈ Finset.univ.erase s, κ t (π₀ t) := by
  set w : (S → A) → ℝ := fun π' => ∏ t ∈ Finset.univ.erase s, κ t (π' t) with hw
  have hw0 : ∀ π', 0 ≤ w π' := fun π' => Finset.prod_nonneg fun t _ => hκ.nonneg t (π' t)
  have hsum : (∑ π' : S → A, if π' s = a then w π' else 0) = 1 := sum_prod_erase_eq_one hκ s a
  have hU : G.Ucoord κ s a = ∑ π' : S → A, if π' s = a then w π' * G.U π' else 0 := rfl
  -- split off the `π₀` term
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ π₀), if_pos hπ₀] at hsum hU
  set R := ∑ π' ∈ Finset.univ.erase π₀, if π' s = a then w π' else 0 with hR
  set RU := ∑ π' ∈ Finset.univ.erase π₀, if π' s = a then w π' * G.U π' else 0 with hRU
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun π' _ => by split_ifs <;> simp [hw0]
  have hRU0 : 0 ≤ RU := Finset.sum_nonneg fun π' _ => by
    split_ifs
    · exact mul_nonneg (hw0 _) (G.U_nonneg _)
    · exact le_rfl
  have hRU1 : RU ≤ R := Finset.sum_le_sum fun π' _ => by
    split_ifs
    · have := G.U_le_one π'; have := hw0 π'; nlinarith
    · exact le_rfl
  have hw1 : w π₀ ≤ 1 := by linarith
  have hU0 := G.U_nonneg π₀; have hU1 := G.U_le_one π₀
  rw [hU, abs_le]
  constructor
  · nlinarith [hw0 π₀]
  · nlinarith [hw0 π₀]

/-- `ρ := 1 − (1−δ)^{|S|−1}`, the probability that some other situation is corrupted. The exponent is a
`Nat` subtraction: at `|S| = 0` it is `0` and `ρ = 0`, where nothing is at stake (no situation exists); for
`|S| ≥ 1` it is the note's `|S| − 1`.
Source: [[updateless-self-game]] §8 (Theorem E)
Kind: D
Fidelity: exact (for `|S| ≥ 1`; `|S| = 0` is vacuous)
Hyps: n/a -/
noncomputable def rho : ℝ := 1 - (1 - G.δ) ^ (Fintype.card S - 1)

/-- The marginal mass of "no corruption off `s`" is `(1−δ)^{|S|−1}`.
Source: [[updateless-self-game]] §8
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem prod_kappa_piStar (s : S) (π₀ : S → A) (h : ∀ t, t ≠ s → π₀ t = G.piStar t) :
    ∏ t ∈ Finset.univ.erase s, kappaOf G.δ G.piStar t (π₀ t) = (1 - G.δ) ^ (Fintype.card S - 1) := by
  have : ∀ t ∈ Finset.univ.erase s, kappaOf G.δ G.piStar t (π₀ t) = 1 - G.δ := by
    intro t ht
    rw [h t (Finset.ne_of_mem_erase ht)]
    simp [kappaOf]
  rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

/-- **C1 margin at least `m`**: `U(a, π*_{-s}) ≤ U* − m` for every `s` and `a ≠ π*(s)`.
Source: [[updateless-self-game]] §8 (Theorem E, `m_s`)
Kind: D
Fidelity: exact (as a lower bound on the note's per-situation minimum)
Hyps: n/a -/
def HasMarginC1 (m : ℝ) : Prop :=
  ∀ s a, a ≠ G.piStar s → G.U (Function.update G.piStar s a) ≤ G.Ustar - m

/-- **Theorem E (C1 margin theorem)**: if `m_s > 2ρ` at every `s`, under the C1 belief `π*(s)` is the
strict argmax at every `s` (every available `a ≠ π*(s)` has a strictly smaller conditional), so the chosen
policy is exactly `π*`. Each conditional is within `ρ` of its `π*_{-s}` value (`abs_Ucoord_sub_le`).
Scope: finite updateless self-game — reading C1 (product belief, conditioning on the enacted action);
not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §8 (Theorem E); [[uea-inventory]] 031
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremE (hA : 2 ≤ Fintype.card A) {m : ℝ} (hm : G.HasMarginC1 m) (hρ : 2 * G.rho < m) (s : S) :
    G.IsArgmaxH G.muC1 s (G.piStar s) ∧
      ∀ a, avail G.muC1 s a → a ≠ G.piStar s → G.cond G.muC1 s a < G.cond G.muC1 s (G.piStar s) := by
  have hκ := G.isMixed_kappa hA
  -- the own action's value is within `ρ` of `U*`
  have hstar : G.Ustar - G.rho ≤ G.cond G.muC1 s (G.piStar s) := by
    rw [G.cond_muC1 hA (G.kappa_self_pos s)]
    have := G.abs_Ucoord_sub_le hκ (s := s) (a := G.piStar s) (π₀ := G.piStar) rfl
    rw [G.prod_kappa_piStar s G.piStar (fun _ _ => rfl), abs_le] at this
    unfold rho Ustar; linarith [this.1]
  have hlt : ∀ a, avail G.muC1 s a → a ≠ G.piStar s →
      G.cond G.muC1 s a < G.cond G.muC1 s (G.piStar s) := by
    intro a hav hne
    have hpos := (G.avail_muC1_iff hA s a).1 hav
    rw [G.cond_muC1 hA hpos]
    have hb := G.abs_Ucoord_sub_le hκ (s := s) (a := a) (π₀ := Function.update G.piStar s a)
      (Function.update_self s a G.piStar)
    rw [G.prod_kappa_piStar s _ (fun t ht => Function.update_of_ne ht a G.piStar), abs_le] at hb
    have hmarg := hm s a hne
    unfold rho at hρ hstar
    linarith [hb.2]
  refine ⟨⟨(G.avail_muC1_iff hA s _).2 (G.kappa_self_pos s), fun b hb => ?_⟩, hlt⟩
  by_cases hbe : b = G.piStar s
  · rw [hbe]
  · exact (hlt b hb hbe).le

/-- Theorem E, conclusion form: the unique chosen policy is `π*`, and `π*` is chosen.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §8 (Theorem E, "the chosen policy is exactly `π*`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremE_realizes (hA : 2 ≤ Fintype.card A) {m : ℝ} (hm : G.HasMarginC1 m) (hρ : 2 * G.rho < m) :
    G.Realizes G.muC1 G.piStar ∧ ∀ π, G.Realizes G.muC1 π → π = G.piStar := by
  refine ⟨fun s => (G.theoremE hA hm hρ s).1, fun π hπ => funext fun s => ?_⟩
  obtain ⟨hmax, hlt⟩ := G.theoremE hA hm hρ s
  by_contra hne
  have h1 := hlt (π s) (hπ s).1 hne
  have h2 := (hπ s).2 (G.piStar s) hmax.1
  linarith

omit [DecidableEq A] in
/-- `ρ ≤ (|S|−1) δ` (Bernoulli), so margin `> 2(|S|−1) δ` suffices — horizon-dependent.
Source: [[updateless-self-game]] §8 ("Since `ρ ≤ (|S|−1)δ`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem rho_le : G.rho ≤ ((Fintype.card S - 1 : ℕ) : ℝ) * G.δ := by
  unfold rho
  have h := one_add_mul_le_pow (a := -G.δ) (by linarith [G.δ_lt_one]) (Fintype.card S - 1)
  have : (1 : ℝ) + -G.δ = 1 - G.δ := by ring
  rw [this] at h
  linarith

/-! ### Reading C2 -/

/-- The expected enacted utility under enactment noise `ν`: `Ut ν π := E[U(corrupt_ν π)] = Umix (kappaOf ν π)`.
Source: [[updateless-self-game]] §8 (Reading C2, `Ũ_ν`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Ut (ν : ℝ) (π : S → A) : ℝ := G.Umix (kappaOf ν π)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ut_mem_Icc (hA : 2 ≤ Fintype.card A) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (π : S → A) :
    0 ≤ G.Ut ν π ∧ G.Ut ν π ≤ 1 := by
  have hκ := isMixed_kappaOf hA h0 h1 π
  unfold Ut Umix
  constructor
  · exact Finset.sum_nonneg fun π' _ => mul_nonneg (prodW_nonneg hκ π') (G.U_nonneg π')
  · calc ∑ π', prodW (kappaOf ν π) π' * G.U π' ≤ ∑ π', prodW (kappaOf ν π) π' :=
        Finset.sum_le_sum fun π' _ => by
          have := G.U_le_one π'; have := prodW_nonneg hκ π'; nlinarith
      _ = 1 := sum_prodW hκ

/-- At `ν = 0` the enacted utility is `U` (no noise).
Source: [[updateless-self-game]] §8
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ut_zero (π : S → A) : G.Ut 0 π = G.U π := by
  unfold Ut
  have : kappaOf 0 π = pureMix π := by
    funext s b; simp [kappaOf, pureMix]
  rw [this, G.Umix_pureMix]

/-- **Reading C2 is the pointwise model with `U := Ut ν`**: the game with the same `Po`, `δ` and the
expected enacted utility (its chosen optimum is a maximizer of `Ut ν`, by `Finset.exists_max_image`).
Source: [[updateless-self-game]] §8 (Reading C2, "This is the pointwise model of §1 with `U` replaced by `Ũ_ν`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def gameC2 (hA : 2 ≤ Fintype.card A) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) : Game S A where
  U := G.Ut ν
  U_nonneg := fun π => (G.Ut_mem_Icc hA h0 h1 π).1
  U_le_one := fun π => (G.Ut_mem_Icc hA h0 h1 π).2
  piStar := Classical.choose (Finset.exists_max_image Finset.univ (G.Ut ν) ⟨G.piStar, Finset.mem_univ _⟩)
  piStar_max := fun π =>
    (Classical.choose_spec (Finset.exists_max_image Finset.univ (G.Ut ν) ⟨G.piStar, Finset.mem_univ _⟩)).2
      π (Finset.mem_univ _)
  Po := G.Po
  Po_mem := G.Po_mem
  δ := G.δ
  δ_nonneg := G.δ_nonneg
  δ_lt_one := G.δ_lt_one

/-- The C2 conditional — the belief `μ` over chosen policies conditioned on the chosen action, scoring the
expected enacted utility — is literally `cond` of the C2 game: `(∑_{π' s = a} μ π' Ut ν π') / μ(π' s = a)`.
Source: [[updateless-self-game]] §8 (Reading C2, "`E[U(enacted) | chosen(s) = a] = E_{π'∼μ}[Ũ_ν(π') | π'(s) = a]`")
Kind: L
Fidelity: exact (definitional)
Hyps: (a) -/
theorem cond_gameC2 (hA : 2 ≤ Fintype.card A) {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (μ : (S → A) → ℝ) (s : S)
    (a : A) : (G.gameC2 hA h0 h1).cond μ s a =
      (∑ π', if π' s = a then μ π' * G.Ut ν π' else 0) / condDen μ s a := rfl

/-! ### Reading C0 -/

/-- **C0 (certainty about the chosen policy, conditioning on the chosen action)**: under `δ_{π*}` every
deviation is unavailable and `π*` is realized — a `δ = 0` statement with no content.
Source: [[updateless-self-game]] §8 (Reading C0)
Kind: T
Fidelity: exact
Hyps: (a) -/
theorem C0_realizes (h0 : G.δ = 0) :
    G.Realizes G.mu G.piStar ∧ ∀ s a, a ≠ G.piStar s → ¬ avail G.mu s a := by
  constructor
  · intro s
    refine ⟨G.avail_muSelf_self G.piStar s, fun b hb => ?_⟩
    by_cases hbe : b = G.piStar s
    · rw [hbe]
    · exfalso
      unfold avail mu at hb
      rw [G.condDen_muSelf, if_neg (Ne.symm hbe), h0] at hb
      simp at hb
  · intro s a hne hav
    unfold avail mu at hav
    rw [G.condDen_muSelf, if_neg (Ne.symm hne), h0] at hav
    simp at hav

end Game

/-! ### The near-tie instance (reading C1, no margin): loss `1 − ε` at every `δ < 1/2` -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem fin2_eq_zero_of_ne_one : ∀ x : Fin 2, x ≠ 1 → x = 0 := by
  simp only [Fin.forall_fin_two]; simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem fin2_eq_one_of_ne_zero : ∀ x : Fin 2, x ≠ 0 → x = 1 := by
  simp only [Fin.forall_fin_two]; simp

namespace NearTie

variable {δ ε : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) (e0 : 0 < ε) (e1 : ε < 1)

/-- `U ≡ 1` except `U(aab) = 0`, `U(bba) = ε`; `piStar = aaa`; `Po` irrelevant (uniform on `aaa`).
Source: [[updateless-self-game]] §8 ("Near-tie counterexample")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 3) (Fin 2) where
  U := tab3 1 0 1 1 1 1 ε 1
  U_nonneg := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ⟨by linarith, by linarith⟩ (by norm_num) π).1
  U_le_one := fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ⟨by linarith, by linarith⟩ (by norm_num) π).2
  piStar := ![0, 0, 0]
  piStar_max := fun π => by
    rw [tab3_000]
    exact (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) ⟨by linarith, by linarith⟩ (by norm_num) π).2
  Po := tab3 1 0 0 0 0 0 0 0
  Po_mem := ⟨fun π => (tab3_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).1,
    by rw [sum_tab3]; norm_num⟩
  δ := δ
  δ_nonneg := h0.le
  δ_lt_one := by linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π) : (game h0 h1 e0 e1).U π = tab3 1 0 1 1 1 1 ε 1 π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem kappa_apply (s : Fin 3) (b : Fin 2) :
    kappaOf (game h0 h1 e0 e1).δ (game h0 h1 e0 e1).piStar s b = if b = 0 then 1 - δ else δ := by
  unfold kappaOf
  have hp : (game h0 h1 e0 e1).piStar s = 0 := by
    show (![0, 0, 0] : Fin 3 → Fin 2) s = 0
    fin_cases s <;> rfl
  rw [hp]
  have hc : ((Fintype.card (Fin 2) : ℝ) - 1) = 1 := by norm_num
  rw [hc, div_one]
  rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem kappa_pos (s : Fin 3) (b : Fin 2) :
    0 < kappaOf (game h0 h1 e0 e1).δ (game h0 h1 e0 e1).piStar s b := by
  rw [kappa_apply]; split_ifs <;> linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem hA : 2 ≤ Fintype.card (Fin 2) := by simp

/-- The six interventional values: at `s₀`, `a ↦ (1−δ) + δ²`, `b ↦ (1−δ) + δ² + δ(1−δ)ε`; at `s₁` the same;
at `s₂`, `a ↦ 1 − δ²(1−ε)`, `b ↦ 2δ − δ²`.
Source: [[updateless-self-game]] §8 ("At `s_0`: … `δ(1−δ)ε > 0`; … at `s_2`, `a` wins by `(1−δ)² − δ²(1−ε)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Ucoord_vals :
    (game h0 h1 e0 e1).Ucoord (kappaOf δ ![0, 0, 0]) 0 0 = (1 - δ) + δ ^ 2 ∧
    (game h0 h1 e0 e1).Ucoord (kappaOf δ ![0, 0, 0]) 0 1 = (1 - δ) + δ ^ 2 + δ * (1 - δ) * ε ∧
    (game h0 h1 e0 e1).Ucoord (kappaOf δ ![0, 0, 0]) 1 0 = (1 - δ) + δ ^ 2 ∧
    (game h0 h1 e0 e1).Ucoord (kappaOf δ ![0, 0, 0]) 1 1 = (1 - δ) + δ ^ 2 + δ * (1 - δ) * ε ∧
    (game h0 h1 e0 e1).Ucoord (kappaOf δ ![0, 0, 0]) 2 0 = 1 - δ ^ 2 * (1 - ε) ∧
    (game h0 h1 e0 e1).Ucoord (kappaOf δ ![0, 0, 0]) 2 1 = 2 * δ - δ ^ 2 := by
  have hk : ∀ (s : Fin 3) (b : Fin 2), kappaOf δ ![0, 0, 0] s b = if b = 0 then 1 - δ else δ :=
    fun s b => kappa_apply h0 h1 e0 e1 s b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Game.Ucoord_fin3_0]; simp [Fin.sum_univ_two, hk, U_apply]; ring
  · rw [Game.Ucoord_fin3_0]; simp [Fin.sum_univ_two, hk, U_apply]; ring
  · rw [Game.Ucoord_fin3_1]; simp [Fin.sum_univ_two, hk, U_apply]; ring
  · rw [Game.Ucoord_fin3_1]; simp [Fin.sum_univ_two, hk, U_apply]; ring
  · rw [Game.Ucoord_fin3_2]; simp [Fin.sum_univ_two, hk, U_apply]; ring
  · rw [Game.Ucoord_fin3_2]; simp [Fin.sum_univ_two, hk, U_apply]; ring

/-- **The chosen policy under C1 is exactly `bba`, with `U(bba) = ε`**, for every `δ ∈ (0, 1/2)` and
`ε ∈ (0,1)`: at `s₀`, `s₁` the hedge `b` wins by `δ(1−δ)ε`; at `s₂`, `a` wins by `(1−δ)² − δ²(1−ε)`.
The loss is `1 − ε` at every `δ` — without a margin the C1 reading fails too.
Refutes: the C1 reading of [[summer-research-plan-2026--research-ideas-may-2026]] line 48 via journal
[[2026-03-26]] line 64 (*"it believes the chosen policy = udt 1.1, not the enacted policy"*) — that C1
is what is meant is ATTRIBUTION-UNVETTED; surviving neighbour: `theoremE` (margin `> 2ρ`).
Scope: finite updateless self-game — reading C1; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §8 ("Near-tie counterexample"); [[uea-inventory]] 031
Kind: P
Fidelity: exact (symbolic `δ`, `ε`)
Hyps: (a) -/
theorem realizes_iff (π : Fin 3 → Fin 2) :
    (game h0 h1 e0 e1).Realizes (game h0 h1 e0 e1).muC1 π ↔ π = ![1, 1, 0] := by
  obtain ⟨v00, v01, v10, v11, v20, v21⟩ := Ucoord_vals h0 h1 e0 e1
  have hc : ∀ s a, (game h0 h1 e0 e1).cond (game h0 h1 e0 e1).muC1 s a =
      (game h0 h1 e0 e1).Ucoord (kappaOf δ ![0, 0, 0]) s a := fun s a =>
    (game h0 h1 e0 e1).cond_muC1 hA (kappa_pos h0 h1 e0 e1 s a)
  have hav : ∀ s a, avail (game h0 h1 e0 e1).muC1 s a := fun s a =>
    ((game h0 h1 e0 e1).avail_muC1_iff hA s a).2 (kappa_pos h0 h1 e0 e1 s a)
  have hδ1 : 0 < 1 - δ := by linarith
  have d0 : (1 - δ) + δ ^ 2 < (1 - δ) + δ ^ 2 + δ * (1 - δ) * ε := by nlinarith [mul_pos (mul_pos h0 hδ1) e0]
  have d2 : 2 * δ - δ ^ 2 < 1 - δ ^ 2 * (1 - ε) := by nlinarith [mul_pos (mul_pos h0 h0) e0]
  constructor
  · intro h
    have hrep : π = ![π 0, π 1, π 2] := by funext i; fin_cases i <;> rfl
    rw [hrep]
    have e0' : π 0 = 1 := by
      by_contra hne
      have h00 : π 0 = 0 := fin2_eq_zero_of_ne_one _ hne
      have := (h 0).2 1 (hav 0 1)
      rw [h00, hc, hc, v00, v01] at this; linarith
    have e1' : π 1 = 1 := by
      by_contra hne
      have h10 : π 1 = 0 := fin2_eq_zero_of_ne_one _ hne
      have := (h 1).2 1 (hav 1 1)
      rw [h10, hc, hc, v10, v11] at this; linarith
    have e2' : π 2 = 0 := by
      by_contra hne
      have h21 : π 2 = 1 := fin2_eq_one_of_ne_zero _ hne
      have := (h 2).2 0 (hav 2 0)
      rw [h21, hc, hc, v20, v21] at this; linarith
    rw [e0', e1', e2']
  · rintro rfl
    unfold Game.Realizes Game.IsArgmaxH
    simp only [forall_fin_three, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨hav 0 1, fun _ => ?_, fun _ => le_rfl⟩, ⟨hav 1 1, fun _ => ?_, fun _ => le_rfl⟩,
      ⟨hav 2 0, fun _ => le_rfl, fun _ => ?_⟩⟩
    · rw [hc, hc, v00, v01]; exact d0.le
    · rw [hc, hc, v10, v11]; exact d0.le
    · rw [hc, hc, v20, v21]; exact d2.le

/-- The loss is `1 − ε`.
Source: [[updateless-self-game]] §8 ("Chosen policy `bba`, `U = ε`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem loss (π : Fin 3 → Fin 2) (hπ : (game h0 h1 e0 e1).Realizes (game h0 h1 e0 e1).muC1 π) :
    (game h0 h1 e0 e1).Ustar - (game h0 h1 e0 e1).U π = 1 - ε := by
  rw [(realizes_iff h0 h1 e0 e1 π).1 hπ, U_apply]
  simp [Game.Ustar, game]

end NearTie

/-! ### The earlier lab's Prop 2 threshold in the C1 model -/

namespace StagC1

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- The *player's* Stag Hunt payoff normalized by `b = 4`: `S` gets `1` if the partner plays `S`, else `0`;
`H` gets `c/b = 3/4`. Order `(own, partner)`: `SS = 1, SH = 0, HS = 3/4, HH = 3/4`.
Source: [[models--unbounded-embedded-agency-model]] Prop 2 (`stag_hunt_select`); trust-lab 033
Kind: D
Fidelity: exact (the player's payoff, not the self-game's symmetrized `U`)
Hyps: n/a -/
noncomputable def playerGame : Game (Fin 2) (Fin 2) where
  U := tab2 1 0 (3 / 4) (3 / 4)
  U_nonneg := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).1
  U_le_one := fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) π).2
  piStar := ![0, 0]
  piStar_max := fun π => by
    rw [tab2_00]
    exact (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) π).2
  Po := tab2 1 0 0 0
  Po_mem := ⟨fun π => (tab2_bounds (lo := 0) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) π).1, by rw [sum_tab2]; norm_num⟩
  δ := δ
  δ_nonneg := h0.le
  δ_lt_one := h1
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem player_kappa (s : Fin 2) (b : Fin 2) :
    kappaOf δ ![0, 0] s b = if b = 0 then 1 - δ else δ := by
  unfold kappaOf
  have hp : (![0, 0] : Fin 2 → Fin 2) s = 0 := by fin_cases s <;> rfl
  rw [hp]
  have hc : ((Fintype.card (Fin 2) : ℝ) - 1) = 1 := by norm_num
  rw [hc, div_one]

/-- **Prop 2's threshold is the C1 (interventional) threshold**: under the C1 belief with the player's
payoff, Stag is the best response at `s₀` iff `(1−δ)·1 ≥ 3/4`, i.e. iff `δ ≤ 1/4` — `(1−δ) b ≥ c`.
Source: [[models--unbounded-embedded-agency-model]] Prop 2; [[updateless-self-game]] §9 ("reading C1's
conditional (product belief), not the EDT conditional")
Kind: P
Fidelity: variant: the C1 model with the player's payoff (the earlier lab's `stag_hunt_select` reading)
Hyps: (a) -/
theorem player_threshold :
    (playerGame h0 h1).cond (playerGame h0 h1).muC1 0 1 ≤ (playerGame h0 h1).cond (playerGame h0 h1).muC1 0 0 ↔
      δ ≤ 1 / 4 := by
  have hA : 2 ≤ Fintype.card (Fin 2) := by simp
  have hk : ∀ b, 0 < kappaOf (playerGame h0 h1).δ (playerGame h0 h1).piStar 0 b := by
    intro b; show 0 < kappaOf δ ![0, 0] 0 b
    rw [player_kappa]; split_ifs <;> linarith
  rw [(playerGame h0 h1).cond_muC1 hA (hk 0), (playerGame h0 h1).cond_muC1 hA (hk 1)]
  show (playerGame h0 h1).Ucoord (kappaOf δ ![0, 0]) 0 1 ≤
    (playerGame h0 h1).Ucoord (kappaOf δ ![0, 0]) 0 0 ↔ δ ≤ 1 / 4
  rw [Game.Ucoord_fin2_0, Game.Ucoord_fin2_0]
  simp [Fin.sum_univ_two, player_kappa, playerGame]
  constructor <;> intro h <;> linarith

/-- With the self-game's symmetrized `U` (`StagHunt.lean`: `SS = 1`, `SH = HS = 3/8`, `HH = 3/4`) the C1
threshold is `δ ≤ 5/8`, not `1/4`: the mandate's "`(1−δ) b ≥ c` with `U` normalized as above" conflates
the player's payoff with the symmetrized utility (findings).
Source: [[uea-self-game-mandate]] target 7 (the `variant` row)
Kind: P
Fidelity: variant (symmetrized `U`)
Hyps: (a) -/
theorem symmetrized_threshold (h0 : 0 < δ) (h1 : δ < 1) (G : Game (Fin 2) (Fin 2))
    (hU : G.U = tab2 1 (3 / 8) (3 / 8) (3 / 4))
    (hπ : G.piStar = ![0, 0]) (hδ : G.δ = δ) :
    G.cond G.muC1 0 1 ≤ G.cond G.muC1 0 0 ↔ δ ≤ 5 / 8 := by
  have hA : 2 ≤ Fintype.card (Fin 2) := by simp
  have hkap : ∀ s b, kappaOf G.δ G.piStar s b = if b = 0 then 1 - δ else δ := by
    intro s b
    unfold kappaOf
    have hp : G.piStar s = 0 := by rw [hπ]; fin_cases s <;> rfl
    have hc : ((Fintype.card (Fin 2) : ℝ) - 1) = 1 := by norm_num
    rw [hp, hc, div_one, hδ]
  have hk : ∀ b, 0 < kappaOf G.δ G.piStar 0 b := by
    intro b; rw [hkap]; split_ifs <;> linarith
  rw [G.cond_muC1 hA (hk 0), G.cond_muC1 hA (hk 1), Game.Ucoord_fin2_0, Game.Ucoord_fin2_0]
  simp [Fin.sum_univ_two, hkap, hU]
  constructor <;> intro h <;> linarith

end StagC1

end Cleanroom.Uea.UeaSelfGame
