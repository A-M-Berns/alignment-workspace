import Cleanroom.Uea.UeaSelfGame.Existence
import Cleanroom.Uea.UeaSelfGame.Tables

/-!
# Herrmann versus the extension: the `|S| = 1` witness and the Herrmann map's closed-graph failure

`S = Fin 1`, `A = Fin 2`, `U(a) = 9/10`, `U(b) = 1`, `Po = δ_a`, `piStar = b`, `δ ∈ (0,1)`. The pure policy
`a` is a Herrmann fixed point for every `δ` (`b` is unavailable: no belief mass plays it), with the trust
bound iff `1/10 ≤ δ` (equality at `δ = 1/10`), and it is *not* an extension fixed point (`Fext b = U(b) =
1 > 9/10 = Fext a`). And the Herrmann best-response map `σ ↦ ∏_s Δ(argmax over available actions)` has no
closed graph over `∏_s Δ(A)`: along `σ_n = (1 − 1/(n+1)) a + (1/(n+1)) b → δ_a`, `b` is available with
`F_herr(b) = 1 > F_herr(a) = 9/10`, so `δ_b ∈ BR_Herr(σ_n)` for all `n`, while `δ_b ∉ BR_Herr(δ_a)` (`b`
unavailable there). This is why existence (target 8b) is stated for the extension: the finite analogue of
`uea-cole-shadow`'s Gap 1.

Scope: finite updateless self-game — self-consistent belief, product self-hypothesis, Herrmann's
availability versus the continuous extension; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset Filter Topology
open Cleanroom.Found.FixKakutani

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-- Allowed actions of the Herrmann best-response map: available, and no available action does better.
Source: [[updateless-self-game]] §6 ("with Herrmann's convention the best-response correspondence");
`F_herr`, `is_fixed_point` (`convention='herr'`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Sherr (σ : S → A → ℝ) (s : S) (a : A) : Prop :=
  G.availMix σ s a ∧ ∀ b, G.availMix σ s b → G.Fext σ s b ≤ G.Fext σ s a

/-- Herrmann fixed points are exactly the fixed points of the Herrmann map (on `dom`).
Source: [[updateless-self-game]] §6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isFPherr_iff_mem_corrOf_Sherr {σ : S → A → ℝ} (hσ : σ ∈ dom S A) :
    G.IsFPherr σ ↔ σ ∈ corrOf G.Sherr σ := by
  have hm : IsMixed σ := mem_dom.1 hσ
  rw [mem_corrOf]
  constructor
  · intro h s
    refine ⟨hm s, fun a ha => ?_⟩
    by_contra hne
    have hpos : 0 < σ s a := lt_of_le_of_ne (hm.nonneg s a) (Ne.symm hne)
    exact ha ⟨G.availMix_of_pos s hpos, h.2 s a hpos⟩
  · intro h
    refine ⟨hm, fun s a ha b hb => ?_⟩
    have hS : G.Sherr σ s a := by
      by_contra hne; exact absurd ((h s).2 a hne) (ne_of_gt ha)
    exact hS.2 b hb

end Game

/-! ### The `|S| = 1` instance -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_fin1_arrow {M : Type*} [AddCommMonoid M] {A : Type*} [Fintype A] (f : (Fin 1 → A) → M) :
    ∑ π, f π = ∑ a, f ![a] := by
  rw [← (Equiv.funUnique (Fin 1) A).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext i
  fin_cases i
  rfl

namespace OneSituation

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- The utility `U(a) = 9/10`, `U(b) = 1` on `Fin 1 → Fin 2`.
Source: [[updateless-self-game]] §6 (mandate target 8(d))
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Ufun (π : Fin 1 → Fin 2) : ℝ := if π 0 = 0 then 9 / 10 else 1

/-- `Po = δ_a`.
Source: mandate target 8(d)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Pofun (π : Fin 1 → Fin 2) : ℝ := if π 0 = 0 then 1 else 0

/-- The `|S| = 1` instance.
Source: mandate target 8(d)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin 1) (Fin 2) where
  U := Ufun
  U_nonneg := fun π => by unfold Ufun; split_ifs <;> norm_num
  U_le_one := fun π => by unfold Ufun; split_ifs <;> norm_num
  piStar := ![1]
  piStar_max := fun π => by
    have h1 : Ufun ![1] = 1 := by simp [Ufun]
    rw [h1]; unfold Ufun; split_ifs <;> norm_num
  Po := Pofun
  Po_mem := ⟨fun π => by unfold Pofun; split_ifs <;> norm_num,
    by rw [sum_fin1_arrow]; simp [Pofun]⟩
  δ := δ
  δ_nonneg := h0.le
  δ_lt_one := h1

/-- The own policy `a`.
Source: none: infrastructure (instance datum)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polA : Fin 1 → Fin 2 := ![0]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem polA_0 : polA 0 = 0 := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_apply (π) : (game h0 h1).U π = Ufun π := rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_eq : (game h0 h1).Ustar = 1 := by simp [Game.Ustar, game, Ufun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thr_eq : (game h0 h1).thr = 1 - δ := by simp [Game.thr, Ustar_eq]; rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem fin1_ext_iff (π ρ : Fin 1 → Fin 2) : π = ρ ↔ π 0 = ρ 0 := by
  rw [funext_iff, Fin.forall_fin_one]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mu_apply (π') : (game h0 h1).muSelf polA π' =
    (1 - δ) * (if π' 0 = 0 then 1 else 0) + δ * Pofun π' := by
  unfold Game.muSelf; simp only [fin1_ext_iff, polA_0]; rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_a : condDen ((game h0 h1).muSelf polA) 0 0 = 1 := by
  unfold condDen; rw [sum_fin1_arrow]; simp [mu_apply, Pofun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_a : (game h0 h1).condNum ((game h0 h1).muSelf polA) 0 0 = 9 / 10 := by
  unfold Game.condNum; rw [sum_fin1_arrow]; simp [mu_apply, Pofun, U_apply, Ufun]
  try ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_b : condDen ((game h0 h1).muSelf polA) 0 1 = 0 := by
  unfold condDen; rw [sum_fin1_arrow]; simp [mu_apply, Pofun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_a : (game h0 h1).cond ((game h0 h1).muSelf polA) 0 0 = 9 / 10 := by
  unfold Game.cond; rw [condNum_a, condDen_a, div_one]

/-- `b` is unavailable under `μ_a`.
Source: mandate target 8(d) ("`b` unavailable")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem not_avail_b : ¬ avail ((game h0 h1).muSelf polA) 0 1 := by
  unfold avail; rw [condDen_b]; exact lt_irrefl 0

/-- **`a` is a Herrmann (pure) fixed point for every `δ`**.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(d)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem isPureFP : (game h0 h1).IsPureFP polA := by
  intro s
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  refine ⟨(game h0 h1).avail_muSelf_self polA 0, ?_⟩
  simp only [Fin.forall_fin_two, polA_0]
  exact ⟨fun _ => le_rfl, fun h => absurd h (not_avail_b h0 h1)⟩

/-- The trust bound at `a` holds iff `1/10 ≤ δ` (equality at `δ = 1/10`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(d) ("`TB` with equality")
Kind: P
Fidelity: exact (the mandate's "with equality" is the case `δ = 1/10`)
Hyps: (a) -/
theorem TB_iff : (game h0 h1).TB ((game h0 h1).muSelf polA) 0 ↔ 1 / 10 ≤ δ := by
  unfold Game.TB; rw [thr_eq]
  simp only [Fin.exists_fin_two]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · rw [cond_a] at h; linarith
    · exact absurd h (not_avail_b h0 h1)
  · intro h; exact Or.inl ⟨(game h0 h1).avail_muSelf_self polA 0, by rw [cond_a]; linarith⟩
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_pure_b : (game h0 h1).Ucoord (pureMix polA) 0 1 = 1 := by
  rw [Game.Ucoord_pureMix, U_apply]; simp [Ufun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pa_b : (game h0 h1).pa 0 1 = 0 := by
  unfold Game.pa condDen; rw [sum_fin1_arrow]; simp [game, Pofun]

/-- **`a` is not an extension fixed point**: `Fext (δ_a) b = U(b) = 1 > 9/10 = Fext (δ_a) a`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: mandate target 8(d) ("not an extension fixed point")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_isFPext_pure : ¬ (game h0 h1).IsFPext (pureMix polA) := by
  rintro ⟨_, h⟩
  have hpos : 0 < pureMix polA 0 0 := by simp [pureMix]
  have := h 0 0 hpos 1
  have hav : avail ((game h0 h1).muSelf polA) 0 0 := (game h0 h1).avail_muSelf_self polA 0
  rw [(game h0 h1).Fext_eq_Ucoord_of_pa_eq_zero _ (pa_b h0 h1), Ucoord_pure_b,
    (game h0 h1).Fext_pureMix polA hav, cond_a] at this
  norm_num at this

/-! ### The Herrmann map has no closed graph -/

/-- `σ_n := (1 − 1/(n+1)) a + (1/(n+1)) b`.
Source: mandate target 8(d)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def seq (n : ℕ) : Fin 1 → Fin 2 → ℝ :=
  fun _ a => if a = 0 then 1 - 1 / ((n : ℝ) + 1) else 1 / ((n : ℝ) + 1)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

@[simp] theorem seq_0 (n : ℕ) : seq n 0 0 = 1 - 1 / ((n : ℝ) + 1) := by simp [seq]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
@[simp] theorem seq_1 (n : ℕ) : seq n 0 1 = 1 / ((n : ℝ) + 1) := by simp [seq]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem inv_le_one' (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem seq_mem_dom (n : ℕ) : seq n ∈ dom (Fin 1) (Fin 2) := by
  rw [mem_dom]
  intro s
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  refine ⟨fun a => ?_, ?_⟩
  · have hle := inv_le_one' n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    revert a; simp only [Fin.forall_fin_two]
    constructor
    · rw [seq_0]; linarith
    · rw [seq_1]; exact hpos.le
  · rw [Fin.sum_univ_two, seq_0, seq_1]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem seq_tendsto : Tendsto seq atTop (𝓝 (pureMix polA)) := by
  rw [tendsto_pi_nhds]
  intro s
  rw [tendsto_pi_nhds]
  intro a
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  revert a; simp only [Fin.forall_fin_two]
  constructor
  · simp only [seq_0, pureMix, polA_0, if_true]
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h
    simpa using h1
  · simp only [seq_1, pureMix, polA_0]
    simpa using h
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_seq_b (n : ℕ) : (game h0 h1).Ucoord (seq n) 0 1 = 1 := by
  unfold Game.Ucoord
  rw [sum_fin1_arrow]
  simp [U_apply, Ufun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_seq_a (n : ℕ) : (game h0 h1).Ucoord (seq n) 0 0 = 9 / 10 := by
  unfold Game.Ucoord
  rw [sum_fin1_arrow]
  simp [U_apply, Ufun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pa_a : (game h0 h1).pa 0 0 = 1 := by
  unfold Game.pa condDen; rw [sum_fin1_arrow]; simp [game, Pofun]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pva_a : (game h0 h1).pva 0 0 = 9 / 10 := by
  unfold Game.pva Game.condNum; rw [sum_fin1_arrow]; simp [game, Pofun, Ufun]

/-- Along `σ_n`, `b` is available and `F_herr(b) = 1`.
Source: mandate target 8(d)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem seq_availMix_b (n : ℕ) : (game h0 h1).availMix (seq n) 0 1 := by
  unfold Game.availMix Game.denMix
  rw [pa_b, seq_1, mul_zero, add_zero]
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact mul_pos (sub_pos.2 h1) hpos
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_seq_b (n : ℕ) : (game h0 h1).Fext (seq n) 0 1 = 1 := by
  rw [(game h0 h1).Fext_eq_Ucoord_of_pa_eq_zero _ (pa_b h0 h1), Ucoord_seq_b]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_seq_a (n : ℕ) : (game h0 h1).Fext (seq n) 0 0 = 9 / 10 := by
  have hpos : 0 < (1 - (game h0 h1).δ) * seq n 0 0 + (game h0 h1).δ * 1 := by
    have hm := (seq_mem_dom n); rw [mem_dom] at hm
    have := hm.nonneg 0 0
    have hδ : (game h0 h1).δ = δ := rfl
    rw [hδ]; nlinarith
  have hav : (game h0 h1).availMix (seq n) 0 0 := by
    unfold Game.availMix Game.denMix; rw [pa_a]; exact hpos
  rw [(game h0 h1).Fext_eq_of_availMix hav, Ucoord_seq_a, pva_a]
  unfold Game.denMix; rw [pa_a, div_eq_iff (ne_of_gt hpos)]
  ring

/-- `δ_b ∈ BR_Herr(σ_n)` for every `n`.
Source: mandate target 8(d)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pureB_mem_corrOf_seq (n : ℕ) : pureMix ![1] ∈ corrOf (game h0 h1).Sherr (seq n) := by
  rw [mem_corrOf]
  intro s
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  refine ⟨(isMixed_pureMix _) 0, fun a ha => ?_⟩
  revert a; simp only [Fin.forall_fin_two]
  refine ⟨fun _ => by simp [pureMix], fun h => ?_⟩
  exfalso; apply h
  refine ⟨seq_availMix_b h0 h1 n, ?_⟩
  simp only [Fin.forall_fin_two]
  exact ⟨fun _ => by rw [Fext_seq_a, Fext_seq_b]; norm_num, fun _ => le_rfl⟩

/-- `δ_b ∉ BR_Herr(δ_a)`: `b` is unavailable at the limit.
Source: mandate target 8(d)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pureB_not_mem_corrOf_limit : pureMix ![1] ∉ corrOf (game h0 h1).Sherr (pureMix polA) := by
  rw [mem_corrOf]
  intro h
  have h1' := (h 0).2 1
  have hb : ¬ (game h0 h1).Sherr (pureMix polA) 0 1 := by
    rintro ⟨hav, _⟩
    exact not_avail_b h0 h1 ((game h0 h1).availMix_pureMix_iff polA 0 1 |>.1 hav)
  have := h1' hb
  simp [pureMix] at this

/-- **The Herrmann best-response map has no closed graph over `∏_s Δ(A)`** (the finite analogue of
`uea-cole-shadow`'s Gap 1): `(σ_n, δ_b)` lies in the graph for every `n`, `σ_n → δ_a`, and `(δ_a, δ_b)` does
not. So Kakutani does not apply to the Herrmann map verbatim; existence (`exists_isFPext`) is for the
continuous extension.
Scope: finite updateless self-game — Herrmann availability; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §6 ("the best-response correspondence does not have a closed graph");
[[uea-inventory]] 029
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_hasClosedGraphOn_herr :
    ¬ HasClosedGraphOn (corrOf (game h0 h1).Sherr) (dom (Fin 1) (Fin 2)) := by
  intro hcg
  have := (hcg.mem_of_tendsto (l := atTop) (xs := seq) (ys := fun _ => pureMix ![1])
    (Eventually.of_forall fun n => ⟨seq_mem_dom n, pureB_mem_corrOf_seq h0 h1 n⟩)
    seq_tendsto tendsto_const_nhds).2
  exact pureB_not_mem_corrOf_limit h0 h1 this

end OneSituation

end Cleanroom.Uea.UeaSelfGame
