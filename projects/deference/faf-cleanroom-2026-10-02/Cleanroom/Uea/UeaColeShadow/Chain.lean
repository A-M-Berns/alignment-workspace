import Cleanroom.Uea.UeaColeShadow.Floored
import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# The chain lower bound: a chain of equality nodes refutes "`C · O_h`, horizon-free"

`chain P` (`P = ⟨K, δ⟩`, `0 < δ < 1`): nodes `h₀ … h_K` along `go`; at `h_k` (`k < K`) `out` is a leaf with reward
`r_k := 1 / (1 + O₀ 2^k)`, `O₀ := δ/(1-δ)`; at `h_K`, `go` pays `1` and `out` pays `0`; one residual hypothesis of
weight `δ` playing `go` at `h₀ … h_{K-1}` and `out` at `h_K`. Actions are `Fin 2` with `0 = out`, `1 = go`. The
policy `chainPol`: `go` with probability `1/2` at `h₀ … h_{K-1}`, `go` surely at `h_K`.

Proved for **every** `K` and `δ` (the note verifies seven `(δ, K)` pairs and claims the closed form): `chainPol` is
a floored fixed point and not a plain one (`K ≥ 1`); `w_{h_k} = r_k`; `h_k` is an equality node for `k < K` (the
odds double at each step) and `h_K` is a strict-argmax node; and
`ε(h₀) = (O₀/2) ∑_{k<K} 1/(1 + O₀ 2^k)`. Corollary: for every `C` there is a model, a floored fixed point and a node
with `0 < w_h` and `ε(h) > C · O_h` — the founding sketch's horizon-free `C · O_h` bound is refuted, and Theorem C's
logarithm is necessary.

Source: [[sequential-self-game]] §4.3; `sequential_self_game.py` `chain_instance`; [[uea-inventory]] 012.
Scope: finite shadow of rOSI ([[sequential-self-game]] §7).
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Chain

/-- Parameters of a chain instance: length `K` and non-self prior `δ ∈ (0,1)`.
Source: [[sequential-self-game]] §4.3
Kind: D
Fidelity: exact
Hyps: n/a -/
structure CP where
  K : ℕ
  δ : ℝ
  hδ : 0 < δ
  hδ1 : δ < 1

variable (P : CP)

/-- `O₀ := δ / (1 - δ)`. -/
noncomputable def O0 : ℝ := P.δ / (1 - P.δ)

/-- `r_k := 1 / (1 + O₀ 2^k)`. -/
noncomputable def rk (k : ℕ) : ℝ := 1 / (1 + O0 P * 2 ^ k)

theorem O0_pos : 0 < O0 P := div_pos P.hδ (by linarith [P.hδ1])

theorem rk_pos (k : ℕ) : 0 < rk P k := by
  unfold rk
  have := O0_pos P
  positivity

theorem rk_lt_one (k : ℕ) : rk P k < 1 := by
  unfold rk
  have h := O0_pos P
  have h2 : (0:ℝ) < 2 ^ k := by positivity
  rw [div_lt_one (by positivity)]
  nlinarith

theorem rk_le_one (k : ℕ) : rk P k ≤ 1 := (rk_lt_one P k).le

theorem rk_succ_lt (k : ℕ) : rk P (k + 1) < rk P k := by
  unfold rk
  have h := O0_pos P
  have h2 : (0:ℝ) < 2 ^ k := by positivity
  apply one_div_lt_one_div_of_lt (by positivity)
  rw [pow_succ]
  nlinarith

theorem one_sub_rk (k : ℕ) : 1 - rk P k = O0 P * 2 ^ k / (1 + O0 P * 2 ^ k) := by
  unfold rk
  have h := O0_pos P
  have h2 : (0:ℝ) < 2 ^ k := by positivity
  field_simp
  ring

/-- All actions of a history are `go`. -/
def allGo (n : ℕ) (h : Hist (Fin 2) Unit n) : Prop := ∀ i : Fin n, (h i).1 = 1

instance (n : ℕ) (h : Hist (Fin 2) Unit n) : Decidable (allGo n h) := by unfold allGo; infer_instance

/-- The all-`go` history `h_n`. -/
def goH (n : ℕ) : Hist (Fin 2) Unit n := fun _ => (1, ())

theorem allGo_goH (n : ℕ) : allGo n (goH n) := fun _ => rfl

theorem goH_ext (n : ℕ) (e : Unit) : ext (goH n) 1 e = goH (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [goH]
  · simp [goH]

theorem eq_goH_of_allGo {n : ℕ} {h : Hist (Fin 2) Unit n} (hg : allGo n h) : h = goH n := by
  funext i
  exact Prod.ext (hg i) (Subsingleton.elim _ _)

theorem allGo_ext_iff {n : ℕ} (h : Hist (Fin 2) Unit n) (a : Fin 2) :
    allGo (n + 1) (ext h a ()) ↔ allGo n h ∧ a = 1 := by
  constructor
  · intro hg
    refine ⟨fun i => ?_, ?_⟩
    · have := hg (Fin.castSucc i); simpa using this
    · have := hg (Fin.last n); simpa using this
  · rintro ⟨hg, rfl⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hg j

theorem not_allGo_ext_zero {n : ℕ} (h : Hist (Fin 2) Unit n) (e : Unit) : ¬ allGo (n + 1) (ext h 0 e) := by
  rw [allGo_ext_iff]
  rintro ⟨_, h1⟩
  exact absurd h1 (by decide)

/-- Alive nodes: the all-`go` histories of depth `≤ K`. -/
def alive (n : ℕ) (h : Hist (Fin 2) Unit n) : Bool := decide (n ≤ P.K ∧ allGo n h)

theorem alive_iff (n : ℕ) (h : Hist (Fin 2) Unit n) : alive P n h = true ↔ n ≤ P.K ∧ allGo n h := by
  simp [alive]

theorem alive_init (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) (hh : alive P (n + 1) h = true) :
    alive P n (Fin.init h) = true := by
  rw [alive_iff] at hh ⊢
  refine ⟨by omega, fun i => ?_⟩
  simpa [Fin.init] using hh.2 (Fin.castSucc i)

/-- Rewards on arrival at a depth-`(n+1)` history: `r_n` for `out` at `h_n` (`n < K`); `1` for `go` at `h_K`. -/
noncomputable def r (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : ℝ :=
  if allGo n (Fin.init h) ∧ n < P.K ∧ (h (Fin.last n)).1 = 0 then rk P n
  else if allGo n (Fin.init h) ∧ n = P.K ∧ (h (Fin.last n)).1 = 1 then 1 else 0

theorem r_nonneg (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : 0 ≤ r P n h := by
  unfold r
  split_ifs
  · exact (rk_pos P n).le
  · exact zero_le_one
  · exact le_rfl

theorem r_le_one (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : r P n h ≤ 1 := by
  unfold r
  split_ifs
  · exact rk_le_one P n
  · exact le_rfl
  · exact zero_le_one

theorem r_ext_zero (n : ℕ) (e : Unit) : r P n (ext (goH n) 0 e) = if n < P.K then rk P n else 0 := by
  unfold r
  simp [allGo_goH]

theorem r_ext_one (n : ℕ) (e : Unit) : r P n (ext (goH n) 1 e) = if n = P.K then 1 else 0 := by
  unfold r
  simp [allGo_goH]

theorem r_goH_succ (n : ℕ) : r P n (goH (n + 1)) = if n = P.K then 1 else 0 := by
  rw [← goH_ext n ()]; exact r_ext_one P n ()

theorem r_eq_zero_of_not_allGo {n : ℕ} (h : Hist (Fin 2) Unit (n + 1)) (hg : ¬ allGo n (Fin.init h)) : r P n h = 0 := by
  unfold r
  simp [hg]

/-- Path returns: `0` along an all-`go` prefix of depth `≤ K`, and at most `1` everywhere. -/
theorem pathReturn_bounds : ∀ (n : ℕ) (h : Hist (Fin 2) Unit n), n ≤ P.K + 1 →
    pathReturnOf 1 (r P) n h ≤ 1 ∧ (n ≤ P.K → allGo n h → pathReturnOf 1 (r P) n h = 0) := by
  intro n
  induction n with
  | zero => intro h _; simp
  | succ n ih =>
    intro h hn
    obtain ⟨ih1, ih2⟩ := ih (Fin.init h) (by omega)
    simp only [pathReturnOf, one_pow, one_mul]
    by_cases hg : allGo n (Fin.init h)
    · have h0 := ih2 (by omega) hg
      rw [h0, zero_add]
      refine ⟨r_le_one P n h, fun hK hga => ?_⟩
      have hlast : (h (Fin.last n)).1 = 1 := hga (Fin.last n)
      unfold r
      simp [hlast, show n ≠ P.K by omega]
    · rw [r_eq_zero_of_not_allGo P h hg, add_zero]
      refine ⟨ih1, fun _ hga => absurd (fun i => by simpa [Fin.init] using hga (Fin.castSucc i)) hg⟩

theorem norm (n : ℕ) (hn : n ≤ P.K + 1) (h : Hist (Fin 2) Unit n) : pathReturnOf 1 (r P) n h ≤ 1 :=
  (pathReturn_bounds P n h hn).1

/-- The residual's action kernel: `go` below depth `K`, `out` at depth `≥ K`. -/
noncomputable def νa : Unit → (n : ℕ) → Hist (Fin 2) Unit n → Fin 2 → ℝ :=
  fun _ n _ a => if n < P.K then (if a = 1 then 1 else 0) else (if a = 0 then 1 else 0)

theorem νa_mem (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) : νa P i n h ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun a => ?_, ?_⟩
  · unfold νa; split_ifs <;> norm_num
  · unfold νa; split_ifs <;> simp [Fin.sum_univ_two]

/-- **The chain instance** `chain P`: `T = K + 1`, `γ = 1`, one residual of weight `δ`.
Source: [[sequential-self-game]] §4.3 (`chain_instance`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def chain : Model (Fin 2) Unit Unit where
  T := P.K + 1
  alive := alive P
  alive_init := alive_init P
  r := r P
  r_nonneg := r_nonneg P
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := norm P
  νa := νa P
  νe := fun _ _ _ _ _ => 1
  νa_mem := νa_mem P
  νe_mem := fun _ _ _ _ => ⟨fun _ => zero_le_one, by simp⟩
  w := fun _ => P.δ
  w_nonneg := fun _ => P.hδ.le
  δ := P.δ
  w_sum := by simp
  δ_pos := P.hδ
  δ_lt_one := P.hδ1

/-- The chain policy: `go` with probability `1/2` below depth `K`, `go` surely at depth `K`. -/
noncomputable def chainPol : Policy (Fin 2) Unit := fun n _ a =>
  if n < P.K then 1 / 2 else (if a = 1 then 1 else 0)

@[simp] theorem chain_T : (chain P).T = P.K + 1 := rfl
@[simp] theorem chain_r : (chain P).r = r P := rfl
@[simp] theorem chain_γ : (chain P).γ = 1 := rfl
@[simp] theorem chain_νa : (chain P).νa = νa P := rfl
@[simp] theorem chain_νe (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : (chain P).νe i n h a e = 1 := rfl
@[simp] theorem chain_w (i : Unit) : (chain P).w i = P.δ := rfl
@[simp] theorem chain_δ : (chain P).δ = P.δ := rfl

theorem nonterminal_iff (n : ℕ) (h : Hist (Fin 2) Unit n) : (chain P).nonterminal n h ↔ n ≤ P.K ∧ allGo n h := by
  unfold Model.nonterminal
  show n < P.K + 1 ∧ alive P n h = true ↔ _
  rw [alive_iff]
  constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩

theorem nt_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).nonterminal n (goH n) :=
  (nonterminal_iff P n _).2 ⟨hn, allGo_goH n⟩

theorem not_nt_ext_zero (n : ℕ) (e : Unit) : ¬ (chain P).nonterminal (n + 1) (ext (goH n) 0 e) := fun h =>
  not_allGo_ext_zero _ e ((nonterminal_iff P _ _).1 h).2

theorem not_nt_goH_succ_K : ¬ (chain P).nonterminal (P.K + 1) (goH (P.K + 1)) := fun h => by
  have := ((nonterminal_iff P _ _).1 h).1; omega

theorem eq_goH_of_nonterminal {n : ℕ} {h : Hist (Fin 2) Unit n} (hnt : (chain P).nonterminal n h) :
    h = goH n := eq_goH_of_allGo ((nonterminal_iff P n h).1 hnt).2

theorem chainPol_isPolicy : (chain P).IsPolicy (chainPol P) := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · unfold chainPol; split_ifs <;> norm_num
  · unfold chainPol; split_ifs <;> simp [Fin.sum_univ_two]

theorem xie_eq_one (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : (chain P).xie n h a e = 1 :=
  (chain P).xie_eq_one_of_unique n h a e

/-- Downward induction from depth `K`. -/
theorem downward {Q : ℕ → Prop} (hK : Q P.K) (hstep : ∀ n, n < P.K → Q (n + 1) → Q n) : ∀ n, n ≤ P.K → Q n := by
  have key : ∀ d n, n + d = P.K → Q n := by
    intro d
    induction d with
    | zero => intro n hn; have : n = P.K := by omega
              rw [this]; exact hK
    | succ d ih => intro n hn; exact hstep n (by omega) (ih (n + 1) (by omega))
  intro n hn
  exact key (P.K - n) n (by omega)

/-! ### Joints along the chain -/

theorem nuJoint_goH : ∀ n, n ≤ P.K → (chain P).nuJoint () n (goH n) = 1 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [← goH_ext n (), Model.nuJoint_ext, ih (by omega)]
    simp [νa, show n < P.K by omega]

theorem nuJoint_goH_succ_K : (chain P).nuJoint () (P.K + 1) (goH (P.K + 1)) = 0 := by
  rw [← goH_ext P.K (), Model.nuJoint_ext, nuJoint_goH P _ le_rfl]
  simp [νa]

theorem xins_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).xins n (goH n) = P.δ := by
  simp [Model.xins, nuJoint_goH P n hn]

theorem xins_goH_succ_K : (chain P).xins (P.K + 1) (goH (P.K + 1)) = 0 := by
  simp [Model.xins, nuJoint_goH_succ_K]

theorem xinsA_goH_zero {n : ℕ} (hn : n ≤ P.K) : (chain P).xinsA n (goH n) 0 = if n < P.K then 0 else P.δ := by
  simp [Model.xinsA, nuJoint_goH P n hn, νa]

theorem xiS_goH : ∀ n, n ≤ P.K → (chain P).xiS (chainPol P) n (goH n) = (1 / 2) ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [← goH_ext n (), Model.xiS_ext, ih (by omega), xie_eq_one, pow_succ]
    simp [chainPol, show n < P.K by omega]

theorem xi_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).xi (chainPol P) n (goH n) = (1 - P.δ) * (1 / 2) ^ n + P.δ := by
  unfold Model.xi
  rw [xiS_goH P n hn, xins_goH P hn, chain_δ]

theorem xi_goH_pos {n : ℕ} (hn : n ≤ P.K) : 0 < (chain P).xi (chainPol P) n (goH n) := by
  rw [xi_goH P hn]
  have := P.hδ; have := P.hδ1
  have : (0:ℝ) < (1 / 2) ^ n := by positivity
  nlinarith

/-- `w_{h_n} = r_n` (the self-odds double at each mixing step).
Source: [[sequential-self-game]] §4.3
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem wS_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).wS (chainPol P) n (goH n) = rk P n := by
  rw [Model.wS_of_xi_ne_zero _ (xi_goH_pos P hn).ne', xi_goH P hn, xiS_goH P n hn, chain_δ]
  unfold rk O0
  have := P.hδ; have := P.hδ1
  have h1 : (0:ℝ) < 1 - P.δ := by linarith
  have h2 : (0:ℝ) < (1 / 2) ^ n := by positivity
  have h3 : ((1:ℝ) / 2) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  field_simp
  nlinarith [h3]

theorem odds_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).odds (chainPol P) n (goH n) = O0 P * 2 ^ n := by
  unfold Model.odds
  rw [wS_goH P hn, one_sub_rk]
  unfold rk
  have := O0_pos P
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  field_simp

/-! ### Values along the chain -/

theorem Vnu_goH_succ_K : (chain P).Vnu () (P.K + 1) (goH (P.K + 1)) = 0 :=
  (chain P).Vnu_of_not_nonterminal () (not_nt_goH_succ_K P)
theorem Vstar_goH_succ_K : (chain P).Vstar (P.K + 1) (goH (P.K + 1)) = 0 :=
  (chain P).Vstar_of_not_nonterminal (not_nt_goH_succ_K P)
theorem Vpi_goH_succ_K : (chain P).Vpi (chainPol P) (P.K + 1) (goH (P.K + 1)) = 0 :=
  (chain P).Vpi_of_not_nonterminal (not_nt_goH_succ_K P)
theorem Vxi_goH_succ_K : (chain P).Vxi (chainPol P) (P.K + 1) (goH (P.K + 1)) = 0 :=
  (chain P).Vxi_of_not_nonterminal (not_nt_goH_succ_K P)

/-- The residual's own value along the chain is `0`. -/
theorem Vnu_goH : ∀ n, n ≤ P.K → (chain P).Vnu () n (goH n) = 0 := by
  refine downward P ?_ ?_
  · rw [(chain P).Vnu_eq () (nt_goH P le_rfl), Fin.sum_univ_two,
      (chain P).Qnu_eq_of_children_terminal () (goH P.K) 0 (fun e => not_nt_ext_zero P P.K e)]
    simp [νa, r_ext_zero]
  · intro n hn ih
    rw [(chain P).Vnu_eq () (nt_goH P hn.le), Fin.sum_univ_two, Model.Qnu_eq_sum, Model.Qnu_eq_sum]
    simp [νa, hn, goH_ext, r_goH_succ, show n ≠ P.K by omega, ih]

theorem Vstar_goH : ∀ n, n ≤ P.K → (chain P).Vstar n (goH n) = 1 := by
  refine downward P ?_ ?_
  · rw [(chain P).Vstar_fin_two (nt_goH P le_rfl),
      (chain P).Qstar_eq_of_children_terminal (goH P.K) 0 (fun e => not_nt_ext_zero P P.K e), Model.Qstar_eq_sum]
    simp [xie_eq_one, r_ext_zero, goH_ext, r_goH_succ, Vstar_goH_succ_K]
  · intro n hn ih
    rw [(chain P).Vstar_fin_two (nt_goH P hn.le),
      (chain P).Qstar_eq_of_children_terminal (goH n) 0 (fun e => not_nt_ext_zero P n e), Model.Qstar_eq_sum]
    simp [xie_eq_one, r_ext_zero, goH_ext, r_goH_succ, hn, show n ≠ P.K by omega, ih]
    exact rk_le_one P n

theorem Qstar_goH_zero {n : ℕ} (hn : n ≤ P.K) : (chain P).Qstar n (goH n) 0 = if n < P.K then rk P n else 0 := by
  rw [(chain P).Qstar_eq_of_children_terminal (goH n) 0 (fun e => not_nt_ext_zero P n e)]
  simp [xie_eq_one, r_ext_zero]

/-- `π⋆(h_n) = go`. -/
theorem piStar_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).piStar n (goH n) = 1 := by
  refine (chain P).piStar_eq_of_unique (nt_goH P hn) (Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => rfl⟩)
  rw [Qstar_goH_zero P hn, Vstar_goH P n hn] at ha
  split_ifs at ha
  · exact absurd ha (rk_lt_one P n).ne
  · exact absurd ha zero_ne_one

/-- The loss `ε(h_n) = ∑_{k<K-n} 2^{-(k+1)} (1 - r_{n+k})`. -/
noncomputable def epsC (n : ℕ) : ℝ := ∑ k ∈ range (P.K - n), (1 / 2) ^ (k + 1) * (1 - rk P (n + k))

theorem epsC_K : epsC P P.K = 0 := by simp [epsC]

theorem epsC_succ {n : ℕ} (hn : n < P.K) : epsC P n = 1 / 2 * (1 - rk P n) + 1 / 2 * epsC P (n + 1) := by
  unfold epsC
  have : P.K - n = (P.K - (n + 1)) + 1 := by omega
  rw [this, sum_range_succ', Finset.mul_sum, add_comm]
  simp only [zero_add, add_zero, pow_one]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show n + (k + 1) = n + 1 + k by ring, pow_succ]
  ring

theorem epsC_nonneg (n : ℕ) : 0 ≤ epsC P n :=
  sum_nonneg fun k _ => mul_nonneg (by positivity) (by linarith [rk_le_one P (n + k)])

theorem Vpi_goH : ∀ n, n ≤ P.K → (chain P).Vpi (chainPol P) n (goH n) = 1 - epsC P n := by
  refine downward P ?_ ?_
  · rw [epsC_K, sub_zero, (chain P).Vpi_eq (nt_goH P le_rfl), Fin.sum_univ_two, Model.Qpi_eq_sum, Model.Qpi_eq_sum]
    simp [chainPol, xie_eq_one, goH_ext, r_goH_succ, Vpi_goH_succ_K]
  · intro n hn ih
    rw [epsC_succ P hn, (chain P).Vpi_eq (nt_goH P hn.le), Fin.sum_univ_two,
      (chain P).Qpi_eq_of_children_terminal (goH n) 0 (fun e => not_nt_ext_zero P n e), Model.Qpi_eq_sum]
    simp [chainPol, xie_eq_one, r_ext_zero, goH_ext, r_goH_succ, hn, show n ≠ P.K by omega, ih]
    ring

theorem gap_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).gap (chainPol P) n (goH n) = epsC P n := by
  unfold Model.gap
  rw [Vstar_goH P n hn, Vpi_goH P n hn]
  ring

/-- `V_ξ(h_n) = w_{h_n} V^π(h_n)` (the residual contributes no value).
Source: [[sequential-self-game]] §4.3 ("Why")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Vxi_goH {n : ℕ} (hn : n ≤ P.K) : (chain P).Vxi (chainPol P) n (goH n) = rk P n * (1 - epsC P n) := by
  have hmix := (chain P).xi_mul_Vxi (chainPol_isPolicy P) n (goH n)
  rw [Fintype.sum_unique, Vnu_goH P n hn, mul_zero, add_zero, Vpi_goH P n hn] at hmix
  have hx := xi_goH_pos P hn
  have hw := wS_goH P hn
  rw [Model.wS_of_xi_ne_zero _ hx.ne'] at hw
  rw [← hw]
  field_simp
  linarith [hmix]

theorem Qxi_goH_zero {n : ℕ} (hn : n ≤ P.K) :
    (chain P).Qxi (chainPol P) n (goH n) 0 = if n < P.K then rk P n else 0 := by
  rw [(chain P).Qxi_eq_of_children_terminal (goH n) 0 (fun e => not_nt_ext_zero P n e)]
  simp [xie_eq_one, r_ext_zero]

theorem Qxi_goH_one_lt {n : ℕ} (hn : n < P.K) :
    (chain P).Qxi (chainPol P) n (goH n) 1 = rk P (n + 1) * (1 - epsC P (n + 1)) := by
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, goH_ext, Vxi_goH P (by omega)]
  simp [xie_eq_one, r_goH_succ, show n ≠ P.K by omega]

theorem Qxi_goH_one_K : (chain P).Qxi (chainPol P) P.K (goH P.K) 1 = 1 := by
  rw [Model.Qxi_eq_sum, Fintype.sum_unique, goH_ext, Vxi_goH_succ_K]
  simp [xie_eq_one, r_goH_succ]

/-- `M(h_n) = r_n` for `n < K`: `go` is strictly worse than `out` there. -/
theorem Mx_goH_lt {n : ℕ} (hn : n < P.K) : (chain P).Mx (chainPol P) n (goH n) = rk P n ∧
    (chain P).Qxi (chainPol P) n (goH n) 1 < rk P n := by
  have h1 := Qxi_goH_one_lt P hn
  have hlt : (chain P).Qxi (chainPol P) n (goH n) 1 < rk P n := by
    rw [h1]
    have := rk_succ_lt P n
    have := rk_pos P (n + 1)
    have := epsC_nonneg P (n + 1)
    nlinarith
  refine ⟨?_, hlt⟩
  rw [(chain P).Mx_fin_two, Qxi_goH_zero P hn.le, if_pos hn]
  exact max_eq_left hlt.le

theorem Mx_goH_K : (chain P).Mx (chainPol P) P.K (goH P.K) = 1 := by
  rw [(chain P).Mx_fin_two, Qxi_goH_zero P le_rfl, Qxi_goH_one_K, if_neg (lt_irrefl _)]
  norm_num

/-- `h_n` (`n < K`) is an **equality node**: `r_{h_n} = 0`; `h_K` is a strict-argmax node: `r_{h_K} > 0`.
Source: [[sequential-self-game]] §4.3
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem resid_goH {n : ℕ} (hn : n ≤ P.K) :
    (chain P).resid (chainPol P) n (goH n) = if n < P.K then 0 else 1 - rk P P.K := by
  unfold Model.resid
  rw [wS_goH P hn, Vstar_goH P n hn, mul_one]
  split_ifs with h
  · rw [(Mx_goH_lt P h).1, sub_self]
  · have : n = P.K := by omega
    subst this
    rw [Mx_goH_K]

/-- **The chain policy is a floored fixed point** (every `K`, every `δ`).
Source: [[sequential-self-game]] §4.3 (Claim)
Kind: P
Fidelity: exact (general `K`, `δ`; the note checks seven pairs)
Hyps: (a) -/
theorem chainPol_isFlooredFP : (chain P).IsFlooredFP (chainPol P) := by
  refine ⟨chainPol_isPolicy P, fun n h hnt => ?_⟩
  have hn : n ≤ P.K := ((nonterminal_iff P n h).1 hnt).1
  rw [eq_goH_of_nonterminal P hnt]
  rw [resid_goH P hn]
  split_ifs with h
  · refine ⟨fun h0 => absurd h0 (lt_irrefl 0), fun h0 => absurd h0 (lt_irrefl 0),
      fun _ => Fin.forall_fin_two.2 ⟨fun _ => Or.inl ?_, fun _ => Or.inr ?_⟩⟩
    · rw [(Mx_goH_lt P h).1, Qxi_goH_zero P hn, if_pos h]
    · exact (piStar_goH P hn).symm
  · have hK : n = P.K := by omega
    subst hK
    have hpos : 0 < 1 - rk P P.K := by linarith [rk_lt_one P P.K]
    refine ⟨fun h0 => absurd h0 (not_lt.2 hpos.le), fun _ => Fin.forall_fin_two.2 ⟨fun ha => ?_, fun _ => ?_⟩,
      fun h0 => absurd h0 hpos.ne'⟩
    · simp [chainPol] at ha
    · rw [Mx_goH_K, Qxi_goH_one_K]

/-- **The chain policy is not a plain fixed point** (`K ≥ 1`): at `h₀` it plays `go` with positive probability
while `𝒜_{h₀} = {out}`.
Source: [[sequential-self-game]] §4.3 ("and not of the plain agent")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem chainPol_not_isPlainFP (hK : 1 ≤ P.K) : ¬ (chain P).IsPlainFP (chainPol P) := by
  rintro ⟨_, hfp⟩
  have h0 : (0:ℕ) < P.K := hK
  have := hfp 0 (goH 0) (nt_goH P (Nat.zero_le _)) 1 (by simp [chainPol, h0])
  rw [(Mx_goH_lt P h0).1] at this
  exact absurd this (Mx_goH_lt P h0).2.ne

/-- **The exact loss**: `ε(h₀) = (O₀/2) ∑_{k<K} 1/(1 + O₀ 2^k)`.
Source: [[sequential-self-game]] §4.3 (Claim, the closed form)
Kind: P
Fidelity: exact (general `K`, `δ`)
Hyps: (a) -/
theorem gap_root : (chain P).gap (chainPol P) 0 (goH 0) = O0 P / 2 * ∑ k ∈ range P.K, 1 / (1 + O0 P * 2 ^ k) := by
  rw [gap_goH P (Nat.zero_le _)]
  unfold epsC
  rw [Nat.sub_zero, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have := O0_pos P
  have h2 : (0:ℝ) < 2 ^ k := by positivity
  rw [zero_add, one_sub_rk, one_div_pow, div_mul_div_comm, one_mul, mul_one_div, div_div,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem wS_root_pos : 0 < (chain P).wS (chainPol P) 0 (goH 0) := by
  rw [wS_goH P (Nat.zero_le _)]; exact rk_pos P 0

theorem odds_root : (chain P).odds (chainPol P) 0 (goH 0) = O0 P := by
  rw [odds_goH P (Nat.zero_le _)]; simp

/-! ### The refutation of "`C · O_h`, horizon-free" -/

/-- The chain with `δ = 2^{-m}`, `K = m`. -/
noncomputable def dyadic (m : ℕ) (hm : 1 ≤ m) : CP :=
  ⟨m, (1 / 2) ^ m, by positivity, by
    calc ((1:ℝ) / 2) ^ m ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ < 1 := by norm_num⟩

theorem dyadic_O0 (m : ℕ) (hm : 1 ≤ m) : O0 (dyadic m hm) = 1 / (2 ^ m - 1) := by
  show ((1:ℝ) / 2) ^ m / (1 - (1 / 2) ^ m) = 1 / (2 ^ m - 1)
  have h : (1:ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) (by omega)
  rw [one_div_pow]
  have h1 : (0:ℝ) < 2 ^ m - 1 := by linarith
  have hne : (0:ℝ) < 1 - 1 / 2 ^ m := by rw [sub_pos, div_lt_one (by positivity)]; exact h
  rw [div_eq_div_iff hne.ne' h1.ne', one_mul, mul_sub, one_div_mul_cancel (by positivity : (2:ℝ) ^ m ≠ 0), mul_one]

/-- `O₀ 2^k < 1` for the dyadic chain with `k < m`, `m ≥ 2`. -/
theorem dyadic_O0_mul_pow_lt (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k < m) :
    O0 (dyadic m (by omega)) * 2 ^ k < 1 := by
  show ((1:ℝ) / 2) ^ m / (1 - (1 / 2) ^ m) * 2 ^ k < 1
  have hpm : ((1:ℝ) / 2) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  have hp : (0:ℝ) < (1 / 2) ^ m := by positivity
  have h4 : (4:ℝ) ≤ 2 ^ m := by
    calc (4:ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hk' : (2:ℝ) ^ k * 2 ≤ 2 ^ m := by rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hk
  have hpos : (0:ℝ) < 1 - (1 / 2) ^ m := by nlinarith
  rw [div_mul_eq_mul_div, div_lt_one hpos]
  have h5 : (2:ℝ) ^ k + 1 < 2 ^ m := by linarith
  nlinarith [mul_lt_mul_of_pos_left h5 hp, hpm]

/-- Each term of the chain sum exceeds `1/2` when `δ = 2^{-m}`, `K = m ≥ 2`, `k < m`. -/
theorem dyadic_term_gt (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k < m) :
    1 / 2 < 1 / (1 + O0 (dyadic m (by omega)) * 2 ^ k) := by
  have := dyadic_O0_mul_pow_lt m hm k hk
  have hx : (0:ℝ) < 1 + O0 (dyadic m (by omega)) * 2 ^ k := by
    have := O0_pos (dyadic m (by omega)); positivity
  exact one_div_lt_one_div_of_lt hx (by linarith)

/-- **The dyadic chain's `gap/bound` bracket** (`δ = 2^{-m}`, `K = m ≥ 2`; `bound := O_{h₀}(1 + T) = O₀(m + 2)`
is Theorem C's bound at the root): `m/(4(m+2)) · bound < gap < m/(2(m+2)) · bound`, because each of the `m`
terms of the chain sum lies in `(1/2, 1)`. So the ratio `gap/bound` lies in `(1/4, 1/2)` only from `m = 4` on
(round-2 audits: the ledger had claimed it from `m = 3`; see `dyadic3_ratio_lt_quarter`), and tends to `1/2`.
Source: [[sequential-self-game]] §4.3; round-2 audits (fidelity §3.1, adversarial 1)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem dyadic_ratio_bracket (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) / (4 * (m + 2)) *
        ((chain (dyadic m (by omega))).odds (chainPol (dyadic m (by omega))) 0 (goH 0) *
          (1 + ((chain (dyadic m (by omega))).T : ℝ))) <
      (chain (dyadic m (by omega))).gap (chainPol (dyadic m (by omega))) 0 (goH 0) ∧
    (chain (dyadic m (by omega))).gap (chainPol (dyadic m (by omega))) 0 (goH 0) <
      (m : ℝ) / (2 * (m + 2)) *
        ((chain (dyadic m (by omega))).odds (chainPol (dyadic m (by omega))) 0 (goH 0) *
          (1 + ((chain (dyadic m (by omega))).T : ℝ))) := by
  have hK : (dyadic m (by omega)).K = m := rfl
  rw [odds_root, gap_root, chain_T, hK]
  have hO := O0_pos (dyadic m (by omega))
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hlo : (m : ℝ) / 2 < ∑ k ∈ range m, 1 / (1 + O0 (dyadic m (by omega)) * 2 ^ k) := by
    have hterm : ∀ k ∈ range m, (1:ℝ) / 2 < 1 / (1 + O0 (dyadic m (by omega)) * 2 ^ k) := fun k hk =>
      dyadic_term_gt m hm k (mem_range.1 hk)
    have := sum_lt_sum_of_nonempty (nonempty_range_iff.2 (by omega)) hterm
    rw [sum_const, card_range, nsmul_eq_mul] at this
    linarith
  have hhi : ∑ k ∈ range m, 1 / (1 + O0 (dyadic m (by omega)) * 2 ^ k) < m := by
    have hterm : ∀ k ∈ range m, 1 / (1 + O0 (dyadic m (by omega)) * 2 ^ k) < (1:ℝ) := fun k _ => by
      rw [div_lt_one (by positivity)]
      have : (0:ℝ) < O0 (dyadic m (by omega)) * 2 ^ k := by positivity
      linarith
    have := sum_lt_sum_of_nonempty (nonempty_range_iff.2 (by omega)) hterm
    rw [sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this
  constructor
  · have e : (m : ℝ) / (4 * (m + 2)) * (O0 (dyadic m (by omega)) * (1 + ((m + 1 : ℕ) : ℝ))) =
        O0 (dyadic m (by omega)) / 2 * ((m : ℝ) / 2) := by
      push_cast; field_simp; ring
    rw [e]
    exact mul_lt_mul_of_pos_left hlo (by positivity)
  · have e : (m : ℝ) / (2 * (m + 2)) * (O0 (dyadic m (by omega)) * (1 + ((m + 1 : ℕ) : ℝ))) =
        O0 (dyadic m (by omega)) / 2 * (m : ℝ) := by
      push_cast; field_simp; ring
    rw [e]
    exact mul_lt_mul_of_pos_left hhi (by positivity)

/-- `m = 4` (`δ = 1/16`, `K = 4`, `T = 5`): Theorem C's bound at the root is `O₀ (1 + T) = 2/5 < 1`. (Round-2
adversarial audit's probe `probe_dyadic4_bound`, moved into the library.)
Source: [[sequential-self-game]] §4.3; round-2 adversarial audit, item 1
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem dyadic4_bound :
    (chain (dyadic 4 (by norm_num))).odds (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) *
      (1 + ((chain (dyadic 4 (by norm_num))).T : ℝ)) = 2 / 5 := by
  rw [odds_root, dyadic_O0, chain_T]
  have hK : (dyadic 4 (by norm_num)).K = 4 := rfl
  rw [hK]
  norm_num

/-- `m = 4`: the exact gap at the root is `25845/237728 ≈ 0.109`, positive and below the bound `2/5`. (Round-2
adversarial audit's probe `probe_dyadic4_gap`, moved into the library.)
Source: [[sequential-self-game]] §4.3; round-2 adversarial audit, item 1
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem dyadic4_gap :
    (chain (dyadic 4 (by norm_num))).gap (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) = 25845 / 237728 := by
  rw [gap_root, dyadic_O0]
  have hK : (dyadic 4 (by norm_num)).K = 4 := rfl
  rw [hK]
  norm_num [Finset.sum_range_succ]

/-- **Theorem C's chain witness is informative, machine-checked** (`m = 4`): the dyadic chain inhabits Theorem C's
full package (`IsFlooredFP`, decision node, `0 < w`) with `0 < gap = 25845/237728 < 2/5 = O_h(1+T) < 1` — the
N+ grade of `chainPol_isFlooredFP` no longer rests on prose arithmetic. (Round-2 adversarial audit's probe
`probe_dyadic4_informative`, moved into the library.)
Source: [[sequential-self-game]] §4.3; round-2 adversarial audit, item 1
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem dyadic4_informative :
    (chain (dyadic 4 (by norm_num))).IsFlooredFP (chainPol (dyadic 4 (by norm_num))) ∧
    (chain (dyadic 4 (by norm_num))).nonterminal 0 (goH 0) ∧
    0 < (chain (dyadic 4 (by norm_num))).wS (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) ∧
    0 < (chain (dyadic 4 (by norm_num))).gap (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) ∧
    (chain (dyadic 4 (by norm_num))).gap (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) <
      (chain (dyadic 4 (by norm_num))).odds (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) *
        (1 + ((chain (dyadic 4 (by norm_num))).T : ℝ)) ∧
    (chain (dyadic 4 (by norm_num))).odds (chainPol (dyadic 4 (by norm_num))) 0 (goH 0) *
        (1 + ((chain (dyadic 4 (by norm_num))).T : ℝ)) < 1 := by
  refine ⟨chainPol_isFlooredFP _, nt_goH _ (Nat.zero_le _), wS_root_pos _, ?_, ?_, ?_⟩
  · rw [dyadic4_gap]; norm_num
  · rw [dyadic4_gap, dyadic4_bound]; norm_num
  · rw [dyadic4_bound]; norm_num

/-- `m = 3` (`δ = 1/8`, `K = 3`, `T = 4`): bound `5/7 < 1` (the witness is already informative at `m = 3`), but
`gap = 259/1584` and `gap < bound / 4`: the ratio `gap/bound` is below `1/4` at `m = 3` (`≈ 0.229`). (Round-2
adversarial audit's probe `probe_dyadic3_ratio_below_quarter`, moved into the library.)
Source: [[sequential-self-game]] §4.3; round-2 audits (fidelity §3.1, adversarial 1)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem dyadic3_ratio_lt_quarter :
    (chain (dyadic 3 (by norm_num))).odds (chainPol (dyadic 3 (by norm_num))) 0 (goH 0) *
      (1 + ((chain (dyadic 3 (by norm_num))).T : ℝ)) = 5 / 7 ∧
    (chain (dyadic 3 (by norm_num))).gap (chainPol (dyadic 3 (by norm_num))) 0 (goH 0) = 259 / 1584 ∧
    (chain (dyadic 3 (by norm_num))).gap (chainPol (dyadic 3 (by norm_num))) 0 (goH 0) < (5 / 7) / 4 := by
  have hK : (dyadic 3 (by norm_num)).K = 3 := rfl
  have hb : (chain (dyadic 3 (by norm_num))).odds (chainPol (dyadic 3 (by norm_num))) 0 (goH 0) *
      (1 + ((chain (dyadic 3 (by norm_num))).T : ℝ)) = 5 / 7 := by
    rw [odds_root, dyadic_O0, chain_T, hK]; norm_num
  have hg : (chain (dyadic 3 (by norm_num))).gap (chainPol (dyadic 3 (by norm_num))) 0 (goH 0) = 259 / 1584 := by
    rw [gap_root, dyadic_O0, hK]; norm_num [Finset.sum_range_succ]
  exact ⟨hb, hg, by rw [hg]; norm_num⟩

/-- **Refutation of the horizon-free `C · O_h` bound** ([[00-founding-sketches]] §2): for every `C` there are a
model, a floored fixed point and a decision node with `0 < w_h` and `ε(h) > C · O_h`. (Take the dyadic chain
`δ = 2^{-m}`, `K = m` with `m > 4C`: each of the `m` terms exceeds `1/2`, so `ε(h₀)/O₀ > m/4`.)
Source: [[sequential-self-game]] §4.3, §4.2; [[uea-inventory]] 012
Kind: P
Fidelity: exact (finite shadow)
Hyps: (a) -/
theorem no_horizon_free_bound (C : ℝ) :
    ∃ (M : Model (Fin 2) Unit Unit) (π : Policy (Fin 2) Unit) (n : ℕ) (h : Hist (Fin 2) Unit n),
      M.IsFlooredFP π ∧ M.nonterminal n h ∧ 0 < M.wS π n h ∧ C * M.odds π n h < M.gap π n h := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, max 2 (4 * C + 1) ≤ m := exists_nat_ge _
  have hm2 : 2 ≤ m := by
    have := le_trans (le_max_left 2 (4 * C + 1)) hm
    exact_mod_cast this
  have hmC : 4 * C + 1 ≤ m := le_trans (le_max_right _ _) hm
  set P := dyadic m (by omega) with hP
  refine ⟨chain P, chainPol P, 0, goH 0, chainPol_isFlooredFP P, nt_goH P (Nat.zero_le _), wS_root_pos P, ?_⟩
  have hK : P.K = m := rfl
  rw [odds_root, gap_root, hK]
  have hO := O0_pos P
  have hsum : (m : ℝ) / 2 < ∑ k ∈ range m, 1 / (1 + O0 P * 2 ^ k) := by
    have hterm : ∀ k ∈ range m, (1:ℝ) / 2 < 1 / (1 + O0 P * 2 ^ k) := fun k hk =>
      dyadic_term_gt m hm2 k (mem_range.1 hk)
    have := sum_lt_sum_of_nonempty (nonempty_range_iff.2 (by omega)) hterm
    rw [sum_const, card_range, nsmul_eq_mul] at this
    linarith
  calc C * O0 P = O0 P / 2 * (2 * C) := by ring
    _ < O0 P / 2 * ((m : ℝ) / 2) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        linarith
    _ < O0 P / 2 * ∑ k ∈ range m, 1 / (1 + O0 P * 2 ^ k) := by
        apply mul_lt_mul_of_pos_left hsum (by positivity)

end Chain

end Cleanroom.Uea.UeaColeShadow
