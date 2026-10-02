import Cleanroom.Uea.UeaColeShadow.Chain
import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# D2: the trap chain for every `K`, `δ`, `δ'`; no horizon-free `δ` at `γ = 1`

The trap chain `TrapChain.model P` (`T = K + 1`, `γ = 1`, deterministic percepts): along the all-`go`
history `h_k` (`k ≤ K`), action `0` is `stay` (terminal, reward `c_k := (1-δ')^(K-k)`) for `k < K` and
`swim` (reward `1 = c_K`) at `h_K`; action `1` is `go` (`k < K`) or `sink` (reward `0`) at `h_K`. One
residual of weight `δ` plays action `1` everywhere; `0 < δ' < δ < 1`. **Theorem D2**: the plain fixed
points are exactly the policies that play `0` at every `h_k` — uniqueness among **all** policies, pure or
mixed (the source verified pure only), with strict preference at every node — and every fixed point has
root loss exactly `1 - (1-δ')^K`, `w_{h₀} = 1 - δ`, `V^*(h₀) = 1`. Cole's premise holds at the one node the
fixed point reaches (`h₀`); below it the self-posterior is `0`. Hence (target 9(−)) for every `δ ∈ (0,1)` and
every `ε < 1` there is a chain (`δ' = 9δ/10`, `K` large) on which every plain fixed point has root loss
`> ε` with `w_{h₀} = 1 - δ`: no horizon-free `δ(ε)` exists at `γ = 1`.

The names carry `TrapChain`; `Chain.chain` of `uea-cole-shadow` is Theorem C's equality-node chain, a
different instance (its `allGo`/`goH` combinatorics is reused here).

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.TrapChain`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow
open Cleanroom.Uea.UeaColeShadow.Chain (allGo goH allGo_goH goH_ext eq_goH_of_allGo allGo_ext_iff not_allGo_ext_zero)

namespace TrapChain

/-- Parameters of a trap chain: depth `K`, residual prior `δ`, reward decay `δ'`, with `0 < δ' < δ < 1`.
Source: `theorem1_search.py` `chain_trap`; [[uea-2-inventory]] 2-011
Kind: D
Fidelity: exact
Hyps: n/a -/
structure TP where
  K : ℕ
  δ : ℝ
  δ' : ℝ
  hδ' : 0 < δ'
  hlt : δ' < δ
  hδ1 : δ < 1

variable (P : TP)

theorem hδ : 0 < P.δ := lt_trans P.hδ' P.hlt
theorem one_sub_δ'_pos : 0 < 1 - P.δ' := by linarith [P.hlt, P.hδ1]
theorem one_sub_δ_pos : 0 < 1 - P.δ := by linarith [P.hδ1]

/-- `c_k := (1-δ')^(K-k)` (so `c_K = 1`). -/
noncomputable def ck (k : ℕ) : ℝ := (1 - P.δ') ^ (P.K - k)

theorem ck_pos (k : ℕ) : 0 < ck P k := pow_pos (one_sub_δ'_pos P) _
theorem ck_le_one (k : ℕ) : ck P k ≤ 1 := pow_le_one₀ (one_sub_δ'_pos P).le (by linarith [P.hδ'])
theorem ck_K : ck P P.K = 1 := by simp [ck]
theorem ck_succ {k : ℕ} (hk : k < P.K) : ck P k = (1 - P.δ') * ck P (k + 1) := by
  unfold ck
  have : P.K - k = (P.K - (k + 1)) + 1 := by omega
  rw [this, pow_succ, mul_comm]

/-- Alive nodes: the all-`go` histories of depth `≤ K`. -/
def alive (n : ℕ) (h : Hist (Fin 2) Unit n) : Bool := decide (n ≤ P.K ∧ allGo n h)

theorem alive_iff (n : ℕ) (h : Hist (Fin 2) Unit n) : alive P n h = true ↔ n ≤ P.K ∧ allGo n h := by
  simp [alive]

theorem alive_init (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) (hh : alive P (n + 1) h = true) :
    alive P n (Fin.init h) = true := by
  rw [alive_iff] at hh ⊢
  refine ⟨by omega, fun i => ?_⟩
  simpa [Fin.init] using hh.2 (Fin.castSucc i)

/-- Rewards on arrival: `c_n` for action `0` at `h_n` (`n ≤ K`), `0` otherwise. -/
noncomputable def r (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : ℝ :=
  if allGo n (Fin.init h) ∧ (h (Fin.last n)).1 = 0 ∧ n ≤ P.K then ck P n else 0

theorem r_nonneg (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : 0 ≤ r P n h := by
  unfold r; split_ifs
  · exact (ck_pos P n).le
  · exact le_rfl

theorem r_le_one (n : ℕ) (h : Hist (Fin 2) Unit (n + 1)) : r P n h ≤ 1 := by
  unfold r; split_ifs
  · exact ck_le_one P n
  · exact zero_le_one

theorem r_stay {n : ℕ} (hn : n ≤ P.K) (e : Unit) : r P n (ext (goH n) 0 e) = ck P n := by
  simp [r, allGo_goH, hn]

theorem r_go (n : ℕ) (e : Unit) : r P n (ext (goH n) 1 e) = 0 := by
  simp [r]

theorem r_eq_zero_of_not_allGo {n : ℕ} (h : Hist (Fin 2) Unit (n + 1)) (hg : ¬ allGo n (Fin.init h)) :
    r P n h = 0 := by
  simp [r, hg]

/-- Path returns: `0` along an all-`go` prefix, at most `1` everywhere. -/
theorem pathReturn_bounds : ∀ (n : ℕ) (h : Hist (Fin 2) Unit n),
    pathReturnOf 1 (r P) n h ≤ 1 ∧ (allGo n h → pathReturnOf 1 (r P) n h = 0) := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    obtain ⟨ih1, ih2⟩ := ih (Fin.init h)
    simp only [pathReturnOf, one_pow, one_mul]
    by_cases hg : allGo n (Fin.init h)
    · rw [ih2 hg, zero_add]
      refine ⟨r_le_one P n h, fun hga => ?_⟩
      have hlast : (h (Fin.last n)).1 = 1 := hga (Fin.last n)
      unfold r
      simp [hlast]
    · rw [r_eq_zero_of_not_allGo P h hg, add_zero]
      refine ⟨ih1, fun hga => absurd (fun i => by simpa [Fin.init] using hga (Fin.castSucc i)) hg⟩

theorem norm (n : ℕ) (_ : n ≤ P.K + 1) (h : Hist (Fin 2) Unit n) : pathReturnOf 1 (r P) n h ≤ 1 :=
  (pathReturn_bounds P n h).1

/-- **The trap chain** `model P`: `T = K + 1`, `γ = 1`, one residual of weight `δ` playing action `1`
(`go`, then `sink`) everywhere.
Source: `theorem1_search.py` `chain_trap`; [[uea-2-inventory]] 2-011; `InstB.model` is the case `K = 1` up to the reaudit's numbers
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def model : Model (Fin 2) Unit Unit where
  T := P.K + 1
  alive := alive P
  alive_init := alive_init P
  r := r P
  r_nonneg := r_nonneg P
  γ := 1
  γ_pos := one_pos
  γ_le_one := le_rfl
  norm := norm P
  νa := fun _ _ _ a => if a = 1 then 1 else 0
  νe := fun _ _ _ _ _ => 1
  νa_mem := fun _ _ _ => ⟨fun a => by show (0:ℝ) ≤ if a = 1 then 1 else 0; split_ifs <;> norm_num, by simp⟩
  νe_mem := fun _ _ _ _ => ⟨fun _ => zero_le_one, by simp⟩
  w := fun _ => P.δ
  w_nonneg := fun _ => (hδ P).le
  δ := P.δ
  w_sum := by simp
  δ_pos := hδ P
  δ_lt_one := P.hδ1

/-- The stay-everywhere policy (`stay` at `h_k`, `swim` at `h_K`): action `0` everywhere. -/
noncomputable def stayPol : Policy (Fin 2) Unit := fun _ _ a => if a = 0 then 1 else 0

@[simp] theorem model_T : (model P).T = P.K + 1 := rfl
@[simp] theorem model_r : (model P).r = r P := rfl
@[simp] theorem model_γ : (model P).γ = 1 := rfl
@[simp] theorem model_νa (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) :
    (model P).νa i n h a = if a = 1 then 1 else 0 := rfl
@[simp] theorem model_νe (i : Unit) (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) :
    (model P).νe i n h a e = 1 := rfl
@[simp] theorem model_w (i : Unit) : (model P).w i = P.δ := rfl
@[simp] theorem model_δ : (model P).δ = P.δ := rfl

theorem nonterminal_iff (n : ℕ) (h : Hist (Fin 2) Unit n) :
    (model P).nonterminal n h ↔ n ≤ P.K ∧ allGo n h := by
  unfold Model.nonterminal
  show n < P.K + 1 ∧ alive P n h = true ↔ _
  rw [alive_iff]
  constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩

theorem nt_goH {n : ℕ} (hn : n ≤ P.K) : (model P).nonterminal n (goH n) :=
  (nonterminal_iff P n _).2 ⟨hn, allGo_goH n⟩

theorem not_nt_ext_zero (n : ℕ) (e : Unit) : ¬ (model P).nonterminal (n + 1) (ext (goH n) 0 e) := fun h =>
  not_allGo_ext_zero _ e ((nonterminal_iff P _ _).1 h).2

theorem not_nt_succ_K (h : Hist (Fin 2) Unit (P.K + 1)) : ¬ (model P).nonterminal (P.K + 1) h := fun h' => by
  have := ((nonterminal_iff P _ _).1 h').1; omega

theorem eq_goH_of_nonterminal {n : ℕ} {h : Hist (Fin 2) Unit n} (hnt : (model P).nonterminal n h) :
    h = goH n := eq_goH_of_allGo ((nonterminal_iff P n h).1 hnt).2

theorem eq_goH_zero (h : Hist (Fin 2) Unit 0) : h = goH 0 := funext fun i => Fin.elim0 i

theorem stayPol_isPolicy : (model P).IsPolicy stayPol := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · unfold stayPol; split_ifs <;> norm_num
  · simp [stayPol]

theorem stayPol_isPure : (model P).IsPure stayPol := fun _ _ _ => ⟨0, by simp [stayPol]⟩

theorem xie_eq_one (n : ℕ) (h : Hist (Fin 2) Unit n) (a : Fin 2) (e : Unit) : (model P).xie n h a e = 1 :=
  (model P).xie_eq_one_of_unique n h a e

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

/-! ### The residual along the chain -/

theorem nuJoint_goH : ∀ n, (model P).nuJoint () n (goH n) = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← goH_ext n (), Model.nuJoint_ext, ih]
    simp

theorem xins_goH (n : ℕ) : (model P).xins n (goH n) = P.δ := by
  simp [Model.xins, nuJoint_goH P n]

theorem xinsA_goH_0 (n : ℕ) : (model P).xinsA n (goH n) 0 = 0 := by
  simp [Model.xinsA, nuJoint_goH P n]

theorem xinsA_goH_1 (n : ℕ) : (model P).xinsA n (goH n) 1 = P.δ := by
  simp [Model.xinsA, nuJoint_goH P n]

/-- The residual's own value along its path is `0` (it never collects a reward). -/
theorem Vnu_goH : ∀ n, (model P).Vnu () n (goH n) = 0 := by
  have key : ∀ d n, n + d = P.K + 1 → (model P).Vnu () n (goH n) = 0 := by
    intro d
    induction d with
    | zero =>
      intro n hn
      have : n = P.K + 1 := by omega
      subst this
      exact (model P).Vnu_of_not_nonterminal () (not_nt_succ_K P _)
    | succ d ih =>
      intro n hn
      have hnt := nt_goH P (show n ≤ P.K by omega)
      have h0 : (model P).νa () n (goH n) 0 = 0 := by simp
      have h1 : (model P).νa () n (goH n) 1 = 1 := by simp
      rw [(model P).Vnu_eq () hnt, Fin.sum_univ_two, h0, h1, zero_mul, zero_add, one_mul, Model.Qnu_eq_sum,
        Fintype.sum_unique, model_νe, one_mul, model_γ, one_pow, one_mul, model_r, r_go, goH_ext,
        ih (n + 1) (by omega)]
      ring
  intro n
  by_cases hn : n ≤ P.K + 1
  · exact key (P.K + 1 - n) n (by omega)
  · exact (model P).Vnu_of_not_nonterminal () (fun h => by have := ((nonterminal_iff P _ _).1 h).1; omega)

theorem Qnu_goH_1 (n : ℕ) : (model P).Qnu () n (goH n) 1 = 0 := by
  rw [Model.Qnu_eq_sum, Fintype.sum_unique, model_νe, one_mul, model_γ, one_pow, one_mul, model_r, r_go,
    goH_ext, Vnu_goH]
  ring

theorem Qmix_goH_1 (n : ℕ) : (model P).Qmix n (goH n) 1 = 0 := by
  unfold Model.Qmix
  rw [Fintype.sum_unique, Qnu_goH_1]
  simp

/-! ### Values along the chain -/

section Values
variable (π : Policy (Fin 2) Unit)

theorem Qxi_goH_0 {n : ℕ} (hn : n ≤ P.K) : (model P).Qxi π n (goH n) 0 = ck P n := by
  rw [(model P).Qxi_eq_of_children_terminal (goH n) 0 (fun e => not_nt_ext_zero P n e), Fintype.sum_unique,
    xie_eq_one, model_γ, one_pow, model_r, r_stay P hn]
  ring

theorem Qpi_goH_0 {n : ℕ} (hn : n ≤ P.K) : (model P).Qpi π n (goH n) 0 = ck P n := by
  rw [(model P).Qpi_eq_of_children_terminal (goH n) 0 (fun e => not_nt_ext_zero P n e), Fintype.sum_unique,
    xie_eq_one, model_γ, one_pow, model_r, r_stay P hn]
  ring

theorem Qstar_goH_0 {n : ℕ} (hn : n ≤ P.K) : (model P).Qstar n (goH n) 0 = ck P n := by
  rw [(model P).Qstar_eq_of_children_terminal (goH n) 0 (fun e => not_nt_ext_zero P n e), Fintype.sum_unique,
    xie_eq_one, model_γ, one_pow, model_r, r_stay P hn]
  ring

theorem Qxi_goH_K_1 : (model P).Qxi π P.K (goH P.K) 1 = 0 := by
  rw [(model P).Qxi_eq_of_children_terminal (goH P.K) 1 (fun e => not_nt_succ_K P _), Fintype.sum_unique,
    xie_eq_one, model_γ, one_pow, model_r, r_go]
  ring

theorem Qpi_goH_K_1 : (model P).Qpi π P.K (goH P.K) 1 = 0 := by
  rw [(model P).Qpi_eq_of_children_terminal (goH P.K) 1 (fun e => not_nt_succ_K P _), Fintype.sum_unique,
    xie_eq_one, model_γ, one_pow, model_r, r_go]
  ring

theorem Qstar_goH_K_1 : (model P).Qstar P.K (goH P.K) 1 = 0 := by
  rw [(model P).Qstar_eq_of_children_terminal (goH P.K) 1 (fun e => not_nt_succ_K P _), Fintype.sum_unique,
    xie_eq_one, model_γ, one_pow, model_r, r_go]
  ring

theorem Qpi_goH_1 (n : ℕ) : (model P).Qpi π n (goH n) 1 = (model P).Vpi π (n + 1) (goH (n + 1)) := by
  rw [Model.Qpi_eq_sum, Fintype.sum_unique, xie_eq_one, model_γ, one_pow, model_r, r_go, goH_ext]
  ring

theorem Qstar_goH_1 (n : ℕ) : (model P).Qstar n (goH n) 1 = (model P).Vstar (n + 1) (goH (n + 1)) := by
  rw [Model.Qstar_eq_sum, Fintype.sum_unique, xie_eq_one, model_γ, one_pow, model_r, r_go, goH_ext]
  ring

/-- `V^*(h_k) = 1` for every `k ≤ K`. -/
theorem Vstar_goH : ∀ n, n ≤ P.K → (model P).Vstar n (goH n) = 1 := by
  refine downward P ?_ ?_
  · rw [(model P).Vstar_fin_two (nt_goH P le_rfl), Qstar_goH_0 P le_rfl, Qstar_goH_K_1, ck_K]
    exact max_eq_left zero_le_one
  · intro n hn ih
    rw [(model P).Vstar_fin_two (nt_goH P hn.le), Qstar_goH_0 P hn.le, Qstar_goH_1, ih]
    exact max_eq_right (ck_le_one P n)

theorem xiS_goH_le_one (hπ : (model P).IsPolicy π) : ∀ n, n ≤ P.K → (model P).xiS π n (goH n) ≤ 1 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [← goH_ext n (), Model.xiS_ext, xie_eq_one, mul_one]
    have h1 := ih (by omega)
    have h2 := hπ.le_one (nt_goH P (show n ≤ P.K by omega)) 1
    have h4 := hπ.nonneg (nt_goH P (show n ≤ P.K by omega)) 1
    exact mul_le_one₀ h1 h4 h2

theorem xiA_goH_1 (n : ℕ) :
    (model P).xiA π n (goH n) 1 = (1 - P.δ) * (model P).xiS π n (goH n) * π n (goH n) 1 + P.δ := by
  rw [Model.xiA_eq, xinsA_goH_1, model_δ]

/-- `w_{h_k go} ≤ 1 - δ`: the self-mass after `go` is at most `(1-δ)` against the residual's `δ`. -/
theorem wA_goH_1_le (hπ : (model P).IsPolicy π) {n : ℕ} (hn : n ≤ P.K) :
    (model P).wA π n (goH n) 1 ≤ 1 - P.δ := by
  have hδ := hδ P
  have h1δ := one_sub_δ_pos P
  set x := (1 - P.δ) * (model P).xiS π n (goH n) * π n (goH n) 1 with hx
  have hx0 : 0 ≤ x := by
    have := (model P).xiS_nonneg hπ n (goH n) (nt_goH P hn)
    have := hπ.nonneg (nt_goH P hn) 1
    positivity
  have hx1 : x ≤ 1 - P.δ := by
    have h1 := xiS_goH_le_one P π hπ n hn
    have h2 := hπ.le_one (nt_goH P hn) 1
    have h4 := hπ.nonneg (nt_goH P hn) 1
    have h5 : (model P).xiS π n (goH n) * π n (goH n) 1 ≤ 1 := mul_le_one₀ h1 h4 h2
    rw [hx, mul_assoc]
    exact mul_le_of_le_one_right h1δ.le h5
  have hA : (model P).xiA π n (goH n) 1 = x + P.δ := by rw [xiA_goH_1]
  have hne : (model P).xiA π n (goH n) 1 ≠ 0 := by rw [hA]; linarith
  rw [(model P).wA_of_xiA_ne_zero hne, hA, model_δ, ← hx, div_le_iff₀ (by linarith)]
  nlinarith

/-- **The one-step bound**: if `Q^π(h_k, go) ≤ c` then `Q_ξ(h_k, go) ≤ (1-δ) c` (Lemma A: the residual's
continuation after `go` is worth `0`, and the self-mass after `go` is at most `1 - δ`).
Source: mandate target 8 (ii)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_goH_1_le (hπ : (model P).IsPolicy π) {n : ℕ} (hn : n ≤ P.K) {c : ℝ} (hc : 0 ≤ c)
    (hQ : (model P).Qpi π n (goH n) 1 ≤ c) : (model P).Qxi π n (goH n) 1 ≤ (1 - P.δ) * c := by
  have hne : (model P).xiA π n (goH n) 1 ≠ 0 := by
    rw [xiA_goH_1]
    have := (model P).xiS_nonneg hπ n (goH n) (nt_goH P hn)
    have := hπ.nonneg (nt_goH P hn) 1
    have := hδ P
    have := one_sub_δ_pos P
    positivity
  rw [(model P).Qxi_eq_wA hπ hne, Qmix_goH_1, mul_zero, add_zero]
  have hw0 := (model P).wA_nonneg hπ (nt_goH P hn) 1
  have hw1 := wA_goH_1_le P π hπ hn
  calc (model P).wA π n (goH n) 1 * (model P).Qpi π n (goH n) 1
      ≤ (model P).wA π n (goH n) 1 * c := mul_le_mul_of_nonneg_left hQ hw0
    _ ≤ (1 - P.δ) * c := mul_le_mul_of_nonneg_right hw1 hc

/-- `Q_ξ(h_k, go) < Q_ξ(h_k, stay)` given `V^π(h_{k+1}) ≤ c_{k+1}` (`k < K`), and at `h_K` unconditionally. -/
theorem Qxi_goH_1_lt (hπ : (model P).IsPolicy π) {n : ℕ} (hn : n ≤ P.K)
    (hV : n < P.K → (model P).Vpi π (n + 1) (goH (n + 1)) ≤ ck P (n + 1)) :
    (model P).Qxi π n (goH n) 1 < ck P n := by
  rcases lt_or_eq_of_le hn with hlt | heq
  · have h1 := Qxi_goH_1_le P π hπ hn (ck_pos P (n + 1)).le (by rw [Qpi_goH_1]; exact hV hlt)
    rw [ck_succ P hlt]
    have := ck_pos P (n + 1)
    have := P.hlt
    nlinarith
  · subst heq
    rw [Qxi_goH_K_1, ck_K]
    exact zero_lt_one

end Values

/-! ### Theorem D2 -/

section D2
variable {π : Policy (Fin 2) Unit}

/-- **Uniqueness (D2 (ii))**: every plain fixed point plays action `0` surely at every `h_k`, with
`V^π(h_k) = c_k` — by downward induction, strict at every node.
Source: [[uea-2-inventory]] 2-011 (D2; the source verified pure fixed points only)
Kind: P
Fidelity: stronger: uniqueness among all policies, pure or mixed, every `K`
Hyps: (a) -/
theorem stay_of_isPlainFP (hfp : (model P).IsPlainFP π) :
    ∀ n, n ≤ P.K → π n (goH n) 0 = 1 ∧ (model P).Vpi π n (goH n) = ck P n := by
  have hπ := hfp.1
  have step : ∀ n, n ≤ P.K → (n < P.K → (model P).Vpi π (n + 1) (goH (n + 1)) ≤ ck P (n + 1)) →
      π n (goH n) 0 = 1 ∧ (model P).Vpi π n (goH n) = ck P n := by
    intro n hn hV
    have hlt := Qxi_goH_1_lt P π hπ hn hV
    have h0 : π n (goH n) 1 = 0 := by
      by_contra hne
      have hpos : 0 < π n (goH n) 1 := lt_of_le_of_ne (hπ.nonneg (nt_goH P hn) 1) (Ne.symm hne)
      have hfx := hfp.2 n (goH n) (nt_goH P hn) 1 hpos
      have hle := (model P).Qxi_le_Mx (π := π) n (goH n) 0
      rw [Qxi_goH_0 P π hn] at hle
      linarith
    have h1 : π n (goH n) 0 = 1 := by rw [hπ.fin_two_zero (nt_goH P hn), h0, sub_zero]
    refine ⟨h1, ?_⟩
    rw [(model P).Vpi_eq (nt_goH P hn), Fin.sum_univ_two, h0, h1, Qpi_goH_0 P π hn]
    ring
  refine downward P ?_ ?_
  · exact step P.K le_rfl (fun h => absurd h (lt_irrefl _))
  · intro n hn ih
    exact step n hn.le (fun _ => ih.2.le)

/-- **Existence (D2 (i))**: any policy that plays action `0` at every `h_k` is a plain fixed point
(strictly: `Q_ξ(go) < Q_ξ(stay)` at every `h_k`).
Source: [[uea-2-inventory]] 2-011 (D2)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isPlainFP_of_stay (hπ : (model P).IsPolicy π) (hstay : ∀ n, n ≤ P.K → π n (goH n) 0 = 1) :
    (model P).IsPlainFP π := by
  have hV : ∀ n, n ≤ P.K → (model P).Vpi π n (goH n) = ck P n := by
    refine downward P ?_ ?_
    · rw [(model P).Vpi_eq (nt_goH P le_rfl), Fin.sum_univ_two, hstay P.K le_rfl, Qpi_goH_0 P π le_rfl,
        Qpi_goH_K_1]
      ring
    · intro n hn ih
      have h0 : π n (goH n) 1 = 0 := by
        have := hπ.fin_two_zero (nt_goH P hn.le); rw [hstay n hn.le] at this; linarith
      rw [(model P).Vpi_eq (nt_goH P hn.le), Fin.sum_univ_two, hstay n hn.le, h0, Qpi_goH_0 P π hn.le]
      ring
  refine ⟨hπ, fun n h hnt => ?_⟩
  have hn : n ≤ P.K := ((nonterminal_iff P n h).1 hnt).1
  rw [eq_goH_of_nonterminal P hnt]
  have hlt := Qxi_goH_1_lt P π hπ hn (fun hlt => (hV (n + 1) hlt).le)
  have hM : (model P).Mx π n (goH n) = ck P n := by
    rw [(model P).Mx_fin_two, Qxi_goH_0 P π hn]
    exact max_eq_left hlt.le
  refine Fin.forall_fin_two.2 ⟨fun _ => ?_, fun ha => ?_⟩
  · rw [hM, Qxi_goH_0 P π hn]
  · have := hπ.fin_two_zero (nt_goH P hn); rw [hstay n hn] at this; linarith

/-- **Theorem D2, the fixed-point set**: the plain fixed points of the trap chain are exactly the policies
that play action `0` at every `h_k`, `k ≤ K` (unique on the chain among all policies, pure or mixed).
Source: [[uea-2-inventory]] 2-011 (D2); mandate target 8
Kind: P
Fidelity: stronger: pure-or-mixed uniqueness, every `K, δ, δ'`
Hyps: (a) -/
theorem isPlainFP_iff : (model P).IsPlainFP π ↔ (model P).IsPolicy π ∧ ∀ n, n ≤ P.K → π n (goH n) 0 = 1 :=
  ⟨fun hfp => ⟨hfp.1, fun n hn => (stay_of_isPlainFP P hfp n hn).1⟩, fun ⟨hπ, hstay⟩ => isPlainFP_of_stay P hπ hstay⟩

theorem stayPol_isPlainFP : (model P).IsPlainFP stayPol :=
  isPlainFP_of_stay P (stayPol_isPolicy P) (fun _ _ => by simp [stayPol])

/-- Strict preference at every node of every fixed point. -/
theorem strict_of_isPlainFP (hfp : (model P).IsPlainFP π) {n : ℕ} (hn : n ≤ P.K) :
    (model P).Qxi π n (goH n) 1 < (model P).Qxi π n (goH n) 0 := by
  rw [Qxi_goH_0 P π hn]
  exact Qxi_goH_1_lt P π hfp.1 hn (fun hlt => (stay_of_isPlainFP P hfp (n + 1) hlt).2.le)

/-- **D2 (iii)**: every plain fixed point has root loss exactly `1 - (1-δ')^K`, with `V^*(h₀) = 1`.
Source: [[uea-2-inventory]] 2-011 (D2)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap_root_of_isPlainFP (hfp : (model P).IsPlainFP π) :
    (model P).gap π 0 (goH 0) = 1 - (1 - P.δ') ^ P.K ∧ (model P).Vstar 0 (goH 0) = 1 := by
  have hV := (stay_of_isPlainFP P hfp 0 (Nat.zero_le _)).2
  have hS := Vstar_goH P 0 (Nat.zero_le _)
  refine ⟨?_, hS⟩
  unfold Model.gap
  rw [hV, hS]
  simp [ck]

/-- `w_{h₀} = 1 - δ` under every policy (the root). -/
theorem wS_root (π : Policy (Fin 2) Unit) : (model P).wS π 0 (goH 0) = 1 - P.δ := by
  have hx : (model P).xi π 0 (goH 0) = 1 := by
    unfold Model.xi; rw [xins_goH, Model.xiS_zero, model_δ]; ring
  rw [Model.wS_of_xi_ne_zero _ (by rw [hx]; exact one_ne_zero), hx, Model.xiS_zero, model_δ]
  ring

/-- **D2 (iv)**: Cole's premise `w = 1 - δ` holds at the one node a fixed point reaches, `h₀`; at every deeper
chain node the fixed point's self-posterior is `0` (it never goes there; the residual does).
Source: mandate target 8 (iv)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem wS_goH_of_isPlainFP (hfp : (model P).IsPlainFP π) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ P.K) :
    (model P).wS π n (goH n) = 0 := by
  have hS : (model P).xiS π n (goH n) = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← goH_ext m (), Model.xiS_ext]
    have h0 : π m (goH m) 1 = 0 := by
      have := hfp.1.fin_two_zero (nt_goH P (show m ≤ P.K by omega))
      rw [(stay_of_isPlainFP P hfp m (by omega)).1] at this
      linarith
    rw [h0]; ring
  have hx : (model P).xi π n (goH n) = P.δ := by
    unfold Model.xi; rw [xins_goH, hS]; ring
  rw [Model.wS_of_xi_ne_zero _ (by rw [hx]; exact (hδ P).ne'), hS]
  simp

end D2

/-! ### Target 9(−): no horizon-free `δ` at `γ = 1` -/

/-- The chain parameters `δ' = 9δ/10`. -/
noncomputable def params (K : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) : TP :=
  ⟨K, δ, 9 * δ / 10, by linarith, by linarith, hδ1⟩

/-- **No horizon-free `δ` (target 9(−))**: for every `δ ∈ (0,1)` and every `ε < 1` there is a depth `K` and a
model (the trap chain with `δ' = 9δ/10`) with non-self prior `δ` which **has** a plain fixed point (the
stay-everywhere policy; the conjunct guards the `∀ π` against vacuity) and on which **every** plain fixed
point has `w_{h₀} = 1 - δ` and root loss `1 - (1-δ')^K > ε`. Neither this nor D1 uses the trust bound as a
hypothesis; the trust bound is what makes the per-node bound hold at every fixed point (Theorem B).
Source: [[uea-2-inventory]] 2-010 (negative half), 2-011; [[uea-inventory]] 018, 006
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem no_horizon_free_delta (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ε : ℝ) (hε : ε < 1) :
    ∃ (K : ℕ) (M : Model (Fin 2) Unit Unit), M.δ = δ ∧ M.T = K + 1 ∧ (∃ π, M.IsPlainFP π) ∧
      ∀ π, M.IsPlainFP π → ∀ h : Hist (Fin 2) Unit 0,
        M.wS π 0 h = 1 - δ ∧ M.gap π 0 h = 1 - (1 - 9 * δ / 10) ^ K ∧ ε < M.gap π 0 h := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1 - ε by linarith)
    (show 1 - 9 * δ / 10 < 1 by linarith)
  refine ⟨K, model (params K δ hδ hδ1), rfl, rfl, ⟨stayPol, stayPol_isPlainFP _⟩, fun π hfp h => ?_⟩
  rw [eq_goH_zero h]
  obtain ⟨hgap, _⟩ := gap_root_of_isPlainFP (params K δ hδ hδ1) hfp
  refine ⟨wS_root _ π, hgap, ?_⟩
  rw [hgap]
  show ε < 1 - (1 - 9 * δ / 10) ^ K
  linarith

end TrapChain

end Cleanroom.Uea.UeaSinkSwim
