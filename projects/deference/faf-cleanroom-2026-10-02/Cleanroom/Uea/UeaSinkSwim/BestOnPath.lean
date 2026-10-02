import Cleanroom.Uea.UeaSinkSwim.ResidualArgmax

/-!
# D1, part 1: the best-on-path recursion `B` and its horizon-dependent bound

Policy-free data of a model: the percept-only path probability `Pe(h) := ∏ ξ(eᵢ | h_{<i} aᵢ)`, the on-path
posterior after `(h, a)` of any pure policy that reaches `h` and plays `a` surely,
`wtA(h, a) := (1-δ) Pe(h) / ((1-δ) Pe(h) + ξ_{-S}(ha))` (`:= 1` at a zero denominator), the rival value
`rival(h, a) := max_{a' ≠ a} Alt(h, a')` (`0` if `|A| = 1`), and the backward recursion (fuel `T - n`, like
`valF`):
`cont(h, a) := ∑_e ξ(e|ha) (γ^n r(hae) + B(hae))`,
`S(h, a) := Q^*(h, a)` if `ξ_{-S}(ha) = 0` else `wtA(h,a) cont(h,a) + (1 - wtA(h,a)) Q̄(h,a)`,
`feasible(h, a) := rival(h, a) ≤ S(h, a)`, `val(h, a) := Q^*(h, a)` if `ξ_{-S}(ha) = 0` else `cont(h, a)`,
`B(h) := max_{feasible a} val(h, a)` at decision nodes (`0` elsewhere; `0` for an empty filter, which never
happens: `altChoice` is always feasible).

**Results** (all policy-free): the invariant `Alt ≤ val` and `V^{π̄} ≤ B` (depth induction), feasibility of
`altChoice`, `Alt(h, a_R) ≤ B(h)`; and the **bound** `V^*(h) - B(h) ≤ ε_n := 1 - (1-δ)^(T-1-n)` at every
history (depth induction with `ε_T = 0` at the last level, where `S = Q^*`, and
`δ + (1-δ) ε_{n+1} = ε_n` below it). Part 2 (`BestOnPathPolicy.lean`) builds `π^B` and shows
`V^{π^B} = B` on its path.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.BestOnPath`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow
open ResidualArgmax (Alt altChoice Alt_le_altChoice)

namespace BestOnPath

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)

/-! ### Policy-free data -/

/-- The percept-only path probability `Pe(h) := ∏_i ξ(eᵢ | h_{<i} aᵢ)`.
Source: `theorem1_search.py` `Structure` (`Pe`); mandate target 7
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Pe : (n : ℕ) → Hist A E n → ℝ
  | 0, _ => 1
  | n + 1, h => Pe n (Fin.init h) * M.xie n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2

@[simp] theorem Pe_zero (h : Hist A E 0) : Pe M 0 h = 1 := rfl

@[simp] theorem Pe_ext {n : ℕ} (h : Hist A E n) (a : A) (e : E) :
    Pe M (n + 1) (ext h a e) = Pe M n h * M.xie n h a e := by
  simp [Pe]

theorem Pe_nonneg : ∀ (n : ℕ) (h : Hist A E n), 0 ≤ Pe M n h := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    simp only [Pe]
    exact mul_nonneg (ih _) (M.xie_nonneg _ _ _ _)

/-- `ξ_{-S}(h) ≤ δ Pe(h)`: the residual's mass on a history is at most the prior times the percept-only path
probability (`ξ_{-S}(hae) = ξ_{-S}(ha) ξ(e|ha) ≤ ξ_{-S}(h) ξ(e|ha)`).
Source: mandate target 7 ("`xins h ≤ δ Pe h` by induction from `xins_ext`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xins_le_delta_Pe : ∀ (n : ℕ) (h : Hist A E n), M.xins n h ≤ M.δ * Pe M n h := by
  intro n
  induction n with
  | zero =>
    intro h
    simp only [Pe_zero, mul_one, Model.xins, Model.nuJoint_zero]
    rw [M.w_sum]
  | succ n ih =>
    intro h
    have hx := M.xins_ext n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2
    rw [ext_init_last] at hx
    rw [hx]
    simp only [Pe]
    have h1 := M.xinsA_le_xins n (Fin.init h) (h (Fin.last n)).1
    have h2 := ih (Fin.init h)
    have h3 := M.xie_nonneg n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2
    calc M.xinsA n (Fin.init h) (h (Fin.last n)).1 * M.xie n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2
        ≤ M.δ * Pe M n (Fin.init h) * M.xie n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2 :=
          mul_le_mul_of_nonneg_right (le_trans h1 h2) h3
      _ = _ := by ring

/-- The on-path posterior after `(h, a)` of any pure policy reaching `h` and playing `a` surely:
`wtA(h, a) := (1-δ) Pe(h) / ((1-δ) Pe(h) + ξ_{-S}(ha))`, `:= 1` at a zero denominator.
Source: `theorem1_search.py` `Structure` (`wt_ha`); mandate target 7
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def wtA (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  if (1 - M.δ) * Pe M n h + M.xinsA n h a = 0 then 1
  else (1 - M.δ) * Pe M n h / ((1 - M.δ) * Pe M n h + M.xinsA n h a)

theorem one_sub_δ_pos : 0 < 1 - M.δ := by linarith [M.δ_lt_one]

theorem wtA_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ wtA M n h a := by
  unfold wtA
  split_ifs
  · exact zero_le_one
  · have := Pe_nonneg M n h; have := M.xinsA_nonneg n h a; have := one_sub_δ_pos M
    positivity

theorem wtA_le_one (n : ℕ) (h : Hist A E n) (a : A) : wtA M n h a ≤ 1 := by
  unfold wtA
  split_ifs with hD
  · exact le_rfl
  · have h1 := Pe_nonneg M n h; have h2 := M.xinsA_nonneg n h a; have h3 := one_sub_δ_pos M
    have hpos : 0 < (1 - M.δ) * Pe M n h + M.xinsA n h a :=
      lt_of_le_of_ne (by positivity) (Ne.symm hD)
    rw [div_le_one hpos]
    linarith

/-- **`wtA ≥ 1 - δ`**: the on-path posterior never falls below the prior (`ξ_{-S}(ha) ≤ δ Pe(h)`).
Source: mandate target 7 ("`wt ≥ 1-δ`; `wtA ≥ wt` since `xinsA ≤ xins`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem one_sub_δ_le_wtA (n : ℕ) (h : Hist A E n) (a : A) : 1 - M.δ ≤ wtA M n h a := by
  unfold wtA
  split_ifs with hD
  · linarith [M.δ_pos]
  · have h1 := Pe_nonneg M n h; have h2 := M.xinsA_nonneg n h a; have h3 := one_sub_δ_pos M
    have hpos : 0 < (1 - M.δ) * Pe M n h + M.xinsA n h a :=
      lt_of_le_of_ne (by positivity) (Ne.symm hD)
    rw [le_div_iff₀ hpos]
    have h4 := le_trans (M.xinsA_le_xins n h a) (xins_le_delta_Pe M n h)
    nlinarith [M.δ_pos]

open Classical in
/-- The rival value `rival(h, a) := max_{a' ≠ a} Alt(h, a')` (`0` if `|A| = 1`).
Source: `theorem1_search.py` `best_onpath` (`rival`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def rival (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  if hne : (univ.erase a).Nonempty then (univ.erase a).sup' hne (Alt M n h) else 0

theorem Alt_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ Alt M n h a := by
  unfold Alt; split_ifs
  · exact M.Qstar_nonneg n h a
  · exact M.Qmix_nonneg n h a

theorem Alt_le_Qstar (n : ℕ) (h : Hist A E n) (a : A) : Alt M n h a ≤ M.Qstar n h a := by
  unfold Alt; split_ifs with hA
  · exact le_rfl
  · rw [M.Qmix_eq_Qbar hA]; exact M.Qbar_le_Qstar n h a

open Classical in
theorem Alt_le_rival {n : ℕ} {h : Hist A E n} {a b : A} (hb : b ≠ a) : Alt M n h b ≤ rival M n h a := by
  unfold rival
  have hmem : b ∈ univ.erase a := mem_erase.2 ⟨hb, mem_univ b⟩
  rw [dif_pos ⟨b, hmem⟩]
  exact le_sup' _ hmem

open Classical in
theorem rival_le_Alt_altChoice (n : ℕ) (h : Hist A E n) (a : A) :
    rival M n h a ≤ Alt M n h (altChoice M n h) := by
  unfold rival
  split_ifs with hne
  · rw [Finset.sup'_le_iff]
    intro b _
    exact Alt_le_altChoice M n h b
  · exact Alt_nonneg M n h _

/-! ### The recursion with fuel -/

/-- `cont(h, a)` with a given value function `Bc` on the children: `∑_e ξ(e|ha)(γ^n r(hae) + Bc(hae))`.
Source: `theorem1_search.py` `best_onpath` (`cont`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def contW (n : ℕ) (Bc : Hist A E (n + 1) → ℝ) (h : Hist A E n) (a : A) : ℝ :=
  ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + Bc (ext h a e))

/-- `S(h, a)` with a given value function on the children: `Q^*(h, a)` on a residual-null action, else
`wt(ha) cont(h, a) + (1 - wt(ha)) Q̄(h, a)` — the on-path `Q_ξ` of a played action.
Source: `theorem1_search.py` `best_onpath` (`S`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def SW (n : ℕ) (Bc : Hist A E (n + 1) → ℝ) (h : Hist A E n) (a : A) : ℝ :=
  if M.xinsA n h a = 0 then M.Qstar n h a
  else wtA M n h a * contW M n Bc h a + (1 - wtA M n h a) * M.Qmix n h a

/-- `feasible(h, a) := rival(h, a) ≤ S(h, a)` (with a given value function on the children).
Source: `theorem1_search.py` `best_onpath` (`feasible`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
def feasW (n : ℕ) (Bc : Hist A E (n + 1) → ℝ) (h : Hist A E n) (a : A) : Prop :=
  rival M n h a ≤ SW M n Bc h a

/-- `val(h, a) := Q^*(h, a)` on a residual-null action, else `cont(h, a)` (with a given value function on the children).
Source: `theorem1_search.py` `best_onpath` (`val`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def valW (n : ℕ) (Bc : Hist A E (n + 1) → ℝ) (h : Hist A E n) (a : A) : ℝ :=
  if M.xinsA n h a = 0 then M.Qstar n h a else contW M n Bc h a

open Classical in
/-- One node of the recursion: the maximum of `val` over the feasible actions (`0` at terminal nodes and for an
empty filter — the latter never fires, `altChoice_feasible`).
Source: `theorem1_search.py` `best_onpath` (the per-node maximum); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact (the empty-filter fallback is junk that is proved unreachable)
Hyps: n/a -/
noncomputable def nodeW (n : ℕ) (Bc : Hist A E (n + 1) → ℝ) (h : Hist A E n) : ℝ :=
  if M.nonterminal n h then
    (if hne : (univ.filter (feasW M n Bc h)).Nonempty then (univ.filter (feasW M n Bc h)).sup' hne (valW M n Bc h)
     else 0)
  else 0

/-- The recursion with fuel: `BF 0 = 0`, `BF (k+1) n h = nodeW n (BF k (n+1)) h`; `B` is `BF (T - n)`.
Source: `theorem1_search.py` `best_onpath` (the recursion); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact (fuel `T - n` reaches every live depth, `B_eq_nodeW`)
Hyps: n/a -/
noncomputable def BF : ℕ → (n : ℕ) → Hist A E n → ℝ
  | 0, _, _ => 0
  | k + 1, n, h => nodeW M n (fun h' => BF k (n + 1) h') h

/-- **The best-on-path value** `B(h)`: the recursion with fuel `T - n`.
Source: `theorem1_search.py` `best_onpath` (`B`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact (the fallback `0` for an empty feasible set never fires: `altChoice_feasible`)
Hyps: n/a -/
noncomputable def B (n : ℕ) (h : Hist A E n) : ℝ := BF M (M.T - n) n h

theorem B_eq_zero_of_not_nonterminal {n : ℕ} {h : Hist A E n} (hnt : ¬ M.nonterminal n h) : B M n h = 0 := by
  unfold B
  cases hk : M.T - n with
  | zero => simp [BF]
  | succ k => simp [BF, nodeW, hnt]

theorem B_eq_nodeW {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    B M n h = nodeW M n (B M (n + 1)) h := by
  have hk : M.T - n = (M.T - (n + 1)) + 1 := by have := hnt.1; omega
  unfold B
  rw [hk]
  rfl

/-- The node-level `cont(h, a)`, with `B` on the children.
Source: `theorem1_search.py` `best_onpath` (`cont`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def cont (n : ℕ) (h : Hist A E n) (a : A) : ℝ := contW M n (B M (n + 1)) h a

/-- The node-level `S(h, a)`, with `B` on the children.
Source: `theorem1_search.py` `best_onpath` (`S`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def S (n : ℕ) (h : Hist A E n) (a : A) : ℝ := SW M n (B M (n + 1)) h a

/-- The node-level `feasible(h, a) := rival(h, a) ≤ S(h, a)`, with `B` on the children.
Source: `theorem1_search.py` `best_onpath` (`feasible`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
def feasible (n : ℕ) (h : Hist A E n) (a : A) : Prop := feasW M n (B M (n + 1)) h a

/-- The node-level `val(h, a)`, with `B` on the children.
Source: `theorem1_search.py` `best_onpath` (`val`); [[uea-2-inventory]] 2-009
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def val (n : ℕ) (h : Hist A E n) (a : A) : ℝ := valW M n (B M (n + 1)) h a

theorem feasible_iff (n : ℕ) (h : Hist A E n) (a : A) : feasible M n h a ↔ rival M n h a ≤ S M n h a := Iff.rfl

theorem val_of_xinsA_eq_zero {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xinsA n h a = 0) :
    val M n h a = M.Qstar n h a := by simp [val, valW, hA]
theorem val_of_xinsA_ne_zero {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xinsA n h a ≠ 0) :
    val M n h a = cont M n h a := by simp [val, valW, hA, cont]
theorem S_of_xinsA_eq_zero {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xinsA n h a = 0) :
    S M n h a = M.Qstar n h a := by simp [S, SW, hA]
theorem S_of_xinsA_ne_zero {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xinsA n h a ≠ 0) :
    S M n h a = wtA M n h a * cont M n h a + (1 - wtA M n h a) * M.Qmix n h a := by
  simp [S, SW, hA, cont]

theorem cont_eq (n : ℕ) (h : Hist A E n) (a : A) :
    cont M n h a = ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + B M (n + 1) (ext h a e)) := rfl

open Classical in
theorem B_eq_sup' {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (hne : (univ.filter (feasible M n h)).Nonempty) :
    B M n h = (univ.filter (feasible M n h)).sup' hne (val M n h) := by
  rw [B_eq_nodeW M hnt]
  unfold nodeW
  rw [if_pos hnt]
  exact dif_pos hne

/-- `cont(h, a) ≥ ∑_e ξ(e|ha)(γ^n r + c(hae))` for any lower bound `c` of `B` at the children.
Source: none: infrastructure (monotonicity of `cont` in the children's values)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cont_ge_of_le {n : ℕ} {h : Hist A E n} {a : A} {c : E → ℝ}
    (hc : ∀ e, c e ≤ B M (n + 1) (ext h a e)) :
    ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + c e) ≤ cont M n h a := by
  rw [cont_eq]
  refine sum_le_sum fun e _ => ?_
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (hc e)) (M.xie_nonneg n h a e)

/-! ### The invariant `Alt ≤ val`, feasibility of `altChoice`, `V^{π̄} ≤ B` -/

/-- Given `Alt ≤ val` at `h`: `Alt ≤ S` (`S = Q^* = Alt` on a null action; else a convex combination of
`cont ≥ Alt` and `Q̄ = Alt`).
Source: none: infrastructure (a step of `invariant`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Alt_le_S_of {n : ℕ} {h : Hist A E n} (hAv : ∀ a, Alt M n h a ≤ val M n h a) (a : A) :
    Alt M n h a ≤ S M n h a := by
  by_cases hA : M.xinsA n h a = 0
  · rw [S_of_xinsA_eq_zero M hA]
    unfold Alt; rw [if_pos hA]
  · rw [S_of_xinsA_ne_zero M hA]
    have h1 := hAv a
    rw [val_of_xinsA_ne_zero M hA] at h1
    have hAlt : Alt M n h a = M.Qmix n h a := by unfold Alt; rw [if_neg hA]
    rw [hAlt] at h1 ⊢
    have := wtA_nonneg M n h a; have := wtA_le_one M n h a
    nlinarith

theorem altChoice_feasible_of {n : ℕ} {h : Hist A E n} (hAv : ∀ a, Alt M n h a ≤ val M n h a) :
    feasible M n h (altChoice M n h) :=
  le_trans (rival_le_Alt_altChoice M n h _) (Alt_le_S_of M hAv _)

open Classical in
theorem filter_nonempty_of {n : ℕ} {h : Hist A E n} (hAv : ∀ a, Alt M n h a ≤ val M n h a) :
    (univ.filter (feasible M n h)).Nonempty :=
  ⟨altChoice M n h, mem_filter.2 ⟨mem_univ _, altChoice_feasible_of M hAv⟩⟩

open Classical in
theorem val_le_B_of {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (hAv : ∀ a, Alt M n h a ≤ val M n h a)
    {a : A} (hf : feasible M n h a) : val M n h a ≤ B M n h := by
  rw [B_eq_sup' M hnt (filter_nonempty_of M hAv)]
  exact le_sup' _ (mem_filter.2 ⟨mem_univ _, hf⟩)

theorem Alt_altChoice_le_B_of {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hAv : ∀ a, Alt M n h a ≤ val M n h a) : Alt M n h (altChoice M n h) ≤ B M n h :=
  le_trans (hAv _) (val_le_B_of M hnt hAv (altChoice_feasible_of M hAv))

theorem Vbar_le_B_of {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hAv : ∀ a, Alt M n h a ≤ val M n h a) : M.Vbar n h ≤ B M n h := by
  have hB := Alt_altChoice_le_B_of M hnt hAv
  by_cases hx : M.xins n h = 0
  · rw [M.Vbar_eq hnt, sum_eq_zero fun a _ => by rw [M.pibar_of_xins_eq_zero hx a, zero_mul]]
    exact le_trans (Alt_nonneg M n h _) hB
  · rw [M.Vbar_eq hnt]
    calc ∑ a, M.pibar n h a * M.Qbar n h a
        ≤ ∑ a, M.pibar n h a * Alt M n h (altChoice M n h) := by
          refine sum_le_sum fun a _ => ?_
          by_cases hA : M.xinsA n h a = 0
          · have h0 : M.pibar n h a = 0 := by unfold Model.pibar; rw [hA, zero_div]
            rw [h0, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left ?_ (M.pibar_nonneg n h a)
            calc M.Qbar n h a = Alt M n h a := by unfold Alt; rw [if_neg hA, M.Qmix_eq_Qbar hA]
              _ ≤ Alt M n h (altChoice M n h) := Alt_le_altChoice M n h a
      _ = Alt M n h (altChoice M n h) := by rw [← sum_mul, M.pibar_sum_eq_one hx, one_mul]
      _ ≤ B M n h := hB

/-- **The invariant**: `V^{π̄}(h) ≤ B(h)` at every history, and `Alt(h, a) ≤ val(h, a)` at every decision node.
Source: mandate target 7 ("prove `a_R` is always feasible: `cont B h a_R ≥ Alt h a_R` by the D0 invariant with `B` in place of `Vpi`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem invariant : ∀ n h, M.Vbar n h ≤ B M n h ∧ (M.nonterminal n h → ∀ a, Alt M n h a ≤ val M n h a) := by
  refine M.depth_induction (fun n h => M.Vbar n h ≤ B M n h ∧ (M.nonterminal n h → ∀ a, Alt M n h a ≤ val M n h a)) ?_ ?_
  · intro n h hnt
    refine ⟨?_, fun h' => absurd h' hnt⟩
    rw [M.Vbar_of_not_nonterminal hnt, B_eq_zero_of_not_nonterminal M hnt]
  · intro n h hnt ih
    have hAv : ∀ a, Alt M n h a ≤ val M n h a := by
      intro a
      by_cases hA : M.xinsA n h a = 0
      · rw [val_of_xinsA_eq_zero M hA]; unfold Alt; rw [if_pos hA]
      · rw [val_of_xinsA_ne_zero M hA]
        unfold Alt; rw [if_neg hA, M.Qmix_eq_Qbar hA, M.Qbar_eq_sum]
        exact cont_ge_of_le M fun e => (ih a e).1
    exact ⟨Vbar_le_B_of M hnt hAv, fun _ => hAv⟩

theorem Alt_le_val {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) : Alt M n h a ≤ val M n h a :=
  (invariant M n h).2 hnt a

theorem Alt_le_S {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) : Alt M n h a ≤ S M n h a :=
  Alt_le_S_of M (Alt_le_val M hnt) a

/-- **`altChoice` is always feasible** (so the fallback `0` in `nodeW` never fires).
Source: `theorem1_search.py` `best_onpath` ("cannot happen: argmax Alt is feasible"); mandate target 7
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem altChoice_feasible {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) : feasible M n h (altChoice M n h) :=
  altChoice_feasible_of M (Alt_le_val M hnt)

open Classical in
theorem filter_nonempty {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    (univ.filter (feasible M n h)).Nonempty := filter_nonempty_of M (Alt_le_val M hnt)

theorem val_le_B {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) {a : A} (hf : feasible M n h a) :
    val M n h a ≤ B M n h := val_le_B_of M hnt (Alt_le_val M hnt) hf

theorem Alt_altChoice_le_B {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    Alt M n h (altChoice M n h) ≤ B M n h := Alt_altChoice_le_B_of M hnt (Alt_le_val M hnt)

theorem rival_le_B {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) : rival M n h a ≤ B M n h :=
  le_trans (rival_le_Alt_altChoice M n h a) (Alt_altChoice_le_B M hnt)

theorem B_nonneg (n : ℕ) (h : Hist A E n) : 0 ≤ B M n h := by
  by_cases hnt : M.nonterminal n h
  · exact le_trans (Alt_nonneg M n h _) (Alt_altChoice_le_B M hnt)
  · rw [B_eq_zero_of_not_nonterminal M hnt]

/-- `B = V^*` on a residual-null subtree (every action is null, `val = Q^*`, and the feasible actions are exactly
the `argmax Q^*`). -/
theorem B_eq_Vstar_of_xins_eq_zero : ∀ n h, M.xins n h = 0 → B M n h = M.Vstar n h := by
  refine M.depth_induction (fun n h => M.xins n h = 0 → B M n h = M.Vstar n h) ?_ ?_
  · intro n h hnt _
    rw [B_eq_zero_of_not_nonterminal M hnt, M.Vstar_of_not_nonterminal hnt]
  · intro n h hnt _ hx
    have hA : ∀ a, M.xinsA n h a = 0 := M.xinsA_eq_zero_of_xins_eq_zero hx
    have hval : ∀ a, val M n h a = M.Qstar n h a := fun a => val_of_xinsA_eq_zero M (hA a)
    apply le_antisymm
    · rw [B_eq_sup' M hnt (filter_nonempty M hnt), Finset.sup'_le_iff]
      intro a _
      rw [hval a]
      exact M.Qstar_le_Vstar hnt a
    · -- `piStar h` is feasible: `S = Q^* = V^* ≥ rival`
      have hf : feasible M n h (M.piStar n h) := by
        rw [feasible_iff, S_of_xinsA_eq_zero M (hA _), ← M.Vstar_eq_Qstar_piStar hnt]
        exact le_trans (rival_le_Alt_altChoice M n h _)
          (le_trans (Alt_le_Qstar M n h _) (M.Qstar_le_Vstar hnt _))
      have := val_le_B M hnt hf
      rwa [hval, ← M.Vstar_eq_Qstar_piStar hnt] at this


/-! ### The horizon-dependent bound `V^* - B ≤ ε_n` -/

/-- `ε_n := 1 - (1-δ)^(T-1-n)`.
Source: [[uea-2-inventory]] 2-009 (D1's per-depth bound)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def eps (n : ℕ) : ℝ := 1 - (1 - M.δ) ^ (M.T - 1 - n)

theorem one_sub_δ_le_one : 1 - M.δ ≤ 1 := by linarith [M.δ_pos]

theorem eps_nonneg (n : ℕ) : 0 ≤ eps M n := by
  unfold eps
  have := pow_le_one₀ (one_sub_δ_pos M).le (one_sub_δ_le_one M) (n := M.T - 1 - n)
  linarith

theorem eps_succ_le (n : ℕ) : eps M (n + 1) ≤ eps M n := by
  unfold eps
  have := pow_le_pow_of_le_one (one_sub_δ_pos M).le (one_sub_δ_le_one M)
    (show M.T - 1 - (n + 1) ≤ M.T - 1 - n by omega)
  linarith

theorem eps_step {n : ℕ} (hn : n + 1 < M.T) : M.δ + (1 - M.δ) * eps M (n + 1) = eps M n := by
  unfold eps
  have : M.T - 1 - n = (M.T - 1 - (n + 1)) + 1 := by omega
  rw [this, pow_succ]
  ring

theorem eps_last {n : ℕ} (hn : n + 1 = M.T) : eps M n = 0 := by
  unfold eps
  have : M.T - 1 - n = 0 := by omega
  rw [this, pow_zero, sub_self]

/-- At the last level `Q̄ = Q^*` (same percept kernel, tree-fixed rewards, no continuation). -/
theorem Qmix_eq_Qstar_of_children_terminal {n : ℕ} {h : Hist A E n} {a : A}
    (hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h a e)) (hA : M.xinsA n h a ≠ 0) :
    M.Qmix n h a = M.Qstar n h a := by
  rw [M.Qmix_eq_Qbar hA, M.Qbar_eq_sum, M.Qstar_eq_of_children_terminal h a hc]
  refine sum_congr rfl fun e _ => ?_
  rw [M.Vbar_of_not_nonterminal (hc e), add_zero]

theorem cont_eq_Qstar_of_children_terminal {n : ℕ} {h : Hist A E n} {a : A}
    (hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h a e)) : cont M n h a = M.Qstar n h a := by
  rw [cont_eq, M.Qstar_eq_of_children_terminal h a hc]
  refine sum_congr rfl fun e _ => ?_
  rw [B_eq_zero_of_not_nonterminal M (hc e), add_zero]

/-- At the last level `S = Q^*`, so `π⋆(h)` is feasible there and the loss is `0`. -/
theorem S_eq_Qstar_of_children_terminal {n : ℕ} {h : Hist A E n} {a : A}
    (hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h a e)) : S M n h a = M.Qstar n h a := by
  by_cases hA : M.xinsA n h a = 0
  · rw [S_of_xinsA_eq_zero M hA]
  · rw [S_of_xinsA_ne_zero M hA, cont_eq_Qstar_of_children_terminal M hc, Qmix_eq_Qstar_of_children_terminal M hc hA]
    ring

/-- `cont(h, π⋆(h)) ≥ V^*(h) - ε_{n+1}` given the bound at the children. -/
theorem cont_piStar_ge {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (ih : ∀ a e, M.Vstar (n + 1) (ext h a e) - B M (n + 1) (ext h a e) ≤ eps M (n + 1)) :
    M.Vstar n h - eps M (n + 1) ≤ cont M n h (M.piStar n h) := by
  calc M.Vstar n h - eps M (n + 1)
      = ∑ e, M.xie n h (M.piStar n h) e * (M.γ ^ n * M.r n (ext h (M.piStar n h) e) +
          M.Vstar (n + 1) (ext h (M.piStar n h) e)) - eps M (n + 1) := by
        rw [M.Vstar_eq_Qstar_piStar hnt, M.Qstar_eq_sum]
    _ = ∑ e, M.xie n h (M.piStar n h) e * (M.γ ^ n * M.r n (ext h (M.piStar n h) e) +
          (M.Vstar (n + 1) (ext h (M.piStar n h) e) - eps M (n + 1))) := by
        simp_rw [← add_sub_assoc, mul_sub]
        rw [sum_sub_distrib, ← sum_mul, M.xie_sum, one_mul]
    _ ≤ cont M n h (M.piStar n h) :=
        cont_ge_of_le M fun e => by linarith [ih (M.piStar n h) e]

/-- **The bound on `B`**: `V^*(h) - B(h) ≤ ε_n = 1 - (1-δ)^(T-1-n)` at every history. Depth induction: at the
last level `S = Q^*`, so `π⋆` is feasible and the loss is `0`; below it, if `π⋆` is feasible then
`B ≥ val(π⋆) ≥ V^* - ε_{n+1}`, and if not then `B ≥ rival(π⋆) > S(π⋆) ≥ wtA · cont(π⋆) ≥ (1-δ)(V^* - ε_{n+1})`,
so `V^* - B ≤ δ V^* + (1-δ) ε_{n+1} ≤ ε_n`.
Source: [[uea-2-inventory]] 2-009 (D1); the proof is the mandate writer's sketch, verified
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Vstar_sub_B_le : ∀ n h, M.Vstar n h - B M n h ≤ eps M n := by
  refine M.depth_induction (fun n h => M.Vstar n h - B M n h ≤ eps M n) ?_ ?_
  · intro n h hnt
    rw [M.Vstar_of_not_nonterminal hnt, B_eq_zero_of_not_nonterminal M hnt, sub_self]
    exact eps_nonneg M n
  · intro n h hnt ih
    have hV := M.Vstar_eq_Qstar_piStar hnt
    have hV1 := M.Vstar_le_one n h
    have hB0 := B_nonneg M n h
    have hrival : rival M n h (M.piStar n h) ≤ B M n h := rival_le_B M hnt _
    have hε0 := eps_nonneg M n
    by_cases hT : n + 1 = M.T
    · have hc : ∀ e, ¬ M.nonterminal (n + 1) (ext h (M.piStar n h) e) :=
        fun e => M.not_nonterminal_of_le (by omega) _
      have hf : feasible M n h (M.piStar n h) := by
        rw [feasible_iff, S_eq_Qstar_of_children_terminal M hc, ← hV]
        exact le_trans (rival_le_Alt_altChoice M n h _)
          (le_trans (Alt_le_Qstar M n h _) (M.Qstar_le_Vstar hnt _))
      have hval : val M n h (M.piStar n h) = M.Vstar n h := by
        by_cases hA : M.xinsA n h (M.piStar n h) = 0
        · rw [val_of_xinsA_eq_zero M hA, hV]
        · rw [val_of_xinsA_ne_zero M hA, cont_eq_Qstar_of_children_terminal M hc, hV]
      have := val_le_B M hnt hf
      rw [hval] at this
      rw [eps_last M hT]
      linarith
    · have hT' : n + 1 < M.T := lt_of_le_of_ne hnt.1 hT
      have hstep := eps_step M hT'
      have hcont := cont_piStar_ge M hnt ih
      have hmono := eps_succ_le M n
      by_cases hf : feasible M n h (M.piStar n h)
      · have hvB := val_le_B M hnt hf
        by_cases hA : M.xinsA n h (M.piStar n h) = 0
        · rw [val_of_xinsA_eq_zero M hA, ← hV] at hvB
          linarith
        · rw [val_of_xinsA_ne_zero M hA] at hvB
          linarith
      · rw [feasible_iff, not_le] at hf
        by_cases hA : M.xinsA n h (M.piStar n h) = 0
        · rw [S_of_xinsA_eq_zero M hA, ← hV] at hf
          linarith
        · rw [S_of_xinsA_ne_zero M hA] at hf
          have hw0 := wtA_nonneg M n h (M.piStar n h)
          have hw1 := wtA_le_one M n h (M.piStar n h)
          have hwδ := one_sub_δ_le_wtA M n h (M.piStar n h)
          have hQ := M.Qmix_nonneg n h (M.piStar n h)
          have hS : wtA M n h (M.piStar n h) * cont M n h (M.piStar n h) ≤
              wtA M n h (M.piStar n h) * cont M n h (M.piStar n h) +
                (1 - wtA M n h (M.piStar n h)) * M.Qmix n h (M.piStar n h) := by nlinarith
          by_cases hpos : 0 ≤ M.Vstar n h - eps M (n + 1)
          · have h1 : (1 - M.δ) * (M.Vstar n h - eps M (n + 1)) ≤
                wtA M n h (M.piStar n h) * cont M n h (M.piStar n h) :=
              calc (1 - M.δ) * (M.Vstar n h - eps M (n + 1))
                  ≤ wtA M n h (M.piStar n h) * (M.Vstar n h - eps M (n + 1)) :=
                    mul_le_mul_of_nonneg_right hwδ hpos
                _ ≤ wtA M n h (M.piStar n h) * cont M n h (M.piStar n h) :=
                    mul_le_mul_of_nonneg_left hcont hw0
            have hδV := mul_nonneg M.δ_pos.le (sub_nonneg.2 hV1)
            nlinarith
          · have : M.Vstar n h < eps M (n + 1) := by linarith [not_le.1 hpos]
            linarith

/-- **Corollary at the root**: `V^*(ε) - B(ε) ≤ 1 - (1-δ)^(T-1)`. -/
theorem Vstar_sub_B_root_le (h : Hist A E 0) : M.Vstar 0 h - B M 0 h ≤ 1 - (1 - M.δ) ^ (M.T - 1) :=
  Vstar_sub_B_le M 0 h

end BestOnPath

end Cleanroom.Uea.UeaSinkSwim
