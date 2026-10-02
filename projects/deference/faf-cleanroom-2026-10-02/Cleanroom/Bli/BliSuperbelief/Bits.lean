import Cleanroom.Bli.BliSuperbelief.Expr
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Log

/-!
# `bli-superbelief` · Bits: the bit-size of `tentExpr`'s constants (E2(d), the half FAF meters)

`tentExpr_cost_le`/`tentExpr_size_le` (`Expr.lean`) bound the node count and the token count of
`tentExpr 𝓜 m h Q` by `88·|S (m+h+1)| + 1` and three times that, uniformly in `h` and `d`, because
a rational constant is one `const` node / one `Encodable.encode q` token. FAF's efficiency class
is **bit**-metered: `EfficientlyComputable` (`Framework/Criterion.lean`) asks for an `FP` function
on `List Bool` whose output is read through `bitsToDigits`/`undigitize` — every token re-emitted as
a self-delimiting base-4 digit block (`tokenBlock`, `digitize`), so a token of value `< 4^K` costs
`K + 1` digits. The program's "constants of `O((m−k) log d)` bits" ([[bli-program]] §3.4) is
therefore the half of E2(d) that FAF meters, and it is proved here (audit r1, fidelity §2.1):

* **denominators** — every chain constant `chainFrom 𝓜 m h μ v` (`μ ∈ {δ₀, U, δ₁}`) and every
  new-coordinate constant `coordMarg 𝓜 m h t φ v` (`φ ∉ S m`) is an integer multiple of
  `1 / chainDen 𝓜 m h`, where `chainDen 𝓜 m 0 = d(m+1) + 1` and
  `chainDen 𝓜 m (h+1) = chainDen 𝓜 m h · d(m+h+1) · (d(m+h+2) + 1)` (`chainFrom_den`,
  `coordMarg_den`); under a mesh bound `d(m+k) ≤ D` for `k ≤ h+1`, `chainDen ≤ (D+1)^(2h+1)`
  (`chainDen_le_pow`): `O(h · log d)` bits;
* **numerators** — the constants are probabilities (`chainFrom_isLaw`, `coordMarg_isLaw`), so
  `|num| ≤ den`; with the scaffolding constants `−1, 0, 1, 2`, every `const q` of `tentExpr`
  has `q.den ≤ chainDen` and `|q.num| ≤ chainDen` (`tentExpr_constsBounded`);
* **codes** — Mathlib's `Encodable ℚ` is `Nat.pair (encode num) den`, so
  `encode q < (2·chainDen + 2)²` (`encode_rat_lt`); every token of the serialization is below
  `max (8, m, the day-`m` sentence codes, (2·chainDen + 2)²)` (`tentExpr_token_lt`);
* **FAF's digit meter** — `(digitize (tentExpr 𝓜 m h Q).serialize).length ≤ (K+1) · 3 · (88·|S (m+h+1)| + 1)`
  whenever `4^K` exceeds the three token bounds (`tentExpr_digitize_length_le`), with the
  explicit `K = log₄(max …) + 1` (`tentExpr_digitize_length_le_log`). This is the digit stream
  of `serialize`; the stream FAF's class reads is its `escExpand` (sentence slots escaped, since
  `strategyOfOutput` contracts them with `unRpn` before deserialization), which costs exactly
  `8·|S m|` more digits — `Escape.lean` (repair round 2).

Sources: [[bli-program]] §3.4 (size `O(|S_m| · poly(m, log d))`, "constants of `O((m−k) log d)`
bits"); mandate E2(d); FAF `Framework/Criterion.lean` (`serialize`, `tokenBlock`, `digitize`,
`EfficientlyComputable`). The sentence codes `encode φ` for `φ ∈ S m` and the day `m` are the
other tokens; their size is `bli-found`'s (the small set's) business and enters as a hypothesis.
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction Finset Cleanroom.Bli.BliFinite

/-! ## Denominator control: integer multiples of `1/N` -/

/-- `Den N q`: `q · N` is an integer, i.e. `q` is an integer multiple of `1/N`. Junk value: at
`N = 0` every `q` satisfies `Den 0 q`; every use here has `0 < N` (`chainDen ≥ 2`,
`two_le_chainDen`), and the only bridge to `q.den ≤ N` (`num_den_le_of_den`) takes `0 < N`
(audit r2 adversarial §3.2).
Source: none: infrastructure (mandate E2(d), the constants' bit-size)
Kind: D
Fidelity: n/a -/
def Den (N : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, q * N = z

namespace Den

/-- `0` is a multiple of `1/N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zero (N : ℕ) : Den N 0 := ⟨0, by simp⟩

/-- `1` is a multiple of `1/N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one (N : ℕ) : Den N 1 := ⟨N, by simp⟩

/-- Sums of multiples of `1/N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma add {N : ℕ} {a b : ℚ} (ha : Den N a) (hb : Den N b) : Den N (a + b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  exact ⟨x + y, by rw [add_mul, hx, hy]; push_cast; ring⟩

/-- Negation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma neg {N : ℕ} {a : ℚ} (ha : Den N a) : Den N (-a) := by
  obtain ⟨x, hx⟩ := ha
  exact ⟨-x, by rw [neg_mul, hx]; push_cast; ring⟩

/-- Differences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sub {N : ℕ} {a b : ℚ} (ha : Den N a) (hb : Den N b) : Den N (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

/-- Doubling.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_mul {N : ℕ} {a : ℚ} (ha : Den N a) : Den N (2 * a) := by
  obtain ⟨x, hx⟩ := ha
  exact ⟨2 * x, by rw [mul_assoc, hx]; push_cast; ring⟩

/-- Products multiply the denominators.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mul {N₁ N₂ : ℕ} {a b : ℚ} (ha : Den N₁ a) (hb : Den N₂ b) : Den (N₁ * N₂) (a * b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  push_cast
  calc a * b * (N₁ * N₂) = (a * N₁) * (b * N₂) := by ring
    _ = x * y := by rw [hx, hy]

/-- A multiple of `1/N` is a multiple of `1/M` when `N ∣ M`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mono {N M : ℕ} {a : ℚ} (ha : Den N a) (h : N ∣ M) : Den M a := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨x, hx⟩ := ha
  exact ⟨x * k, by push_cast; rw [← mul_assoc, hx]⟩

/-- Finite sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum {N : ℕ} {ι : Type*} {s : Finset ι} {f : ι → ℚ} (h : ∀ i ∈ s, Den N (f i)) :
    Den N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Den.zero N
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Indicators.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ite (p : Prop) [Decidable p] (N : ℕ) : Den N (if p then (1 : ℚ) else 0) := by
  split_ifs
  · exact Den.one N
  · exact Den.zero N

/-- `max 0 ·` preserves the denominator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma max_zero {N : ℕ} {a : ℚ} (ha : Den N a) : Den N (max 0 a) := by
  obtain ⟨x, hx⟩ := ha
  refine ⟨max 0 x, ?_⟩
  rw [max_mul_of_nonneg _ _ (Nat.cast_nonneg N), zero_mul, hx]
  push_cast
  rfl

/-- Absolute values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs {N : ℕ} {a : ℚ} (ha : Den N a) : Den N |a| := by
  obtain ⟨x, hx⟩ := ha
  refine ⟨|x|, ?_⟩
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℚ) N), ← abs_mul, hx]
  push_cast
  rfl

end Den

/-- The uniform law on `gridVals d` is a multiple of `1/(d+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma den_uniform1 (d : ℕ) (v : ℚ) : Den (d + 1) (uniform1 d v) := by
  unfold uniform1
  split_ifs
  · exact ⟨1, by push_cast; field_simp⟩
  · exact Den.zero _

/-- A grid value `k/d` is a multiple of `1/d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma den_of_mem_gridVals {d : ℕ} {v : ℚ} (hv : v ∈ gridVals d) : Den d v := by
  obtain ⟨k, -, rfl⟩ := mem_gridVals_iff.mp hv
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, by simp⟩
  · refine ⟨k, ?_⟩
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp

/-- **The tent law at a grid price has denominator `d' · (d+1)`**: `tent1 d x v` with
`x ∈ gridVals d'` is a multiple of `1 / (d' · (d + 1))` (weights in `1/d'`, laws in `1/(d+1)`).
Source: none: infrastructure (mandate E2(d))
Kind: L
Fidelity: n/a -/
lemma den_tent1_of_mem {d' d : ℕ} {x : ℚ} (hx : x ∈ gridVals d') (v : ℚ) :
    Den (d' * (d + 1)) (tent1 d x v) := by
  have hc : clamp01 x = x := clamp01_eq_self (gridVals_subset_Icc hx)
  have hdx : Den d' x := den_of_mem_gridVals hx
  unfold tent1
  rw [hc]
  have hw0 : Den d' (max 0 (1 - 2 * x)) := ((Den.one d').sub hdx.two_mul).max_zero
  have hwU : Den d' (1 - |2 * x - 1|) := (Den.one d').sub (hdx.two_mul.sub (Den.one d')).abs
  have hw1 : Den d' (max 0 (2 * x - 1)) := (hdx.two_mul.sub (Den.one d')).max_zero
  exact ((hw0.mul (Den.ite _ _)).add (hwU.mul (den_uniform1 d v))).add (hw1.mul (Den.ite _ _))

/-! ## One-coordinate laws on a grid, and the tent step -/

/-- `IsLaw d c`: `c` is a probability on `gridVals d` — nonnegative, zero off the grid, mass one.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def IsLaw (d : ℕ) (c : ℚ → ℚ) : Prop :=
  (∀ v, 0 ≤ c v) ∧ (∀ v, v ∉ gridVals d → c v = 0) ∧ ∑ v ∈ gridVals d, c v = 1

/-- A law's values are at most `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma IsLaw.le_one {d : ℕ} {c : ℚ → ℚ} (hc : IsLaw d c) (v : ℚ) : c v ≤ 1 := by
  by_cases hv : v ∈ gridVals d
  · rw [← hc.2.2]
    exact Finset.single_le_sum (fun u _ => hc.1 u) hv
  · rw [hc.2.1 v hv]; exact zero_le_one

/-- **The tent step preserves laws**: composing a law on `gridVals d'` with the tent law at mesh
`d` (`0 < d`) gives a law on `gridVals d`.
Source: none: infrastructure ([[bli-program]] §2.4, the kernel is stochastic)
Kind: L
Fidelity: n/a -/
lemma IsLaw.step {d' d : ℕ} (hd : 0 < d) {c : ℚ → ℚ} (hc : IsLaw d' c) :
    IsLaw d (fun v => ∑ v' ∈ gridVals d', c v' * tent1 d v' v) := by
  refine ⟨fun v => ?_, fun v hv => ?_, ?_⟩
  · exact Finset.sum_nonneg fun v' _ => mul_nonneg (hc.1 v') (tent1_nonneg d v' v)
  · exact Finset.sum_eq_zero fun v' _ => by rw [tent1_eq_zero_of_not_mem hd v' hv, mul_zero]
  · rw [Finset.sum_comm]
    calc ∑ v' ∈ gridVals d', ∑ v ∈ gridVals d, c v' * tent1 d v' v
        = ∑ v' ∈ gridVals d', c v' := by
          apply Finset.sum_congr rfl
          intro v' _
          rw [← Finset.mul_sum, tent1_sum_one hd, mul_one]
      _ = 1 := hc.2.2

/-- The point mass at `0` is a law on every grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isLaw_delta0 (d : ℕ) : IsLaw d fun u => if u = 0 then (1 : ℚ) else 0 := by
  refine ⟨fun v => by dsimp only; split_ifs <;> norm_num, fun v hv => ?_, ?_⟩
  · dsimp only; rw [if_neg]; rintro rfl; exact hv (zero_mem_gridVals d)
  · simpa using sum_gridVals_indicator (d := d) 1 0 (zero_mem_gridVals d)

/-- The point mass at `1` is a law on every grid with `0 < d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isLaw_delta1 {d : ℕ} (hd : 0 < d) : IsLaw d fun u => if u = 1 then (1 : ℚ) else 0 := by
  refine ⟨fun v => by dsimp only; split_ifs <;> norm_num, fun v hv => ?_, ?_⟩
  · dsimp only; rw [if_neg]; rintro rfl; exact hv (one_mem_gridVals hd)
  · simpa using sum_gridVals_indicator (d := d) 1 1 (one_mem_gridVals hd)

/-- The uniform law is a law (`0 < d`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isLaw_uniform1 {d : ℕ} (hd : 0 < d) : IsLaw d (uniform1 d) :=
  ⟨uniform1_nonneg d, fun _ hv => uniform1_eq_zero_of_not_mem hv, uniform1_sum_one hd⟩

/-! ## The chain constants: laws with controlled denominators -/

/-- **`chainDen 𝓜 m h`**: a common denominator for the horizon-`h` chain constants —
`d(m+1) + 1` at horizon `0`, times `d(m+k+1) · (d(m+k+2) + 1)` for each further step `k < h`.
Source: none: infrastructure (mandate E2(d): "the constants' bit-size bounded by a polynomial in
`h` and `log₂ d`")
Kind: D
Fidelity: n/a -/
def chainDen (𝓜 : Mesh) (m : ℕ) : ℕ → ℕ
  | 0 => 𝓜.d (m + 1) + 1
  | h + 1 => chainDen 𝓜 m h * (𝓜.d (m + h + 1) * (𝓜.d (m + h + 1 + 1) + 1))

/-- Unfolding at horizon `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma chainDen_zero (𝓜 : Mesh) (m : ℕ) : chainDen 𝓜 m 0 = 𝓜.d (m + 1) + 1 := rfl

/-- Unfolding at horizon `h+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma chainDen_succ (𝓜 : Mesh) (m h : ℕ) :
    chainDen 𝓜 m (h + 1) = chainDen 𝓜 m h * (𝓜.d (m + h + 1) * (𝓜.d (m + h + 1 + 1) + 1)) := rfl

/-- `chainDen` is at least `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_le_chainDen (𝓜 : Mesh) (m : ℕ) : ∀ h, 2 ≤ chainDen 𝓜 m h
  | 0 => by have := 𝓜.d_pos (m + 1); simp; omega
  | h + 1 => by
      rw [chainDen_succ]
      have ih := two_le_chainDen 𝓜 m h
      have h1 := 𝓜.d_pos (m + h + 1)
      have h2 := 𝓜.d_pos (m + h + 1 + 1)
      calc 2 ≤ chainDen 𝓜 m h := ih
        _ = chainDen 𝓜 m h * 1 := (mul_one _).symm
        _ ≤ chainDen 𝓜 m h * (𝓜.d (m + h + 1) * (𝓜.d (m + h + 1 + 1) + 1)) :=
          Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (by positivity))

/-- **`chainDen` is polynomial in the mesh**: if `d(m+k) ≤ D` for every `k ≤ h+1` then
`chainDen 𝓜 m h ≤ (D+1)^(2h+1)` — `O(h · log D)` bits.
Source: [[bli-program]] §3.4 ("constants of `O((m−k) log d)` bits"); mandate E2(d)
Kind: P
Fidelity: exact
Hyps: (a) the mesh bound `∀ k ≤ h+1, d(m+k) ≤ D` -/
lemma chainDen_le_pow (𝓜 : Mesh) (m : ℕ) (D : ℕ) :
    ∀ h, (∀ k, k ≤ h + 1 → 𝓜.d (m + k) ≤ D) → chainDen 𝓜 m h ≤ (D + 1) ^ (2 * h + 1)
  | 0, hD => by
      rw [chainDen_zero, Nat.mul_zero, Nat.zero_add, pow_one]
      exact Nat.succ_le_succ (hD 1 le_rfl)
  | h + 1, hD => by
      rw [chainDen_succ]
      have ih := chainDen_le_pow 𝓜 m D h fun k hk => hD k (by omega)
      have h1 : 𝓜.d (m + h + 1) ≤ D + 1 := by
        have := hD (h + 1) (by omega)
        rw [← Nat.add_assoc] at this
        omega
      have h2 : 𝓜.d (m + h + 1 + 1) + 1 ≤ D + 1 := by
        have := hD (h + 1 + 1) le_rfl
        rw [← Nat.add_assoc, ← Nat.add_assoc] at this
        omega
      calc chainDen 𝓜 m h * (𝓜.d (m + h + 1) * (𝓜.d (m + h + 1 + 1) + 1))
          ≤ (D + 1) ^ (2 * h + 1) * ((D + 1) * (D + 1)) :=
            Nat.mul_le_mul ih (Nat.mul_le_mul h1 h2)
        _ = (D + 1) ^ (2 * (h + 1) + 1) := by ring

/-- **The chain from a law is a law** on the day-`(m+h+1)` grid.
Source: none: infrastructure ([[bli-program]] §3.4)
Kind: L
Fidelity: n/a -/
lemma chainFrom_isLaw (𝓜 : Mesh) (m : ℕ) {μ : ℚ → ℚ} (hμ : IsLaw (𝓜.d (m + 1)) μ) :
    ∀ h, IsLaw (𝓜.d (m + h + 1)) (chainFrom 𝓜 m h μ)
  | 0 => hμ
  | h + 1 => by
      have ih := chainFrom_isLaw 𝓜 m hμ h
      exact ih.step (𝓜.d_pos _)

/-- **The chain constants have denominator `chainDen`**: from a start law that is a multiple of
`1/(d(m+1)+1)`, every horizon-`h` value is a multiple of `1 / chainDen 𝓜 m h`.
Source: [[bli-program]] §3.4 ("constants of `O((m−k) log d)` bits"); mandate E2(d)
Kind: P
Fidelity: exact
Hyps: (a) the start law's denominator -/
lemma chainFrom_den (𝓜 : Mesh) (m : ℕ) {μ : ℚ → ℚ} (hμ : ∀ v, Den (𝓜.d (m + 1) + 1) (μ v)) :
    ∀ (h : ℕ) (v : ℚ), Den (chainDen 𝓜 m h) (chainFrom 𝓜 m h μ v)
  | 0, v => hμ v
  | h + 1, v => by
      rw [chainFrom_succ, chainDen_succ]
      apply Den.sum
      intro v' hv'
      exact (chainFrom_den 𝓜 m hμ h v').mul (den_tent1_of_mem hv' v)

/-- **A new coordinate's marginal is a law** on the day-`(m+h+1)` grid (for `φ ∉ S m`, any `t`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coordMarg_isLaw {𝒮 : SmallIndex} (𝓜 : Mesh) (m : ℕ) (t : Table 𝒮 m) :
    ∀ (h : ℕ) (φ : ↥(𝒮.S (m + h + 1))), φ.1 ∉ 𝒮.S m →
      IsLaw (𝓜.d (m + h + 1)) (coordMarg 𝓜 m h t φ)
  | 0, φ, hφ => by
      have : coordMarg 𝓜 m 0 t φ = uniform1 (𝓜.d (m + 1)) := by
        funext v
        rw [coordMarg_zero]
        unfold tentCoord
        rw [dif_neg hφ]
      rw [this]
      exact isLaw_uniform1 (𝓜.d_pos _)
  | h + 1, φ, hφ => by
      by_cases hφ' : φ.1 ∈ 𝒮.S (m + h + 1)
      · have : coordMarg 𝓜 m (h + 1) t φ = fun v =>
            ∑ v' ∈ gridVals (𝓜.d (m + h + 1)),
              coordMarg 𝓜 m h t ⟨φ.1, hφ'⟩ v' * tent1 (𝓜.d (m + h + 1 + 1)) v' v := by
          funext v
          exact coordMarg_succ_of_mem t v hφ'
        rw [this]
        exact (coordMarg_isLaw 𝓜 m t h ⟨φ.1, hφ'⟩ hφ).step (𝓜.d_pos _)
      · have : coordMarg 𝓜 m (h + 1) t φ = uniform1 (𝓜.d (m + h + 1 + 1)) := by
          funext v
          exact coordMarg_succ_of_not_mem t v hφ'
        rw [this]
        exact isLaw_uniform1 (𝓜.d_pos _)

/-- **A new coordinate's marginal has denominator `chainDen`** (for `φ ∉ S m`, any `t`).
Source: [[bli-program]] §3.4; mandate E2(d)
Kind: P
Fidelity: exact
Hyps: (a) `φ ∉ S m` -/
lemma coordMarg_den {𝒮 : SmallIndex} (𝓜 : Mesh) (m : ℕ) (t : Table 𝒮 m) :
    ∀ (h : ℕ) (φ : ↥(𝒮.S (m + h + 1))) (v : ℚ), φ.1 ∉ 𝒮.S m →
      Den (chainDen 𝓜 m h) (coordMarg 𝓜 m h t φ v)
  | 0, φ, v, hφ => by
      rw [coordMarg_zero, chainDen_zero]
      unfold tentCoord
      rw [dif_neg hφ]
      exact den_uniform1 _ v
  | h + 1, φ, v, hφ => by
      rw [chainDen_succ]
      by_cases hφ' : φ.1 ∈ 𝒮.S (m + h + 1)
      · rw [coordMarg_succ_of_mem t v hφ']
        apply Den.sum
        intro v' hv'
        exact (coordMarg_den 𝓜 m t h ⟨φ.1, hφ'⟩ v' hφ).mul (den_tent1_of_mem hv' v)
      · rw [coordMarg_succ_of_not_mem t v hφ']
        exact (den_uniform1 _ v).mono ((dvd_mul_left _ _).mul_left _)

/-! ## The constants of a term: numerator and denominator bounds -/

/-- `ConstsBounded D e`: every rational constant `const q` of `e` has `q.den ≤ D` and `|q.num| ≤ D`.
Source: none: infrastructure (mandate E2(d), "the constants' bit-size")
Kind: D
Fidelity: n/a -/
def ConstsBounded (D : ℕ) : EF → Prop
  | .price _ _ => True
  | .const q => q.den ≤ D ∧ q.num.natAbs ≤ D
  | .add a b => ConstsBounded D a ∧ ConstsBounded D b
  | .mul a b => ConstsBounded D a ∧ ConstsBounded D b
  | .max a b => ConstsBounded D a ∧ ConstsBounded D b
  | .safeRecip a => ConstsBounded D a
  | .var _ => True
  | .letE x b => ConstsBounded D x ∧ ConstsBounded D b

/-- A probability that is a multiple of `1/N` (`0 < N`) has denominator `≤ N` and numerator `≤ N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma num_den_le_of_den {N : ℕ} (hN : 0 < N) {q : ℚ} (hq : Den N q) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    q.den ≤ N ∧ q.num.natAbs ≤ N := by
  obtain ⟨z, hz⟩ := hq
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq' : q = (z : ℚ) / ((N : ℤ) : ℚ) := by
    push_cast
    rw [← hz]
    field_simp
  have hdvd : (q.den : ℤ) ∣ (N : ℤ) := by
    rw [hq', ← Rat.divInt_eq_div]
    exact Rat.den_dvd z N
  have hden : q.den ≤ N := Nat.le_of_dvd hN (Int.natCast_dvd_natCast.mp hdvd)
  refine ⟨hden, ?_⟩
  have hnum : (q.num : ℚ) = q * q.den := by
    have := Rat.num_div_den q
    rwa [div_eq_iff (by positivity)] at this
  have hle : (q.num : ℚ) ≤ q.den := by
    rw [hnum]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) h1
  have h2 : q.num ≤ (q.den : ℤ) := by exact_mod_cast hle
  have h3 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  omega

/-- The scaffolding constants `−1, 0, 1, 2` are bounded by any `D ≥ 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_small {D : ℕ} (hD : 2 ≤ D) :
    ConstsBounded D (.const (-1)) ∧ ConstsBounded D (.const 0) ∧ ConstsBounded D (.const 1) ∧
      ConstsBounded D (.const 2) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp <;> omega

section Consts

variable {D : ℕ} (hD : 2 ≤ D)
include hD

/-- Constants of `negE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_negE {a : EF} (ha : ConstsBounded D a) : ConstsBounded D (negE a) :=
  ⟨(constsBounded_small hD).1, ha⟩

/-- Constants of `subE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_subE {a b : EF} (ha : ConstsBounded D a) (hb : ConstsBounded D b) :
    ConstsBounded D (subE a b) :=
  ⟨ha, constsBounded_negE hD hb⟩

/-- Constants of `minE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_minE {a b : EF} (ha : ConstsBounded D a) (hb : ConstsBounded D b) :
    ConstsBounded D (minE a b) :=
  constsBounded_negE hD ⟨constsBounded_negE hD ha, constsBounded_negE hD hb⟩

/-- Constants of `clampE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_clampE {a : EF} (ha : ConstsBounded D a) : ConstsBounded D (clampE a) :=
  ⟨(constsBounded_small hD).2.1, constsBounded_minE hD (constsBounded_small hD).2.2.1 ha⟩

/-- Constants of `absE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_absE {a : EF} (ha : ConstsBounded D a) : ConstsBounded D (absE a) :=
  ⟨ha, constsBounded_negE hD ha⟩

/-- Constants of the three tent weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_weights {x : EF} (hx : ConstsBounded D x) :
    ConstsBounded D (w0E x) ∧ ConstsBounded D (wUE x) ∧ ConstsBounded D (w1E x) := by
  obtain ⟨hneg, h₀, h₁, h₂⟩ := constsBounded_small hD
  have hcl : ConstsBounded D (.mul (.const 2) (clampE x)) := ⟨h₂, constsBounded_clampE hD hx⟩
  exact ⟨⟨h₀, constsBounded_subE hD h₁ hcl⟩,
    constsBounded_subE hD h₁ (constsBounded_absE hD (constsBounded_subE hD hcl h₁)),
    ⟨h₀, constsBounded_subE hD hcl h₁⟩⟩

/-- Constants of `mix3E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_mix3E {x : EF} (hx : ConstsBounded D x) {c0 cU c1 : ℚ}
    (hc0 : c0.den ≤ D ∧ c0.num.natAbs ≤ D) (hcU : cU.den ≤ D ∧ cU.num.natAbs ≤ D)
    (hc1 : c1.den ≤ D ∧ c1.num.natAbs ≤ D) : ConstsBounded D (mix3E x c0 cU c1) := by
  obtain ⟨h0, hU, h1⟩ := constsBounded_weights hD hx
  exact ⟨⟨⟨h0, hc0⟩, ⟨hU, hcU⟩⟩, ⟨h1, hc1⟩⟩

/-- Constants of `prodList`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constsBounded_prodList : ∀ l : List EF, (∀ e ∈ l, ConstsBounded D e) →
    ConstsBounded D (prodList l)
  | [], _ => (constsBounded_small hD).2.2.1
  | e :: l, h => ⟨h e (List.mem_cons_self ..),
      constsBounded_prodList l fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

end Consts

variable {𝒮 : SmallIndex}

/-- **E2(d), the constants' size.** Every rational constant of `tentExpr 𝓜 m h Q` has denominator
`≤ chainDen 𝓜 m h` and `|numerator| ≤ chainDen 𝓜 m h`: the chain constants are probabilities
(`chainFrom_isLaw`, `coordMarg_isLaw`) with denominator dividing `chainDen` (`chainFrom_den`,
`coordMarg_den`); the scaffolding constants are `−1, 0, 1, 2`. With `chainDen_le_pow` this is the
program's "constants of `O(h · log d)` bits", for every `Q` (on the grid or not).
Source: [[bli-program]] §3.4 ("constants of `O((m−k) log d)` bits"); mandate E2(d)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tentExpr_constsBounded (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    ConstsBounded (chainDen 𝓜 m h) (tentExpr 𝓜 m h Q) := by
  have hD := two_le_chainDen 𝓜 m h
  have hN : 0 < chainDen 𝓜 m h := by omega
  unfold tentExpr
  apply constsBounded_prodList hD
  intro e he
  rw [List.mem_map] at he
  obtain ⟨φ, -, rfl⟩ := he
  unfold coordExpr
  split_ifs with hφ
  · have hl0 := chainFrom_isLaw 𝓜 m (isLaw_delta0 _) h
    have hlU := chainFrom_isLaw 𝓜 m (isLaw_uniform1 (𝓜.d_pos _)) h
    have hl1 := chainFrom_isLaw 𝓜 m (isLaw_delta1 (𝓜.d_pos _)) h
    refine constsBounded_mix3E hD (x := .price φ.1 m) trivial ?_ ?_ ?_
    · exact num_den_le_of_den hN (chainFrom_den 𝓜 m (fun v => Den.ite _ _) h _) (hl0.1 _)
        (hl0.le_one _)
    · exact num_den_le_of_den hN (chainFrom_den 𝓜 m (fun v => den_uniform1 _ v) h _) (hlU.1 _)
        (hlU.le_one _)
    · exact num_den_le_of_den hN (chainFrom_den 𝓜 m (fun v => Den.ite _ _) h _) (hl1.1 _)
        (hl1.le_one _)
  · have hl := coordMarg_isLaw 𝓜 m (fun _ => 0) h φ hφ
    exact num_den_le_of_den hN (coordMarg_den 𝓜 m _ h φ _ hφ) (hl.1 _) (hl.le_one _)

/-! ## Codes: Mathlib's `Encodable ℚ` and FAF's digit meter -/

/-- Mathlib's code of an integer is at most `2·|z| + 1` (`Equiv.intEquivNat`: `2n` / `2n+1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma encode_int_le (z : ℤ) : Encodable.encode z ≤ 2 * z.natAbs + 1 := by
  cases z with
  | ofNat n =>
      show 2 * n ≤ 2 * n + 1
      omega
  | negSucc n =>
      show 2 * n + 1 ≤ 2 * (n + 1) + 1
      omega

/-- Mathlib's code of a rational is `Nat.pair (encode num) den`.
Source: none: infrastructure (Mathlib `Rat.instEncodable`)
Kind: L
Fidelity: n/a -/
lemma encode_rat_eq (q : ℚ) : Encodable.encode q = Nat.pair (Encodable.encode q.num) q.den := by
  obtain ⟨n, d, hd, hc⟩ := q
  rfl

/-- **The code of a bounded rational is small**: `den ≤ D` and `|num| ≤ D` give
`encode q < (2D + 2)²`.
Source: none: infrastructure (mandate E2(d))
Kind: L
Fidelity: n/a -/
lemma encode_rat_lt {D : ℕ} {q : ℚ} (hd : q.den ≤ D) (hn : q.num.natAbs ≤ D) :
    Encodable.encode q < (2 * D + 2) ^ 2 := by
  rw [encode_rat_eq]
  have hz := encode_int_le q.num
  calc Nat.pair (Encodable.encode q.num) q.den
      < (max (Encodable.encode q.num) q.den + 1) ^ 2 := Nat.pair_lt_max_add_one_sq _ _
    _ ≤ (2 * D + 2) ^ 2 := by
        apply Nat.pow_le_pow_left
        have : max (Encodable.encode q.num) q.den ≤ 2 * D + 1 := max_le (by omega) (by omega)
        omega

/-- A token below `4^K` has at most `K` base-4 digits (FAF's `natDigits4`).
Source: none: infrastructure (FAF `Framework/Criterion.lean` `natDigits4`)
Kind: L
Fidelity: n/a -/
lemma length_natDigits4_le : ∀ (K n : ℕ), n < 4 ^ K → (natDigits4 n).length ≤ K
  | _, 0, _ => by simp [natDigits4]
  | 0, n + 1, h => by simp at h
  | K + 1, n + 1, h => by
      rw [natDigits4, List.length_cons]
      have hlt : (n + 1) / 4 < 4 ^ K := by
        rw [pow_succ, mul_comm] at h
        exact Nat.div_lt_of_lt_mul h
      exact Nat.succ_le_succ (length_natDigits4_le K ((n + 1) / 4) hlt)

/-- **FAF's digit meter of a token stream**: if every token is below `4^K`, the digitized stream
(`digitize`: one self-delimiting block per token) has length at most `(K+1) · (number of tokens)`.
Source: none: infrastructure (FAF `Framework/Criterion.lean` `digitize`, `tokenBlock`)
Kind: L
Fidelity: n/a -/
lemma length_digitize_le (K : ℕ) : ∀ l : List ℕ, (∀ t ∈ l, t < 4 ^ K) →
    (digitize l).length ≤ (K + 1) * l.length
  | [], _ => by simp [digitize]
  | t :: l, h => by
      have ih := length_digitize_le K l fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
      have ht := length_natDigits4_le K t (h t (List.mem_cons_self ..))
      show (tokenBlock t ++ digitize l).length ≤ (K + 1) * (l.length + 1)
      rw [List.length_append, tokenBlock, List.length_append, List.length_singleton, Nat.mul_succ]
      omega

/-- **The tokens of a closed same-day term are small**: with `8 < N`, the day `n < N`, every leaf
code `< N` and `(2D+2)² ≤ N`, every token of `e.serialize` is `< N` (tags are `≤ 8`; the
constants' codes are below `(2D+2)²` by `encode_rat_lt`).
Source: none: infrastructure (FAF `EF.serialize`)
Kind: L
Fidelity: n/a -/
lemma token_lt_of_priceLeavesIn {A : Finset Sentence} {n N D : ℕ} (h8 : 8 < N)
    (hA : ∀ φ ∈ A, Encodable.encode φ < N) (hn : n < N) (hD : (2 * D + 2) ^ 2 ≤ N) :
    ∀ e : EF, PriceLeavesIn A n e → ConstsBounded D e → ∀ t ∈ e.serialize, t < N
  | .price φ k, hp, _, t, ht => by
      obtain ⟨hφ, rfl⟩ := hp
      simp only [EF.serialize, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · omega
      · exact hA φ hφ
      · exact hn
  | .const q, _, hc, t, ht => by
      simp only [EF.serialize, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · omega
      · exact lt_of_lt_of_le (encode_rat_lt hc.1 hc.2) hD
  | .add a b, ⟨ha, hb⟩, ⟨ca, cb⟩, t, ht => by
      simp only [EF.serialize, List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | rfl
      · exact token_lt_of_priceLeavesIn h8 hA hn hD a ha ca t ht
      · exact token_lt_of_priceLeavesIn h8 hA hn hD b hb cb t ht
      · omega
  | .mul a b, ⟨ha, hb⟩, ⟨ca, cb⟩, t, ht => by
      simp only [EF.serialize, List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | rfl
      · exact token_lt_of_priceLeavesIn h8 hA hn hD a ha ca t ht
      · exact token_lt_of_priceLeavesIn h8 hA hn hD b hb cb t ht
      · omega
  | .max a b, ⟨ha, hb⟩, ⟨ca, cb⟩, t, ht => by
      simp only [EF.serialize, List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | rfl
      · exact token_lt_of_priceLeavesIn h8 hA hn hD a ha ca t ht
      · exact token_lt_of_priceLeavesIn h8 hA hn hD b hb cb t ht
      · omega
  | .safeRecip _, hp, _, _, _ => hp.elim
  | .var _, hp, _, _, _ => hp.elim
  | .letE _ _, hp, _, _, _ => hp.elim

/-- **E2(d), the bit bound in FAF's digit meter, on the serialization.** If `4^K` exceeds the day
`m`, every code of a day-`m` small sentence, and `(2·chainDen 𝓜 m h + 2)²`, then the digitized
token stream of `(tentExpr 𝓜 m h Q).serialize` (`digitize`: one self-delimiting base-4 block per
token, three bits per digit) has length at most `(K+1) · 3 · (88·|S (m+h+1)| + 1)`. The constants
contribute through `K` alone (`tentExpr_constsBounded`, `encode_rat_lt`); with `chainDen_le_pow`,
`K` is `O(h · log d)` plus the size of the day-`m` sentence codes (`bli-found`'s business).
**This is the digit stream of `serialize`, not the stream FAF's class reads** (audit r2
adversarial §2.1): `strategyOfOutput` contracts sentence blocks (`unRpn`) before deserialization,
so a machine's output must be an `unRpn`-preimage — FAF's `escExpand` of this stream, which costs
exactly `8·|S m|` digits more (`Escape.lean`: `unRpn_escExpand_tentExpr`,
`tentExpr_escExpand_digitize_length_le`). Constants and tags are metered identically in both; the
leaves are metered by their Gödel codes (`hA`, the escape spelling), not by the canonical run
`rpn φ` (audit r2 fidelity §3.1).
Source: [[bli-program]] §3.4 (size `O(|S_m| · poly(m, log d))`); mandate E2(d) ("with the
constants' bit-size bounded by a polynomial in `h` and `log₂ (𝓜.d (m+h))`")
Kind: C
Fidelity: variant: the digit stream of `serialize`; FAF's class reads an `unRpn`-preimage
(`escExpand`, `+ 8·|S m|` digits, `Escape.lean`); leaves metered by Gödel code (`hA`), the
canonical-run cost not stated
Hyps: (a) `4^K` above the day, the leaf codes and `(2·chainDen + 2)²` (scope hypotheses on the
free `K`) -/
theorem tentExpr_digitize_length_le (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) (K : ℕ)
    (hA : ∀ φ ∈ 𝒮.S m, Encodable.encode φ < 4 ^ K) (hm : m < 4 ^ K)
    (hD : (2 * chainDen 𝓜 m h + 2) ^ 2 < 4 ^ K) :
    (digitize (tentExpr 𝓜 m h Q).serialize).length ≤
      (K + 1) * (3 * (88 * (𝒮.S (m + h + 1)).card + 1)) := by
  have h8 : 8 < 4 ^ K := by
    have h2 := two_le_chainDen 𝓜 m h
    have h36 : 6 ^ 2 ≤ (2 * chainDen 𝓜 m h + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    norm_num at h36
    omega
  calc (digitize (tentExpr 𝓜 m h Q).serialize).length
      ≤ (K + 1) * (tentExpr 𝓜 m h Q).serialize.length :=
        length_digitize_le K _ (token_lt_of_priceLeavesIn h8 hA hm hD.le _
          (tentExpr_priceLeavesIn 𝓜 m h Q) (tentExpr_constsBounded 𝓜 m h Q))
    _ ≤ (K + 1) * (3 * (88 * (𝒮.S (m + h + 1)).card + 1)) :=
        Nat.mul_le_mul_left _ (tentExpr_size_le 𝓜 m h Q)

/-- **The digit bound with the explicit exponent** `K = log₄(max(m, max code on S m,
(2·chainDen + 2)²)) + 1` — on the serialization (see `tentExpr_digitize_length_le`: FAF's class
reads its `escExpand`, `+ 8·|S m|` digits).
Source: [[bli-program]] §3.4; mandate E2(d)
Kind: C
Fidelity: variant: as `tentExpr_digitize_length_le` (the stream of `serialize`; leaves by Gödel code)
Hyps: (a) none -/
theorem tentExpr_digitize_length_le_log (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    (digitize (tentExpr 𝓜 m h Q).serialize).length ≤
      (Nat.log 4 (max (max m ((𝒮.S m).sup Encodable.encode)) ((2 * chainDen 𝓜 m h + 2) ^ 2)) + 2) *
        (3 * (88 * (𝒮.S (m + h + 1)).card + 1)) := by
  set M := max (max m ((𝒮.S m).sup Encodable.encode)) ((2 * chainDen 𝓜 m h + 2) ^ 2) with hM
  have hlt : M < 4 ^ (Nat.log 4 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have hA : ∀ φ ∈ 𝒮.S m, Encodable.encode φ < 4 ^ (Nat.log 4 M + 1) := fun φ hφ =>
    lt_of_le_of_lt ((Finset.le_sup hφ).trans ((le_max_right _ _).trans (le_max_left _ _))) hlt
  have hm : m < 4 ^ (Nat.log 4 M + 1) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hlt
  have hD : (2 * chainDen 𝓜 m h + 2) ^ 2 < 4 ^ (Nat.log 4 M + 1) :=
    lt_of_le_of_lt (le_max_right _ _) hlt
  exact tentExpr_digitize_length_le 𝓜 m h Q (Nat.log 4 M + 1) hA hm hD

/-- **The constants' digit budget is polynomial in `h` and `log d`**: under the mesh bound
`d(m+k) ≤ D` for `k ≤ h+1`, `(2·chainDen 𝓜 m h + 2)² < 4^((4h+2)·(log₄(D+1)+1) + 2)`.
Source: [[bli-program]] §3.4 ("constants of `O((m−k) log d)` bits"); mandate E2(d)
Kind: C
Fidelity: exact
Hyps: (a) the mesh bound -/
lemma chainDen_sq_lt_pow (𝓜 : Mesh) (m h D : ℕ) (hD : ∀ k, k ≤ h + 1 → 𝓜.d (m + k) ≤ D) :
    (2 * chainDen 𝓜 m h + 2) ^ 2 < 4 ^ ((4 * h + 2) * (Nat.log 4 (D + 1) + 1) + 2) := by
  have hc := chainDen_le_pow 𝓜 m D h hD
  have h1 : D + 1 < 4 ^ (Nat.log 4 (D + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : (D + 1) ^ (4 * h + 2) < (4 ^ (Nat.log 4 (D + 1) + 1)) ^ (4 * h + 2) :=
    Nat.pow_lt_pow_left h1 (by omega)
  have h3 : 2 * chainDen 𝓜 m h + 2 ≤ 4 * (D + 1) ^ (2 * h + 1) := by
    have := two_le_chainDen 𝓜 m h
    omega
  calc (2 * chainDen 𝓜 m h + 2) ^ 2 ≤ (4 * (D + 1) ^ (2 * h + 1)) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = 16 * (D + 1) ^ (4 * h + 2) := by ring
    _ < 16 * (4 ^ (Nat.log 4 (D + 1) + 1)) ^ (4 * h + 2) := by omega
    _ = 4 ^ ((4 * h + 2) * (Nat.log 4 (D + 1) + 1) + 2) := by
        rw [pow_add, ← pow_mul, mul_comm (Nat.log 4 (D + 1) + 1)]
        ring

/-- **E2(d) in the mandate's form**: under a mesh bound `D`, any `K ≥ (4h+2)·(log₄(D+1)+1) + 2`
that also covers the day and the day-`m` sentence codes bounds the digitized token stream of the
serialization by `(K+1) · 3 · (88·|S (m+h+1)| + 1)` — `|S| · (c₁ + c₂ · K)` with `K` polynomial
in `h` and `log d`. The stream FAF's class reads is its `escExpand`, `+ 8·|S m|` digits
(`tentExpr_escExpand_digitize_length_le_poly`, `Escape.lean`); that is the statement for
`bli-assemble` to consume.
Source: mandate E2(d) ("`serialize.length ≤ |S_{m+h}| · (c₁ + c₂ · (bits of the constants))` with
the constants' bit-size bounded by a polynomial in `h` and `log₂ (𝓜.d (m+h))`")
Kind: C
Fidelity: variant: as `tentExpr_digitize_length_le` (the stream of `serialize`; leaves by Gödel code)
Hyps: (a) the mesh bound; `K` above the polynomial, the day and the leaf codes -/
theorem tentExpr_digitize_length_le_poly (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) (D : ℕ)
    (hD : ∀ k, k ≤ h + 1 → 𝓜.d (m + k) ≤ D) (K : ℕ)
    (hK : (4 * h + 2) * (Nat.log 4 (D + 1) + 1) + 2 ≤ K)
    (hA : ∀ φ ∈ 𝒮.S m, Encodable.encode φ < 4 ^ K) (hm : m < 4 ^ K) :
    (digitize (tentExpr 𝓜 m h Q).serialize).length ≤
      (K + 1) * (3 * (88 * (𝒮.S (m + h + 1)).card + 1)) :=
  tentExpr_digitize_length_le 𝓜 m h Q K hA hm
    (lt_of_lt_of_le (chainDen_sq_lt_pow 𝓜 m h D hD) (Nat.pow_le_pow_right (by norm_num) hK))

end Cleanroom.Bli.BliSuperbelief
