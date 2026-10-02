import Cleanroom.Found.DefLattice.Expert
import Mathlib.Data.Finset.Max

/-!
# Value: menus, the followed strategy, argmax and the blended forms

Package `def-lattice`, file 3 of the definitions module (T4). The instrumental deference notion:

* `Menu k` — an e.d. sequence of finite menus `O^0_n, …, O^k_n` (`k+1` options, so the menu is
  nonempty and the least-index argmax is total);
* `Menu.quote`, `Menu.maxQuote`, `Menu.argmax` — the expert's quotes `m^j_n := E*(O^j_n)`, the
  maximum `M_n`, and the **least index** attaining it (`argmax_attains`, `argmax_le`);
* `Follows DP E M S` — "`Ŝ_n` is `O^{j*(n)}_n` in every consistent world": the followed
  strategy as a LUV whose world value is that of the selected option (never a syntactic
  equality — the corpus's `Ŝ_n` is a *different formula* with the same world value);
* `Value P DP E` — for every e.d. world-valued menu and every e.d. `S` following the expert's
  argmax, `E^H_n(Ŝ_n) ≳ₙ E^H_n(O^i_n)` for every fixed `i`;
* `BlendValue P DP E blend` — the same with the followed strategy replaced by a blend of the
  options weighted by a function of the quotes (`softmaxBlend`, `rampBlend` as instances):
  the "`δ`-hedged Value" that always carries its qualifier.
-/

namespace Cleanroom.Found.DefLattice

open LogicalInduction Filter Topology Finset

noncomputable section

/-! ## Menus -/

/-- **A menu sequence:** `k+1` e.d. option sequences `O j`, the corpus's e.d. finite menus
`𝒪_n = {O^1_n, …, O^k_n}` of bounded bets (`[0,1]`-LUVs here). `k+1` keeps the menu nonempty
so the least-index argmax is total. World-valuedness of the options (the corpus's "LUV" —
a formula that names a unique real) is the separate predicate `Menu.Valued`, carried in
`Value`'s quantifier.
Source: [[deference-notions]] §Shared apparatus; v6 §1 preamble (lines 150–160)
Kind: D
Fidelity: exact (`[0,1]`-LUVs; the corpus's `[a,b]`-LUVs are affine images) -/
structure Menu (k : ℕ) where
  /-- the options, indexed by `Fin (k+1)` and the day -/
  O : Fin (k + 1) → ℕ → LUV
  /-- every option sequence is efficiently describable -/
  codes : ∀ j, LUV.MachineThresholdCodeSeq (O j)

namespace Menu

variable {k : ℕ} {DP : DeductiveProcess}

/-- Every completed-theory world values every option of every day.
Source: [[setting-and-notation]] §LUV
Kind: D
Fidelity: exact -/
def Valued (DP : DeductiveProcess) (M : Menu k) : Prop :=
  ∀ j, Cleanroom.Found.DefLattice.Valued DP (M.O j)

/-- The expert's quote of option `j` on day `n`: `m^j_n := E*(O^j_n)`.
Source: [[deference-notions]] §Shared apparatus
Kind: D
Fidelity: exact -/
abbrev quote (E : Expert DP) (M : Menu k) (j : Fin (k + 1)) (n : ℕ) : ℝ :=
  E.estimate (M.O j) n

/-- The maximal quote `M_n := max_j m^j_n`.
Source: [[deference-notions]] §Shared apparatus
Kind: D
Fidelity: exact -/
def maxQuote (E : Expert DP) (M : Menu k) (n : ℕ) : ℝ :=
  univ.sup' univ_nonempty (fun j => M.quote E j n)

/-- Every quote is at most the maximal quote (the corpus's (F2): `M_n ≥ m^i_n`).
Source: v6 §1 (F2)
Kind: L
Fidelity: exact -/
lemma quote_le_maxQuote (E : Expert DP) (M : Menu k) (j : Fin (k + 1)) (n : ℕ) :
    M.quote E j n ≤ M.maxQuote E n :=
  le_sup' (fun j => M.quote E j n) (mem_univ j)

/-- The indices attaining the maximal quote.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def attaining (E : Expert DP) (M : Menu k) (n : ℕ) : Finset (Fin (k + 1)) := by
  classical
  exact univ.filter (fun j => M.quote E j n = M.maxQuote E n)

/-- Some index attains the maximum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma attaining_nonempty (E : Expert DP) (M : Menu k) (n : ℕ) :
    (M.attaining E n).Nonempty := by
  classical
  obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' (univ_nonempty (α := Fin (k + 1)))
    (fun j => M.quote E j n)
  exact ⟨j, by simp [attaining, maxQuote, hj]⟩

/-- **The least-index argmax** `j*(n)`: the least `j` with `m^j_n = M_n` (the corpus's
"least index; any ledger-decided tie-break" — the generalization to other ledger-decided rules
is a remark, not a second definition; [[ledger-decided-tie-breaks]]).
Source: [[deference-notions]] §Shared apparatus; v6 §1 preamble
Kind: D
Fidelity: exact -/
def argmax (E : Expert DP) (M : Menu k) (n : ℕ) : Fin (k + 1) :=
  (M.attaining E n).min' (M.attaining_nonempty E n)

/-- The argmax attains the maximum: `m^{j*(n)}_n = M_n`.
Source: v6 §1 (the selection identity's first half)
Kind: L
Fidelity: exact -/
lemma argmax_attains (E : Expert DP) (M : Menu k) (n : ℕ) :
    M.quote E (M.argmax E n) n = M.maxQuote E n := by
  classical
  have h := min'_mem (M.attaining E n) (M.attaining_nonempty E n)
  unfold argmax
  simpa [attaining] using h

/-- The argmax is the least attaining index.
Source: [[deference-notions]] §Shared apparatus ("least index")
Kind: L
Fidelity: exact -/
lemma argmax_le (E : Expert DP) (M : Menu k) (n : ℕ) (j : Fin (k + 1))
    (hj : M.quote E j n = M.maxQuote E n) : M.argmax E n ≤ j := by
  classical
  exact min'_le _ _ (by simp [attaining, hj])

/-- The argmax is `0` exactly when option `0` attains the maximum (the least index wins ties).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_eq_zero_iff (E : Expert DP) (M : Menu k) (n : ℕ) :
    M.argmax E n = 0 ↔ M.quote E 0 n = M.maxQuote E n := by
  constructor
  · intro h
    rw [← h]
    exact M.argmax_attains E n
  · intro h
    exact le_antisymm (M.argmax_le E n 0 h) (Fin.zero_le _)

/-- On a two-option menu the maximal quote is the max of the two quotes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma maxQuote_two (E : Expert DP) (M : Menu 1) (n : ℕ) :
    M.maxQuote E n = max (M.quote E 0 n) (M.quote E 1 n) := by
  apply le_antisymm
  · obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' (univ_nonempty (α := Fin 2))
      (fun j => M.quote E j n)
    unfold maxQuote
    rw [hj]
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (M.quote_le_maxQuote E 0 n) (M.quote_le_maxQuote E 1 n)

/-- **The two-option argmax:** option `0` is followed iff its quote is at least option `1`'s
(ties toward `0` — the least-index rule; DDB's Lemma 7.1 chooses `s` so that no tie occurs,
`TwoOptionFinite.lean`).
Source: [[two-option-value-iff-total-trust]] §Setting ("tie broken toward `X`")
Kind: L
Fidelity: exact -/
lemma argmax_two (E : Expert DP) (M : Menu 1) (n : ℕ) :
    M.argmax E n = if M.quote E 1 n ≤ M.quote E 0 n then 0 else 1 := by
  by_cases h : M.quote E 1 n ≤ M.quote E 0 n
  · rw [if_pos h]
    rw [argmax_eq_zero_iff, maxQuote_two]
    exact (max_eq_left h).symm
  · rw [if_neg h]
    have h0 : M.argmax E n ≠ 0 := by
      rw [Ne, argmax_eq_zero_iff, maxQuote_two, max_eq_right (le_of_lt (not_le.mp h))]
      exact ne_of_lt (not_le.mp h)
    revert h0
    generalize M.argmax E n = a
    intro h0
    fin_cases a
    · exact absurd rfl h0
    · rfl

end Menu

/-! ## The followed strategy and Value -/

/-- **The followed strategy** — "`Ŝ_n` is `O^{j*(n)}_n` in every consistent world": `S n` takes,
in every completed-theory world, the value the selected option takes there. This is a
*value* clause, never a syntactic identity: the corpus's `Ŝ_n` is a different e.d. formula
(it case-splits on the expert's readable quotes) with the same world value, and a syntactic
`S n = M.O (argmax) n` would leave no e.c. `S` for a quote-referencing selection. The
selection is the ledger-decided least-index rule of `Menu.argmax`.
Source: [[deference-notions]] §Shared apparatus (`Ŝ_n := O^{j*(n)}_n`, "the option the expert
picks, evaluated at the world that obtains"); [[ledger-decided-tie-breaks]]
Kind: D
Fidelity: exact (reflection form) -/
def Follows {k : ℕ} (DP : DeductiveProcess) (E : Expert DP) (M : Menu k) (S : ℕ → LUV) :
    Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x,
    v.ValuesAt (M.O (M.argmax E n) n) x → v.ValuesAt (S n) x

/-- **Value** — quoted from [[deference-notions]] §Value: "for every e.d. sequence of finite
menus `𝒪_n` and every fixed index `i`: `E^H_n(Ŝ_n) ≳ₙ E^H_n(O^i_n)`" — "let the expert pick"
is weakly preferred, by the novice's own current lights, to committing to any fixed option.
Over FAF: for every `k`, every e.d. world-valued menu `M : Menu k`, every e.d. `S` following
the expert's least-index argmax (`Follows`), and every `i`. Quantified over **all** `k` and
all menus (a fixed-menu Value would make the two-option identity a squeeze).
⚠ Scope (the page's own note, verbatim in one sentence): "For inductor-experts, *unconditional*
argmax Value is **false**: selection-referencing menus (Death-in-Damascus-type; Counterfactual
Mugging is the same family) make 'follow the expert' lose by every light" — the scope condition
(conditional-stability, H3) and the punishing menu are `def-argmax-value`'s; this package only
*defines* the unconditional predicate. "Value" unqualified always means this argmax form; the
blended form is `BlendValue` and always carries its qualifier.
Source: [[deference-notions]] §Value and its ⚠ 2026-07-25 scope note; v6 §1 table
Kind: D
Fidelity: exact (unconditional; the scoped predicate is `def-argmax-value`'s) -/
def Value (P : History) (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (k : ℕ) (M : Menu k), M.Valued DP → ∀ S : ℕ → LUV, LUV.MachineThresholdCodeSeq S →
    Follows DP E M S → ∀ i, (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n)

/-! ## Blended (δ-hedged) Value -/

/-- **The blended-strategy quote package:** `S n` is valued, within a vanishing `slack`, at
`∑ j, blend (m_n) j · x_j` whenever the options are valued at `x_j`, where `m_n` is the vector
of the expert's quotes. The blend enters only as a reflected LUV value, never as a trade
weight (finding F5: `EF` has no `exp`, so softmax weights are not expressible features).
Source: [[soft-self-endorsement]] §The soft strategy (`T_{δ,n} := ∑_j θ_j O^j_n`); mandate T4
Kind: D
Fidelity: variant: within FAF's vanishing slack (design decision 3) -/
structure BlendQuote {k : ℕ} (DP : DeductiveProcess) (E : Expert DP) (M : Menu k)
    (blend : (Fin (k + 1) → ℝ) → Fin (k + 1) → ℝ) (S : ℕ → LUV) where
  /-- the blended strategy is efficiently describable -/
  codes : LUV.MachineThresholdCodeSeq S
  /-- the per-day reflection slack -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- `S n` is valued within `slack n` of the blend of the options' values -/
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x : Fin (k + 1) → ℝ,
    (∀ j, v.ValuesAt (M.O j n) (x j)) →
      ∃ z, v.ValuesAt (S n) z ∧
        |z - ∑ j, blend (fun j => M.quote E j n) j * x j| ≤ slack n

/-- **Blended ("δ-hedged") Value:** `Value` with the followed strategy replaced by a blend of
the options weighted by `blend` applied to the expert's quotes: for every e.d. world-valued
menu and every e.d. `S` reflecting the blend (`BlendQuote`), `E^H_n(S_n) ≳ₙ E^H_n(O^i_n)`.
A strictly weaker notion than `Value`; it must always carry its qualifier ("δ-hedged Value",
[[deference-notions]] §Terminological default 2026-07-23). Instances: `softmaxBlend` (v1's
route, root-deference-064), `rampBlend` ([[soft-self-endorsement]]).
Source: [[deference-notions]] §Value (terminological default); [[soft-self-endorsement]]
§δ-hedged Value; v1 §3 via root-deference-064
Kind: D
Fidelity: exact (blend as reflected value) -/
def BlendValue (P : History) (DP : DeductiveProcess) (E : Expert DP)
    (blend : ∀ {k : ℕ}, (Fin (k + 1) → ℝ) → Fin (k + 1) → ℝ) : Prop :=
  ∀ (k : ℕ) (M : Menu k), M.Valued DP → ∀ S : ℕ → LUV, BlendQuote DP E M blend S →
    ∀ i, (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n)

/-- The softmax blend `θ_j = exp(m_j/δ) / ∑_i exp(m_i/δ)` (v1's route to Value; not an
expressible feature — finding F5). For `0 < δ`; at `δ = 0` (Lean: `x / 0 = 0`) it is the
uniform blend `1/(k+1)`, so any headline at a fixed width takes `0 < δ`.
Source: v1 §3 via root-deference-064; mandate T4
Kind: D
Fidelity: exact -/
def softmaxBlend (δ : ℚ) {k : ℕ} (m : Fin (k + 1) → ℝ) (j : Fin (k + 1)) : ℝ :=
  Real.exp (m j / δ) / ∑ i, Real.exp (m i / δ)

/-- The softmax denominator is positive (no junk division).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma softmaxBlend_denom_pos (δ : ℚ) {k : ℕ} (m : Fin (k + 1) → ℝ) :
    0 < ∑ i, Real.exp (m i / δ) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/-- The softmax weights sum to `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma softmaxBlend_sum (δ : ℚ) {k : ℕ} (m : Fin (k + 1) → ℝ) :
    ∑ j, softmaxBlend δ m j = 1 := by
  unfold softmaxBlend
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty))

/-- The ramp of option `j` against `M_n − 2δ`: `φ_j := Ind_δ(m_j > max − 2δ)`.
Source: [[soft-self-endorsement]] §The soft strategy
Kind: D
Fidelity: exact -/
def rampPhi (δ : ℚ) {k : ℕ} (m : Fin (k + 1) → ℝ) (j : Fin (k + 1)) : ℝ :=
  ctsInd δ (m j) (univ.sup' univ_nonempty m - 2 * (δ : ℝ))

/-- The ramp blend `θ_j := φ_j / ∑_i φ_i` of [[soft-self-endorsement]]. For `0 < δ` the
denominator is `≥ 1` (`one_le_rampPhi_sum`); at `δ = 0` every `rampPhi` is `0` and the blend is
the zero vector (`0 / 0 = 0`), so `BlendValue … (rampBlend 0)` is an over-strong predicate
(`S ≈ 0` must weakly beat every option) — no headline uses it; fixed-width statements take
`0 < δ`.
Source: [[soft-self-endorsement]] §The soft strategy
Kind: D
Fidelity: exact -/
def rampBlend (δ : ℚ) {k : ℕ} (m : Fin (k + 1) → ℝ) (j : Fin (k + 1)) : ℝ :=
  rampPhi δ m j / ∑ i, rampPhi δ m i

/-- **No junk division in the ramp blend:** for `δ > 0` the argmax's ramp is `1`
(`ctsInd_eq_one_of_le_sub` at the gap `2δ ≥ δ`) and every ramp is nonnegative, so the
denominator is at least `1` — the page's "the top option has `φ = 1`, so the normalization
is safe".
Source: [[soft-self-endorsement]] §The soft strategy
Kind: L
Fidelity: exact -/
lemma one_le_rampPhi_sum (δ : ℚ) (hδ : 0 < δ) {k : ℕ} (m : Fin (k + 1) → ℝ) :
    1 ≤ ∑ i, rampPhi δ m i := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' (univ_nonempty (α := Fin (k + 1))) m
  have hj1 : rampPhi δ m j = 1 := by
    unfold rampPhi
    apply ctsInd_eq_one_of_le_sub _ _ _ hδ
    rw [← hj]
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
    linarith
  calc (1 : ℝ) = rampPhi δ m j := hj1.symm
    _ ≤ ∑ i, rampPhi δ m i :=
        single_le_sum (fun i _ => (ctsInd_mem_Icc _ _ _).1) (mem_univ j)

/-- The ramp weights sum to `1` for `δ > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rampBlend_sum (δ : ℚ) (hδ : 0 < δ) {k : ℕ} (m : Fin (k + 1) → ℝ) :
    ∑ j, rampBlend δ m j = 1 := by
  unfold rampBlend
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, mul_inv_cancel₀]
  exact ne_of_gt (lt_of_lt_of_le one_pos (one_le_rampPhi_sum δ hδ m))

end

end Cleanroom.Found.DefLattice
