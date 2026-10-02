import Cleanroom.Li.LiProjection.Defs
import Cleanroom.Found.LiQuoteLane.Defs
import Cleanroom.Found.LiAsympCalc.Defs
import LogicalInduction.Construction.LIA
import LogicalInduction.Properties.ExpectationConvergence

/-!
# `def-dose-response` · Defs: the design of record over FAF (D1–D3, D5)

The dose-response note ([[dose-response]] §2) runs `k` copies of one advisee algorithm on `k`
*exposure ledgers*: arm `i` receives, on day `n+1`, the record `(c^{(i)}_n, c^{(i)}_n · a_n(u))` of
whether it was exposed to the advisor's committed day-`n` quote and, if so, the quote. Over FAF:

* **D1** the exposure ledger is `li-quote-lane`'s `ledgerProcess` over the two-item table
  `exposureTable c a` (item `0`: the recorded `c_n · a_n(u)`; item `1`: the coin), published at
  stage `n+1` (`PublicationSchedule.succ`);
* **D2** realized dose, testimony average and the response `Φ(m) = ½ + γ(m − ½)`, with the
  **jump-target identity** (∗) `Φ(m_{N*}) = ½ + γ(v − ½)·p̂` proved from the hypothesis that the
  *exposed* quotes of the window are `v` (not from `a ≡ v`, which the zip assumed);
* **D3** the arm: `li-projection`'s `project` of FAF's LIA over the exposure ledger, on the
  protected atom `projAtomCode 0`, with the one-jump weight `armWeight`. "Same algorithm,
  different ledgers" is the fact that `arm` is one `def` applied to `(c, a)`. The content-blind twin
  `armBlind` has the weight `blindWeight s N c`, whose *type* does not mention the stream;
* **D5** the audit statistics: the cross-arm gap and its Cesàro average, batteries (arbitrary
  nonnegative real weightings with divergent mass — the auditor is not a player), `passes`, the
  within-arm residual, and the cross-arm effect as a difference of FAF's `LUV.expectInf`.

D4 (the committed stream and the steered advisor) lives in `Advisor.lean` (it needs
`li-projection`'s `patch` and `li-quote-lane`'s mirror pair); D6 (the thinned gate) in
`Thinned.lean` (it needs `fa-forcing-trader`).

**Scope tag.** Everything in this package is **one-way**: the arms read a fixed committed stream
`a : ℕ → ℚ` (`H` reads `A`); in `Advisor.lean` the advisor reads a fixed arm (`A` reads `H`). The
two-way closure is the one OPEN statement of record in `Open.lean`.

**Two kernel-pinned facts any re-founding must reproduce** (verbatim from the zip's `AUDIT.md`
§2.6, "What the kernel pinned"):

> *The sign convention of the mirror identities.* With the value convention `t·(𝟙_W − price)`
> and `D_n := Σ_φ t_{n,φ}(P̄_n(α_φ) − P̄_n(β_φ))`, the kernel-checked identities are
> `V(T^⊤) = V_{(W,1)}(T) − Σ(1−q_n)D_n` and `V(T^⊥) = V_{(W,0)}(T) + Σ q_n D_n`. The superficially
> natural opposite signs — consistent under `D ↦ −D`, and easy to write down in prose — do not
> survive the `Finsupp` accounting. The note's §6.1 displays carry the kernel's signs.
>
> *The exact marginal is not available.* The exact identity `𝕡_n(u) = q_n` at finite `n` needs
> a price normalization (`P̄_n(⊤) = 1`, `P̄_n(⊥) = 0`) that LI markets promise only in the limit.
> What is true, proved (`atom_price_tendsto`), and consumed by T2(a) is the limit form
> `𝕡_n(u) → q_∞` — which is what the note's Lemma A displays, with the reason stated there.

In this run the first is `li-projection`'s `Trader.mirror_netWorth_true` / `_false`; the second is
`li-projection`'s `project_atom_tendsto` (the exact form is its OPEN `exact_marginal_exists`).
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## The protected atom -/

/-- **The protected fresh atom `u`**: `li-projection`'s `projAtomCode 0`, fresh for `paperDP T`
(`paperDP_atomFree`) and for every ledger process over it (`atomFreeProcess_ledgerProcess`).
Source: [[dose-response]] §2.1 ("one fresh propositional atom `u`"); mandate § Definitions of record
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev protAtom : ℕ := projAtomCode 0

/-- The protected sentence `u` itself.
Source: [[dose-response]] §2.1
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev protSentence : Sentence := Formula.atom protAtom

/-! ## D1 — the exposure ledger -/

/-- **The exposure table** (D1): item `0` on day `n` is the recorded `c_n · a_n(u)` (the quote if
exposed, `0` otherwise), item `1` is the coin `c_n` as `1`/`0`, every other item is `0`. `[0,1]`-valued
whenever the stream is (`exposureTable_mem`).
Source: [[dose-response]] §2.3 step 3 ("arm `i`'s ledger receives by day `n+1`: `(c_n, c_n · a_n(·))`"); anson-048
Kind: D
Fidelity: exact (the other quoted LUVs' columns are not carried: `u` is the only item T2 needs)
Hyps: n/a -/
def exposureTable (c : ℕ → Bool) (a : ℕ → ℚ) : ℕ → ℕ → ℚ :=
  fun j n => if j = 0 then (if c n then a n else 0) else if j = 1 then (if c n then 1 else 0) else 0

/-- `exposureTable_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma exposureTable_zero (c : ℕ → Bool) (a : ℕ → ℚ) (n : ℕ) :
    exposureTable c a 0 n = if c n then a n else 0 := rfl

/-- `exposureTable_one`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma exposureTable_one (c : ℕ → Bool) (a : ℕ → ℚ) (n : ℕ) :
    exposureTable c a 1 n = if c n then 1 else 0 := rfl

/-- The exposure table is `[0,1]`-valued when the stream is (the `hmem` of `li-quote-lane`).
Source: mandate D1 ("*Trap:* the table must be `[0,1]`-valued — it is")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem exposureTable_mem (c : ℕ → Bool) (a : ℕ → ℚ) (hmem : ∀ n, 0 ≤ a n ∧ a n ≤ 1) :
    ∀ j n, 0 ≤ exposureTable c a j n ∧ exposureTable c a j n ≤ 1 := by
  intro j n
  unfold exposureTable
  split_ifs <;> first | exact hmem n | norm_num

/-- **The arms' publication schedule**: day `n`'s record is posted at stage `n+1` (D2 step 3).
Source: [[dose-response]] §2.3 step 3 ("by day `n+1`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def armSchedule : ℕ → PublicationSchedule := fun _ => PublicationSchedule.succ

/-- **The arm's exposure ledger process** (D1): the base process with the exposure table adjoined
by `li-quote-lane`'s `ledgerProcess`, next-day publication.
Source: [[dose-response]] §2.3 ("`Γ_i := Γ_0 + own ledger`"); anson-048; anson-2-025 (A)
Kind: D
Fidelity: exact
Hyps: n/a -/
def armProcess (base : DeductiveProcess) (c : ℕ → Bool) (a : ℕ → ℚ) : DeductiveProcess :=
  ledgerProcess base (exposureTable c a) armSchedule

/-- The base stages are contained in the arm's stages (the `extendBy` union).
Source: mandate T3.5 ("true for `armProcess` by `ledgerProcess_D`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem base_subset_armProcess (base : DeductiveProcess) (c : ℕ → Bool) (a : ℕ → ℚ) (n : ℕ) :
    base.D n ⊆ (armProcess base c a).D n := by
  intro φ hφ
  unfold armProcess
  rw [ledgerProcess_D]
  exact Finset.mem_union_left _ hφ

/-! ## D2 — realized dose, testimony, response -/

/-- **The realized dose** `p̂ := (1/N) ∑_{j<N} 𝟙[c_j]` over the formative window `[0, N)`; junk `0`
at `N = 0` (ℚ's `x / 0 = 0`), which is why every theorem carries `0 < N`.
Source: [[dose-response]] §2.2 D1 ("day-`N*` averages `p̂_i`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def realizedDose (c : ℕ → Bool) (N : ℕ) : ℚ :=
  (∑ j ∈ Finset.range N, if c j then (1 : ℚ) else 0) / N

/-- **The testimony average** `m_N := (1/N) ∑_{j<N} (c_j a_j + (1 − c_j)·½)`: the received quote
on exposed days, the null value `½` on blinded days.
Source: [[dose-response]] §6.2 (the display for `m_{N*}`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def testimony (c : ℕ → Bool) (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  (∑ j ∈ Finset.range N, if c j then a j else (1 / 2 : ℚ)) / N

/-- **The response** `Φ(m) := ½ + γ(m − ½)` at impressionability `γ`.
Source: [[dose-response]] §6.2 ("response `Φ(m) := ½ + γ(m − ½)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def response (γ m : ℚ) : ℚ := 1 / 2 + γ * (m - 1 / 2)

/-- The realized dose lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem realizedDose_mem (c : ℕ → Bool) (N : ℕ) :
    0 ≤ realizedDose c N ∧ realizedDose c N ≤ 1 := by
  unfold realizedDose
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num) hNq.le
  · rw [div_le_one hNq]
    calc (∑ j ∈ Finset.range N, if c j then (1 : ℚ) else 0)
        ≤ ∑ _j ∈ Finset.range N, (1 : ℚ) :=
          Finset.sum_le_sum fun j _ => by split_ifs <;> norm_num
      _ = N := by simp

/-- The testimony average lies in `[0,1]` when the stream does.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem testimony_mem (c : ℕ → Bool) (a : ℕ → ℚ) (N : ℕ) (hmem : ∀ n, 0 ≤ a n ∧ a n ≤ 1) :
    0 ≤ testimony c a N ∧ testimony c a N ≤ 1 := by
  unfold testimony
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  constructor
  · refine div_nonneg (Finset.sum_nonneg fun j _ => ?_) hNq.le
    split_ifs
    · exact (hmem j).1
    · norm_num
  · rw [div_le_one hNq]
    calc (∑ j ∈ Finset.range N, if c j then a j else (1 / 2 : ℚ))
        ≤ ∑ _j ∈ Finset.range N, (1 : ℚ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · exact (hmem j).2
          · norm_num
      _ = N := by simp

/-- **The testimony identity**: if every *exposed* day of the window carries the quote `v`, the
testimony average is `½ + (v − ½)·p̂`. The hypothesis is on the exposed days only — the stream may
be anything on blinded days (the zip's `testimonyAverage_eq` assumed `a ≡ v`).
Source: [[dose-response]] §6.3 (∗), first equation; zip AUDIT §2.4
Kind: P
Fidelity: stronger: the stream is constrained on the exposed days of the window only
Hyps: (a) none -/
theorem testimony_eq {c : ℕ → Bool} {a : ℕ → ℚ} {v : ℚ} {N : ℕ} (hN : 0 < N)
    (hv : ∀ j < N, c j = true → a j = v) :
    testimony c a N = 1 / 2 + (v - 1 / 2) * realizedDose c N := by
  unfold testimony realizedDose
  have h : ∀ j ∈ Finset.range N,
      (if c j then a j else (1 / 2 : ℚ)) = 1 / 2 + (v - 1 / 2) * (if c j then (1 : ℚ) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hc : c j = true
    · rw [if_pos hc, if_pos hc, hv j hj hc]; ring
    · rw [if_neg hc, if_neg hc]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum, nsmul_eq_mul]
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- **The jump-target identity (∗)**: `Φ(m_N) = ½ + γ(v − ½)·p̂` on every ledger whose exposed
formative quotes are `v`. This is the number both the content-steered arm (`armWeight`) and the
content-blind arm (`blindWeight`) jump to, and the whole of T2(e)'s content.
Source: [[dose-response]] §6.3 (∗); anson-054; zip `jump_target_eq` (AUDIT §2.4), now with the
hypothesis on the stream visible
Kind: P
Fidelity: stronger: exposed-day hypothesis in place of `a ≡ v`
Hyps: (a) none -/
theorem jump_target_eq {c : ℕ → Bool} {a : ℕ → ℚ} {v : ℚ} {N : ℕ} (γ : ℚ) (hN : 0 < N)
    (hv : ∀ j < N, c j = true → a j = v) :
    response γ (testimony c a N) = 1 / 2 + γ * (v - 1 / 2) * realizedDose c N := by
  rw [testimony_eq hN hv]
  unfold response
  ring

/-! ## D3 — the arm: one program on a ledger -/

/-- **The arm's weight** (the critical-period disposition): `½` through the formative window
`[0, N)`, then the one jump to `Φ(m_N)` — a function of the ledger `(c, a)` through the testimony
average. This is the `q` of `li-projection`'s Lemma A.
Source: [[dose-response]] §6.2 ("set `q_n := ½` for `n < N*`, `q_n := Φ(m_{N*})` for `n ≥ N*`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def armWeight (γ : ℚ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ) : ℕ → ℚ :=
  fun n => if n < N then 1 / 2 else response γ (testimony c a N)

/-- **The content-blind weight**: `½` through the window, then the jump to `½ + s·p̂` — the
arm's own realized dose with a hardwired slope `s`. **Its type does not mention the stream**: this
is the mandate's "check that `armBlind`'s weight must not mention `a`", made a matter of arity.
Source: [[dose-response]] §6.3 T2(e) ("the jump target is `½ + s ĥ` … ignoring quote contents entirely")
Kind: D
Fidelity: exact
Hyps: n/a -/
def blindWeight (s : ℚ) (N : ℕ) (c : ℕ → Bool) : ℕ → ℚ :=
  fun n => if n < N then 1 / 2 else 1 / 2 + s * realizedDose c N

/-- **The arm's base market**: FAF's LIA over the exposure ledger — "the standard base construction
for `Γ_0 + ledger`".
Source: [[dose-response]] §6.2 ("run the standard base construction [LI 5.4.2] for `Γ_0 + ledger`")
Kind: D
Fidelity: exact (FAF's `liaHistory` is [LI 5.4.2]'s construction)
Hyps: n/a -/
noncomputable def armBase (base : DeductiveProcess) (c : ℕ → Bool) (a : ℕ → ℚ) : History :=
  liaHistory (armProcess base c a)

/-- **The arm** `M(γ, N)` on the ledger `(c, a)` (D3, anson-2-025 reading (A)): the projection of
the base LIA on the protected atom with the critical-period weight. One `def` applied to the
ledger: "same algorithm, different ledgers" is this signature, and its semantic form is
`arm_of_exposureTable_eq` (`Arms.lean`: equal exposure tables give equal arms). The e.c.
certificate of the weight (`armWeight_machineRatCodes`) is a per-ledger finite table, not a
ledger-reading program — see its docstring (fidelity audit r1, N9).
Source: [[dose-response]] §6.2 ("output the Lemma-A extension"); anson-2-025 (A); anson-048
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def arm (base : DeductiveProcess) (γ : ℚ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ) :
    History :=
  project (armBase base c a) protAtom (armWeight γ N c a)

/-- **The content-blind twin** `M̃(s, N)`: the same base over the same ledger, the blind weight.
The ledger (hence the base market) still carries the recorded quotes — a blind arm *receives*
testimony, it just does not read it when it jumps.
Source: [[dose-response]] §6.3 T2(e) ("the content-blind arm algorithm")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def armBlind (base : DeductiveProcess) (s : ℚ) (N : ℕ) (c : ℕ → Bool)
    (a : ℕ → ℚ) : History :=
  project (armBase base c a) protAtom (blindWeight s N c)

/-- `armWeight_of_lt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma armWeight_of_lt (γ : ℚ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ) {n : ℕ} (h : n < N) :
    armWeight γ N c a n = 1 / 2 := by simp [armWeight, h]

/-- `armWeight_of_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma armWeight_of_le (γ : ℚ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ) {n : ℕ} (h : N ≤ n) :
    armWeight γ N c a n = response γ (testimony c a N) := by
  simp [armWeight, not_lt.mpr h]

/-- `blindWeight_of_lt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma blindWeight_of_lt (s : ℚ) (N : ℕ) (c : ℕ → Bool) {n : ℕ} (h : n < N) :
    blindWeight s N c n = 1 / 2 := by simp [blindWeight, h]

/-- `blindWeight_of_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma blindWeight_of_le (s : ℚ) (N : ℕ) (c : ℕ → Bool) {n : ℕ} (h : N ≤ n) :
    blindWeight s N c n = 1 / 2 + s * realizedDose c N := by
  simp [blindWeight, not_lt.mpr h]

/-- The arm's weight is eventually constant from the window end (Lemma A's `hjump`).
Source: [[dose-response]] §6.1 Lemma A (ii) ("eventually constant")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem armWeight_jump (γ : ℚ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ) :
    ∀ n, N ≤ n → armWeight γ N c a n = armWeight γ N c a N := by
  intro n hn
  rw [armWeight_of_le γ N c a hn, armWeight_of_le γ N c a le_rfl]

/-- The blind weight is eventually constant from the window end.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem blindWeight_jump (s : ℚ) (N : ℕ) (c : ℕ → Bool) :
    ∀ n, N ≤ n → blindWeight s N c n = blindWeight s N c N := by
  intro n hn
  rw [blindWeight_of_le s N c hn, blindWeight_of_le s N c le_rfl]

/-- **The arm's weight lives in `[η, 1 − η]` with `η := (1 − γ)/2`** for `γ ∈ [0, 1]` and a
`[0,1]`-valued stream: `Φ` maps `[0,1]` onto `[½ − γ/2, ½ + γ/2]`, and `½` is inside. Lemma A's
range hypothesis; `η > 0` needs `γ < 1`, which is where the headlines add it.
Source: [[dose-response]] §6.2 ("interior range"); mandate D3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem armWeight_mem (γ : ℚ) (hγ0 : 0 ≤ γ) (N : ℕ) (c : ℕ → Bool) (a : ℕ → ℚ)
    (hmem : ∀ n, 0 ≤ a n ∧ a n ≤ 1) :
    ∀ n, (1 - γ) / 2 ≤ armWeight γ N c a n ∧ armWeight γ N c a n ≤ 1 - (1 - γ) / 2 := by
  intro n
  unfold armWeight response
  obtain ⟨h0, h1⟩ := testimony_mem c a N hmem
  split_ifs
  · constructor <;> linarith
  · constructor <;> nlinarith

/-- The blind weight lives in `[η, 1 − η]` with `η := (1 − |2s|)/2`, stated in the form the
witnesses use: for `|s| ≤ γ/2` the blind weight is in `[(1 − γ)/2, 1 − (1 − γ)/2]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem blindWeight_mem (s γ : ℚ) (hγ0 : 0 ≤ γ) (hs : |s| ≤ γ / 2) (N : ℕ)
    (c : ℕ → Bool) :
    ∀ n, (1 - γ) / 2 ≤ blindWeight s N c n ∧ blindWeight s N c n ≤ 1 - (1 - γ) / 2 := by
  intro n
  unfold blindWeight
  obtain ⟨h0, h1⟩ := realizedDose_mem c N
  rw [abs_le] at hs
  split_ifs
  · constructor <;> linarith
  · constructor <;> nlinarith

/-! ## D5 — the audit statistics -/

/-- **The cross-arm gap** `𝔼^{(i)}_n(X) − 𝔼^{(j)}_n(X)` on day `n`, over FAF's day-`n` expectation.
Source: [[dose-response]] §2.5 D4 (the summand of `G^{ij}_N`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def crossArmGap (Pi Pj : History) (X : LUV) (n : ℕ) : ℝ :=
  X.expect Pi n - X.expect Pj n

/-- **The cross-arm audit** `G^{ij}_N(X) := (1/N) ∑_{n<N} (𝔼^{(i)}_n(X) − 𝔼^{(j)}_n(X))`, the
exclusive Cesàro mean of the gap (`li-asymp-calc`'s `cesaro`; `G_0 = 0` is junk, everything is
`atTop`).
Source: [[dose-response]] §2.5 D4 (the display for `G^{ij}_N(X)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def crossArmAudit (Pi Pj : History) (X : LUV) (N : ℕ) : ℝ :=
  cesaro (crossArmGap Pi Pj X) N

/-- **A battery weighting**: any nonnegative real sequence with divergent (inclusive) prefix sums.
The auditor is an external statistician, not a player (§2.5), so batteries are *not* required to
be P-generable features — the quantifier of T3 (i) is over all of them.
Source: [[dose-response]] §2.5 D4 ("`w` a divergent weighting"); mandate D5
Kind: D
Fidelity: stronger: real sequences, not `PGenerableWeighting`
Hyps: n/a -/
def IsBattery (w : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ w n) ∧ Tendsto (prefixSum w) atTop atTop

/-- The uniform weighting is a battery.
Source: [[dose-response]] §7 ("the uniform weighting alone")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem isBattery_one : IsBattery (fun _ => (1 : ℝ)) := by
  refine ⟨fun _ => zero_le_one, ?_⟩
  have : prefixSum (fun _ : ℕ => (1 : ℝ)) = fun n : ℕ => (n : ℝ) + 1 := by
    funext n; simp [prefixSum]
  rw [this]
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- **A cross-arm audit over the battery `w` passes** when the `w`-weighted average of the gap
tends to `0`.
Source: [[dose-response]] §2.5 D4 ("pass ⟺ `G^{ij}_N(X) → 0`", generalized over a battery)
Kind: D
Fidelity: exact
Hyps: n/a -/
def passes (w : ℕ → ℝ) (Pi Pj : History) (X : LUV) : Prop :=
  Tendsto (weightedAverage w (crossArmGap Pi Pj X)) atTop (𝓝 0)

/-- **The within-arm (calibration) residual** of an arm `H` against a quote stream `a` at the
lookahead `f`: `𝔼^H_{f n}(X) − a_n`.
Source: [[dose-response]] §2.5 D4 ("`r_n = E^{H^{(1)}}_{f(n)}(X) − a_n(X)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def withinArmResidual (H : History) (X : LUV) (f : ℕ → ℕ) (a : ℕ → ℝ) (n : ℕ) :
    ℝ :=
  X.expect H (f n) - a n

/-- **The cross-arm effect of record**: the difference of the two arms' limiting expectations
(FAF's `LUV.expectInf`, which needs each arm's `expect_converges` package).
Source: [[dose-response]] §2.5 D4 ("whose limit (T3) is exactly the destination gap"); §3 (A)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def crossArmEffect (Pi Pj : History) (DPi DPj : DeductiveProcess)
    [IsLogicalInductor Pi DPi] [IsLogicalInductor Pj DPj] (X : LUV)
    (hcode : X.MachineThresholdCodes)
    (hconsi : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPi.D n))
    (hconsj : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPj.D n))
    (hvali : ∀ v : PCWorld, v.ConsistentWithTheory DPi → ∃ x : ℝ, v.ValuesAt X x)
    (hvalj : ∀ v : PCWorld, v.ConsistentWithTheory DPj → ∃ x : ℝ, v.ValuesAt X x) : ℝ :=
  X.expectInf Pi DPi hcode hconsi hvali - X.expectInf Pj DPj hcode hconsj hvalj

end Cleanroom.Deference.DefDoseResponse
