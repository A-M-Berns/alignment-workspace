import Cleanroom.Fa.FaTheoremA.Engine

/-!
# `fa-theorem-a` · LemmaP: on a generable day-set where `Y_n → c`, the quote `a_n → c` (T6)

**Lemma P (Preemptive symmetry)** of [[route-negative-introspective]] §7, quoted verbatim:
"Let `E ⊆ ℕ⁺` be efficiently computable and suppose `Y_n → c` as `n → ∞` along `E`. Then
`a_n → c` along `E`." Here `E` is rendered as a `{0,1}`-valued `PGenerableWeighting` of `A`'s
market (FAF's rendering of "efficiently computable set", fidelity `variant`), "along `E`" is the
filter `atTop ⊓ 𝓟 {n | E_n = 1}`, and the proof is **Route A** of the mandate: Theorem A's gate
argument localized to `E` (`Engine.lean`), giving `limsup_E a_n ≤ c ≤ liminf_E a_n`. Only FAF's
corrected 4.8.15 is used; the note's route through Expectation Preemptive Learning (4.8.13) and
Limit Coherence is not needed (finding F5). This is where a **full limit** holds — in contrast
to Half 1's limit point — and only because the gate is restricted to a set where `Y_n`
converges.

* `lemmaP` (T6, headline), `lemmaP_const` (`E ≡ 1`: "if `Y_n → c` then `a_n → c`", vq-wiki-032).
* `claim2` is in `TheoremA.lean` (it needs `expect_converges`).

**Why `E` must be generable** (T6 Traps; finding F4): for an arbitrary `Set ℕ` nothing in the
criterion constrains `a_n` on `E` — e.g. `E := {n | a_n > Y_n + ½}`, if infinite with `Y_n → c`
along it, has `a_n ↛ c`; whether such an `E` exists for a given inductor is not settled here.
If `E` has finite support the filter is `⊥` and the conclusion is vacuous (the N+ witness uses an
infinite `E`, `Witnesses.lean`).

Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. No `H`-side convergence hypothesis beyond `hY`; the only modelling step is
`pkg.reflected` (`Half1.lean`).
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **T6 (headline). Lemma P.** In the context of T3 (no `H`-side convergence hypothesis at all),
for a generable `{0,1}`-valued day-set feature `E` of `A`'s market and a real `c`: if the
realized `Y_n = 𝔼^H_{f n}(X_n) → c` along `E` (the filter `atTop ⊓ 𝓟 {n | E_n = 1}`), then the
quote `a_n = 𝔼^A_n(Y_n) → c` along `E` — a **full limit**, pointwise on `E`. Proof (Route A): for
each `ε > 0`, `a_n < c + ε` eventually on `E` by `not_frequently_quote_ge` at `u = c + ε/2`,
`η = ε/2`, and `c − ε < a_n` eventually on `E` by `not_frequently_quote_le`; both from T4 on the
gated ramps `E_n · Ind_δ(a_n ≷ q)`.
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The only modelling step is the quote's determinacy, `pkg.reflected` — `A`'s theory
determines `H`'s run outputs, a form of `A` "seeing" `H` logically rather than through prices
(root-fa-027); at the mirror witness it is (a) at variant fidelity (ledger-recorded).
Source: [[route-negative-introspective]] §7 Lemma P (vq-wiki-058: "Let `E ⊆ ℕ⁺` be efficiently computable and suppose `Y_n → c` as `n → ∞` along `E`. Then `a_n → c` along `E`."); vq-wiki-032 (lab update)
Kind: C
Fidelity: variant: `E` is a `{0,1}`-valued `PGenerableWeighting` of `A`'s market (FAF's rendering of "efficiently computable"); "along `E`" is `atTop ⊓ 𝓟 {n | E_n = 1}`. Nearly exact: an `EF` denotes a continuous function of the day's prices, so a `{0,1}`-valued one is constant in the prices on each day — `hE01` forces `E` to be a price-independent day-set, which is precisely the note's e.c. `E ⊆ ℕ⁺`; the rendering changes only the metering (FAF's machine-metered `PGenerableWeighting` for the paper's poly-time). A finite-support `E` makes the along-`E` filter `⊥` and the conclusion vacuous (module docstring)
Hyps: (a) `hworldA`, `hE`, `hE01`, `hY`; (c) `pkg.reflected` as above. -/
theorem lemmaP {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {E : ℕ → EF} (hE : PGenerableWeighting E)
    (hE01 : ∀ n, (E n).denote A = 0 ∨ (E n).denote A = 1) {c : ℝ}
    (hY : Tendsto (realized H f X) (atTop ⊓ 𝓟 {n | (E n).denote A = 1}) (𝓝 c)) :
    Tendsto (quoteSeq Y A) (atTop ⊓ 𝓟 {n | (E n).denote A = 1}) (𝓝 c) := by
  rw [Metric.tendsto_nhds] at hY ⊢
  intro ε hε
  have hY' := hY (ε / 2) (by positivity)
  rw [eventually_inf_principal] at hY'
  have hup : ∀ᶠ n in atTop ⊓ 𝓟 {n | (E n).denote A = 1}, quoteSeq Y A n < c + ε := by
    by_contra hcon
    rw [not_eventually, frequently_inf_principal] at hcon
    refine not_frequently_quote_ge pkg hworldA hE hE01 (u := c + ε / 2) (η := ε / 2)
      (by positivity) ?_ ?_
    · refine hY'.mono (fun n hn hS => ?_)
      have := hn hS
      rw [Real.dist_eq, abs_sub_lt_iff] at this
      linarith [this.1]
    · refine hcon.mono (fun n hn => ⟨hn.1, ?_⟩)
      have := not_lt.1 hn.2
      linarith
  have hlow : ∀ᶠ n in atTop ⊓ 𝓟 {n | (E n).denote A = 1}, c - ε < quoteSeq Y A n := by
    by_contra hcon
    rw [not_eventually, frequently_inf_principal] at hcon
    refine not_frequently_quote_le pkg hworldA hE hE01 (u := c - ε / 2) (η := ε / 2)
      (by positivity) ?_ ?_
    · refine hY'.mono (fun n hn hS => ?_)
      have := hn hS
      rw [Real.dist_eq, abs_sub_lt_iff] at this
      linarith [this.2]
    · refine hcon.mono (fun n hn => ⟨hn.1, ?_⟩)
      have := not_lt.1 hn.2
      linarith
  filter_upwards [hup, hlow] with n h1 h2
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- The constant-`1` feature names every day: its day-set is `univ` and the along-`E` filter is
`atTop`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma setOf_const_one_denote_eq_univ (A : History) :
    {n : ℕ | ((fun _ : ℕ => EF.const (1 : ℚ)) n).denote A = 1} = Set.univ := by
  ext n
  simp

/-- **T6, corollary: the pointwise Half 1 on the full day-set.** If `Y_n → c` (as `n → ∞`) then
`a_n → c` — Lemma P at `E ≡ 1` (vq-wiki-032's extension "if `Y_n → c` (varying) then
`a_n → c`"). The hypothesis is on `H`'s realized expectations; the conclusion on `A`'s quotes.
Scope: one-way; the (c) is `pkg.reflected`.
Source: [[route-negative-introspective]] §7 (Lemma P at `E = ℕ⁺`); vq-wiki-032
Kind: C
Fidelity: exact
Hyps: (a) `hworldA`, `hY`; (c) `pkg.reflected`. -/
theorem lemmaP_const {H A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) {c : ℝ}
    (hY : Tendsto (realized H f X) atTop (𝓝 c)) :
    Tendsto (quoteSeq Y A) atTop (𝓝 c) := by
  have h := lemmaP (A := A) pkg hworldA (pgenerableWeighting_const 1)
    (fun _ => Or.inr (by simp)) (c := c)
    (by rw [setOf_const_one_denote_eq_univ A, principal_univ, inf_top_eq]; exact hY)
  rwa [setOf_const_one_denote_eq_univ A, principal_univ, inf_top_eq] at h

/-! ## A non-trivial generable day-set: the even days (W4's `E`) -/

/-- The even days as a `{0,1}`-valued feature progression: `E_n := const (if n even then 1
else 0)` — a day-set that is not `≡ 1`, price-independent (as every `{0,1}`-valued `EF` is), and
generable (`evenDays_pgenerable`).
Source: mandate W4 (the even-day day-set for Lemma P); [[route-negative-introspective]] §7 ("efficiently computable `E`")
Kind: D
Fidelity: exact -/
def evenDays (n : ℕ) : EF := EF.const (if n % 2 = 0 then 1 else 0)

/-- `evenDays` denotes `1` on even days and `0` on odd days, in any market.
Source: mandate W4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem evenDays_denote (A : History) (n : ℕ) :
    (evenDays n).denote A = if n % 2 = 0 then 1 else 0 := by
  unfold evenDays
  split_ifs <;> simp

/-- `evenDays` is `{0,1}`-valued (Lemma P's `hE01`).
Source: mandate W4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem evenDays_01 (A : History) (n : ℕ) :
    (evenDays n).denote A = 0 ∨ (evenDays n).denote A = 1 := by
  rw [evenDays_denote]
  split_ifs <;> simp

/-- **W4's certificate: the even days are a `PGenerableWeighting`** (FAF's `def:ece` class).
The serialization stream is FAF's `MachineSpliceStream.ifZero`, dispatching on the parity
ruler `(MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two` between the two constant
serializations `serialize_const 1`/`serialize_const 0`; rank `0`; closed denotation. This is the
route F16 did not find in `MachineRatCodes`: a day-set is emitted as a token stream, not as a
rational sequence. (a) throughout — FAF's class exactly, no weaker "generable".
Source: mandate W4; [[route-negative-introspective]] §7 ("Let `E ⊆ ℕ⁺` be efficiently computable")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem evenDays_pgenerable : PGenerableWeighting evenDays where
  polySeg :=
    ((MachineSpliceStream.serialize_const (1 : ℚ)).ifZero
      (MachineSpliceStream.serialize_const (0 : ℚ))
      (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two).of_eq (fun n => by
        by_cases h : n % 2 = 0
        · simp [evenDays, h]
        · simp [evenDays, h])
  rank_le := fun n => by simp [evenDays]
  closed := fun n ρ V => by simp [evenDays, EF.denote]

end Cleanroom.Fa.FaTheoremA
