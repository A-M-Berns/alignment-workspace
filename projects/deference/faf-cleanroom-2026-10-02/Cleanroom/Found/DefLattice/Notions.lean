import Cleanroom.Found.DefLattice.Expert

/-!
# The deference notions of record: Tower, the conditional tower, Total Trust, Reflection

Package `def-lattice`, file 2 of the definitions module. The predicates every dependent states
its theorems over (`Value` and its blended forms are in `Menu.lean`):

* `Tower P DP E` — the corpus's **Mart**: `E^H_n(X_n) ≈ₙ E^H_n(⌜E*(X_n)⌝)` for every e.d. `X`
  and every e.d. quote `Y` reflecting `E*(X)`.
* `CondTower P DP E` — the conditional tower (`ccee`-shaped): the same with a P-generable
  `[0,1]` weight folded in, at FAF's deferred-day index.
* `ThresholdIneqAbove / Below P DP E wt s` — the above/below-threshold inequalities in
  **product form** `E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0` (denominator-free; the conditional
  reading divides by the conditioning mass `E^H_n(W_n)`, which may be `0`), of which
  `SoftTotalTrustAbove/Below` (ramp weights), `HardTotalTrustAbove/Below` (DDB's hard cut, a
  comparison object), `BandReflection` (the band value-form) and `HardValueReflection` (the
  refuted exact object) are instances; `TotalTrust` is the soft form at every rational
  threshold and positive width.

Every notion quantifies **universally** over the e.d. sources and the e.d. quote LUVs that
satisfy the reflection clauses of `Expert.lean`. None asserts that a quote exists.

The notions presuppose a theory-consistent world, as `hworld` does in FAF's endpoints: with no
`ConsistentWithTheory DP` world every e.c. pair is a `WeightQuote` at every weight with zero
slack, and the threshold inequalities become *false* (not vacuously true) at any positive
threshold on a history pricing `⊤` at `1` and `⊥` at `0`. Inconsistency cannot be used to
satisfy the definitions (audit round 1, probe N6).
-/

namespace Cleanroom.Found.DefLattice

open LogicalInduction Filter Topology

noncomputable section

variable (P : History) (DP : DeductiveProcess)

/-! ## Asymptotic plumbing (product form ⟺ unnormalized form) -/

/-- `f − g ≳ₙ 0` is `f ≳ₙ g` (unfolding `AsympLE`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma asympGE_sub_zero_iff {f g : ℕ → ℝ} :
    (fun n => f n - g n) ≳ₙ (fun _ => (0 : ℝ)) ↔ f ≳ₙ g := by
  unfold AsympGE AsympLE
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    linarith
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    linarith

/-- `f − g ≲ₙ 0` is `f ≲ₙ g`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma asympLE_sub_zero_iff {f g : ℕ → ℝ} :
    (fun n => f n - g n) ≲ₙ (fun _ => (0 : ℝ)) ↔ f ≲ₙ g := by
  unfold AsympLE
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    linarith
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    linarith

/-- `f − g ≈ₙ 0` is `f ≈ₙ g`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma asympEq_sub_zero_iff {f g : ℕ → ℝ} :
    (fun n => f n - g n) ≈ₙ (fun _ => (0 : ℝ)) ↔ f ≈ₙ g := by
  unfold AsympEq
  simp only [sub_zero]

/-! ## T2 — Tower (the corpus's Mart) and the conditional tower -/

/-- **Tower** — the corpus's **Mart**`(H → E*)`, quoted from [[deference-notions]] §Mart: "for
every e.d. sequence of LUVs `(X_n)`: `E^H_n(X_n) ≈ₙ E^H_n(⌜E*(X_n)⌝)`". Over FAF: for every
e.d. source `X` and every e.d. quote `Y` reflecting the expert's estimate (`Reflects`), the
novice's day-`n` expectations of `X n` and of `Y n` agree in the limit. It is the asymptotic
*equality*; the inequality faces are `ThresholdIneqAbove/Below`. This is the deference
*hypothesis*, not an LI theorem: its self-instance at one `(X, Y)` given a full
`ExpectedFutureExpectationQuote` is FAF's `lic_expected_future_expectations` (`thm:cee`) —
a theorem of `def-self-trust`, not of this package. **Two things dependents must know (audit
round 1, items 5/N7):** (i) `Tower` carries no `Valued` clause on the source (FAF's `cee`
package has none), so it demands the equality also on *unvalued* e.c. sources (all-`⊤` families
and the like) — free for the self-expert (`cee` holds for every e.c. `X`), but whoever *forces*
`Tower` for a cross-market expert must force it for unvalued sources too, or the forced
statement is `Tower` restricted to valued sources, which is not this predicate; `Tower` is
thereby stronger as a hypothesis than the corpus's Mart over e.d. LUVs, never weaker. (ii)
`Tower` is falsifiable when a reflecting quote exists (the all-ones expert fails it), and
vacuously true for an expert none of whose estimates any e.c. LUV reflects — an arrow
hypothesised on `Tower` at an AI-instance needs `li-quote-lane`'s existence lemma to say
anything.
Source: [[deference-notions]] §Mart; v6 §1 table line 173; [[centered-bet-squeeze]] §0
Kind: D
Fidelity: exact (at FAF's deferred-day estimate; finding F1 on the corpus's two clocks) -/
def Tower (E : Expert DP) : Prop :=
  ∀ X Y : ℕ → LUV, LUV.MachineThresholdCodeSeq X → LUV.MachineThresholdCodeSeq Y →
    Reflects DP E X Y → (fun n => (X n).expect P n) ≈ₙ (fun n => (Y n).expect P n)

/-- **The conditional tower** — the corpus's **ccee**`(H → E*)`, quoted from
[[deference-notions]] §The conditional tower: "for every e.d. `(X_n)` and every observable
weight `w_n ∈ [0,1]`: `E^H_n(X_n · w_n) ≈ₙ E^H_n(⌜E*(X_n) · w_n⌝)`". Over FAF: for every
e.d. source, every `[0,1]` weight sequence generable from the *novice's* market `P`
(`PGenerableRat P w`, the corpus's "`𝒞_H`-market-generable"), and every pair of e.d. quote
LUVs forming a `CondQuote` (left product within FAF's slack, right product exact, weight at
the deferred day `w (E.f n)` as in FAF and LI 4.12.3 — the wiki's `w_n` is finding F2), the
two expectations agree in the limit. Self-instance: FAF's `lic_no_expected_net_update_conditional`
(`thm:ccee`) via `CondQuote.of_conditionalExpectationQuote` — `def-self-trust`'s theorem.
The FAF `affine` certificate is *not* part of the hypothesis (mandate T2 trap).
Source: [[deference-notions]] §The conditional tower; v6 §1.5; vq-wiki-002
Kind: D
Fidelity: variant: weight at `w (f n)`, left product within slack (both as FAF; disclosed) -/
def CondTower (E : Expert DP) : Prop :=
  ∀ (X : ℕ → LUV) (w : ℕ → ℚ), (∀ n, 0 ≤ w n ∧ w n ≤ 1) → PGenerableRat P w →
    LUV.MachineThresholdCodeSeq X → ∀ Z Z' : ℕ → LUV, CondQuote DP E X w Z Z' →
    (fun n => (Z n).expect P n) ≈ₙ (fun n => (Z' n).expect P n)

/-! ## T3 — the threshold inequalities in product form -/

/-- **The above-threshold inequality, product form.** For every e.d. source `X` and every
weight quote `(W, XW)` at the weight function `wt` (`WeightQuote`):
`E^H_n(XW_n) − s · E^H_n(W_n) ≳ₙ 0` — the `LUVCombination.expect` of `[(1, XW), (−s, W)]`
(`TwoOptionLUV.lean`), so that `lit-ddb-frames`'s finite
`0 ≤ ∑ π (X − s) 1[E(X) ≥ s]` and this are recognizably one object. The conditional reading
`E^H_n(X_n | ·) ≳ₙ s` divides by the conditioning mass `E^H_n(W_n)`, which can be `0`; it is
never part of a definition here (Lean's `x / 0 = 0` would make "conditional `≥ s`" trivially
true at threshold `0`).
Source: [[deference-notions]] §Total Trust (the unnormalized threshold form); mandate
design decision 5
Kind: D
Fidelity: exact (unnormalized form) -/
def ThresholdIneqAbove (E : Expert DP) (wt : ℝ → ℝ) (s : ℚ) : Prop :=
  ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → WeightQuote DP E X wt W XW →
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ))

/-- **The below-threshold inequality, product form:** `E^H_n(XW_n) − s · E^H_n(W_n) ≲ₙ 0`
for every e.d. source and weight quote at `wt`.
Source: [[deference-notions]] §Total Trust ("together with the lower cut"); DDB l. 180
Kind: D
Fidelity: exact (unnormalized form) -/
def ThresholdIneqBelow (E : Expert DP) (wt : ℝ → ℝ) (s : ℚ) : Prop :=
  ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → WeightQuote DP E X wt W XW →
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ))

/-- **The product form is the display with the right side moved over** (per instance):
`E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0` ⟺ `E^H_n(XW_n) ≳ₙ s·E^H_n(W_n)`. Dependents may use either
spelling of the same predicate.
Source: [[deference-notions]] §Total Trust; mandate T3
Kind: L
Fidelity: exact -/
theorem soft_above_iff_unnormalized (s : ℚ) (W XW : ℕ → LUV) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) ↔
      (fun n => (XW n).expect P n) ≳ₙ (fun n => (s : ℝ) * (W n).expect P n) :=
  asympGE_sub_zero_iff

/-- The below-threshold companion of `soft_above_iff_unnormalized`.
Source: [[deference-notions]] §Total Trust; mandate T3
Kind: L
Fidelity: exact -/
theorem soft_below_iff_unnormalized (s : ℚ) (W XW : ℕ → LUV) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ)) ↔
      (fun n => (XW n).expect P n) ≲ₙ (fun n => (s : ℝ) * (W n).expect P n) :=
  asympLE_sub_zero_iff

/-- `ThresholdIneqAbove` in the unnormalized spelling, as a predicate.
Source: mandate T3
Kind: L
Fidelity: exact -/
theorem thresholdIneqAbove_iff_unnormalized (E : Expert DP) (wt : ℝ → ℝ) (s : ℚ) :
    ThresholdIneqAbove P DP E wt s ↔
      ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → WeightQuote DP E X wt W XW →
        (fun n => (XW n).expect P n) ≳ₙ (fun n => (s : ℝ) * (W n).expect P n) := by
  unfold ThresholdIneqAbove
  simp only [soft_above_iff_unnormalized]

/-- `ThresholdIneqBelow` in the unnormalized spelling, as a predicate.
Source: mandate T3
Kind: L
Fidelity: exact -/
theorem thresholdIneqBelow_iff_unnormalized (E : Expert DP) (wt : ℝ → ℝ) (s : ℚ) :
    ThresholdIneqBelow P DP E wt s ↔
      ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → WeightQuote DP E X wt W XW →
        (fun n => (XW n).expect P n) ≲ₙ (fun n => (s : ℝ) * (W n).expect P n) := by
  unfold ThresholdIneqBelow
  simp only [soft_below_iff_unnormalized]

/-- **Soft Total Trust, above-threshold, at `(s, δ)`** — [[deference-notions]] §Total Trust's
display `E^H_n(X_n · w_{t,δ}) ≳ₙ t · E^H_n(w_{t,δ})`, `w_{t,δ} = Ind_δ(E*(X_n) > t)`, in product
form with the right side moved over (`soft_above_iff_unnormalized`): the above-threshold
inequality at the ramp weight `rampAbove δ s`. The corpus writes the threshold `t`; here it is
the rational `s`. At `δ = 0` the ramp is identically `0`, so the predicate asks
`E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0` of quote LUVs valued `0` in every consistent world:
content-free (true for every inductor novice by `thm:expprovind`), though not syntactically
trivial for an arbitrary `P`. **Dependents' rule:** every headline at a fixed width takes
`0 < δ` as a hypothesis, `TotalTrust` quantifies `0 < δ →`, and a theorem whose only
`SoftTotalTrust*` instance is at `δ = 0` is a stub (audit round 1, items 3/N3).
Source: [[deference-notions]] §Total Trust; v6 §1.6 (boxed display); [[centered-bet-squeeze]]
§0 (`w^>`)
Kind: D
Fidelity: exact -/
abbrev SoftTotalTrustAbove (E : Expert DP) (s δ : ℚ) : Prop :=
  ThresholdIneqAbove P DP E (rampAbove δ s) s

/-- **Soft Total Trust, below-threshold, at `(s, δ)`:** the below-threshold inequality at the
down-ramp `rampBelow δ s = Ind_δ(E*(X_n) < s)`: `E^H_n(X_n · w^<) ≲ₙ s · E^H_n(w^<)`.
Source: [[deference-notions]] §Total Trust (the lower cut); [[centered-bet-squeeze]] §0 (`w^<`)
Kind: D
Fidelity: exact -/
abbrev SoftTotalTrustBelow (E : Expert DP) (s δ : ℚ) : Prop :=
  ThresholdIneqBelow P DP E (rampBelow δ s) s

/-- **Total Trust (LUV level, the definition of record):** both soft threshold inequalities at
every rational threshold `s` and every positive width `δ` — the corpus's "for every e.d.
`(X_n)` and every threshold `t`" at the soft grade it adopts in LI. The hard cut is the
comparison object `HardTotalTrust`; the finite-frame Total Trust is
`Cleanroom.Found.LitDdbFrames.TotalTrust` (its product form is this one on a finite world set,
`TwoOptionFinite.lean`); the real-sequence rungs are `tt-ladder`'s `…Seq` predicates.
Thresholds range over all of `ℚ`: outside `[0, 1]` the faces are trivial on an inductor
(for `s ≥ 1` the up-ramp vanishes on `[0,1]`-valued quotes, for `s ≤ −δ` it is `1`), which is
harmless; the corpus's real `t` loses nothing to rational `s` for the predicate as a whole,
since each face is monotone in `s` and rationals are dense (a dependent needing one fixed
irrational threshold would notice).
Source: [[deference-notions]] §Total Trust; [[centered-bet-squeeze]] §0 (both cuts, width `δ`)
Kind: D
Fidelity: exact (soft grade; thresholds rational) -/
def TotalTrust (E : Expert DP) : Prop :=
  ∀ s δ : ℚ, 0 < δ → SoftTotalTrustAbove P DP E s δ ∧ SoftTotalTrustBelow P DP E s δ

/-- `SoftTotalTrust` is `TotalTrust` under its explicit name.
Source: mandate T3
Kind: D
Fidelity: exact -/
abbrev SoftTotalTrust (E : Expert DP) : Prop := TotalTrust P DP E

/-- **Hard Total Trust, above-threshold, at `s`** — DDB's `E_π(X | E(X) ≥ t) ≥ t` in product
form, at the hard indicator `1[s ≤ E*(X_n)]`. **Not the definition of record:** the hard
indicator is not a generable weight (`EF.continuous_denote`; `BetClass.lean`
`no_generable_hard_indicator`), and the hard form is the comparison/refuted object of
lean-deference-2-015 (`def-lattice-arrows`), never a hypothesis of any theorem in this run.
**Refutability caveat (audit round 1, N8):** as a universal statement over `WeightQuote`s at
`hardAbove s`, it is refuted only by exhibiting, for the expert in question, an e.c. weight LUV
valued at the sharp event `1[s ≤ E*(X_n)]` in every consistent world (with its product); this
package neither builds nor claims such a quote, and if none exists the predicate is vacuously
true and cannot be refuted in this form. The refuting package owns that obligation.
Source: [[Deference Done Better]] l. 175; [[deference-notions]] §Total Trust ("a hard
`1[E*(X) > t]` is discontinuous (illegal as a weight) and liar-prone")
Kind: D
Fidelity: exact (DDB's cut over FAF LUVs) -/
abbrev HardTotalTrustAbove (E : Expert DP) (s : ℚ) : Prop :=
  ThresholdIneqAbove P DP E (hardAbove s) s

/-- **Hard Total Trust, below-threshold, at `s`** (DDB l. 180, `1[E*(X_n) ≤ s]`); comparison
object, see `HardTotalTrustAbove`.
Source: [[Deference Done Better]] l. 180
Kind: D
Fidelity: exact -/
abbrev HardTotalTrustBelow (E : Expert DP) (s : ℚ) : Prop :=
  ThresholdIneqBelow P DP E (hardBelow s) s

/-- **Hard Total Trust** at every rational threshold, both cuts — the comparison object.
Source: [[Deference Done Better]] l. 175, 180
Kind: D
Fidelity: exact -/
def HardTotalTrust (E : Expert DP) : Prop :=
  ∀ s : ℚ, HardTotalTrustAbove P DP E s ∧ HardTotalTrustBelow P DP E s

/-- `TotalTrust` gives both faces at any fixed positive width.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem TotalTrust.above {E : Expert DP} (h : TotalTrust P DP E) (s δ : ℚ) (hδ : 0 < δ) :
    SoftTotalTrustAbove P DP E s δ := (h s δ hδ).1

/-- `TotalTrust` gives both faces at any fixed positive width.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem TotalTrust.below {E : Expert DP} (h : TotalTrust P DP E) (s δ : ℚ) (hδ : 0 < δ) :
    SoftTotalTrustBelow P DP E s δ := (h s δ hδ).2

/-! ## T5 — Reflection: the band value-form, and the hard form as refuted object -/

/-- **Band Reflection** — [[reflection-in-li]] §The value form's two-sided pinch,
unnormalized: for every threshold `s`, band half-width `ε > 0` and ramp width `δ > 0`, with the
band weight `b_n = Ind_δ(⌜E*(X_n)⌝ > s − ε) · Ind_δ(⌜E*(X_n)⌝ < s + ε)` (`bandWt δ s ε`, one
`WeightQuote`),
`(s − ε) · E^H_n(b_n) ≲ₙ E^H_n(X_n · b_n) ≲ₙ (s + ε) · E^H_n(b_n)`: the above-threshold
inequality at `s − ε` and the below-threshold inequality at `s + ε`, both at the band weight
(`bandReflection_iff_pinch` spells out the display). The normalized reading ("conditional on
the expert's estimate sitting in the band, the novice's conditional estimate sits in the same
band") divides by the band mass and is not part of the definition. `ε = 0` collapses the band
to the hard form (`HardValueReflection`), hence `0 < ε`. This is *this run's* identification of
the corpus's LI weakening of value-form Reflection (ATTRIBUTION-UNVETTED; see
`def-lattice-report` §T5 and lean-deference-2-029). DDB's *function-form* Reflection
`π(· | P = ρ) = ρ` has no LUV carrier and is `lit-ddb-frames`'s finite-frame `Reflects`.
Source: [[reflection-in-li]] §The value form is a theorem (the `b_n` display and the pinch);
[[deference-notions]] §Reflection and its ⚠ re-scope
Kind: D
Fidelity: exact (unnormalized, at FAF's deferred-day estimate) -/
def BandReflection (E : Expert DP) : Prop :=
  ∀ s ε δ : ℚ, 0 < ε → 0 < δ →
    ThresholdIneqAbove P DP E (bandWt δ s ε) (s - ε) ∧
      ThresholdIneqBelow P DP E (bandWt δ s ε) (s + ε)

/-- `BandReflection` is the two-sided pinch of [[reflection-in-li]], per instance.
Source: [[reflection-in-li]] §The value form is a theorem
Kind: L
Fidelity: exact -/
theorem bandReflection_iff_pinch (E : Expert DP) :
    BandReflection P DP E ↔
      ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X →
        WeightQuote DP E X (bandWt δ s ε) W XW →
          (fun n => ((s - ε : ℚ) : ℝ) * (W n).expect P n) ≲ₙ (fun n => (XW n).expect P n) ∧
            (fun n => (XW n).expect P n) ≲ₙ (fun n => ((s + ε : ℚ) : ℝ) * (W n).expect P n) := by
  unfold BandReflection
  constructor
  · intro h s ε δ hε hδ X W XW hX q
    obtain ⟨ha, hb⟩ := h s ε δ hε hδ
    exact ⟨(soft_above_iff_unnormalized P (s - ε) W XW).mp (ha X W XW hX q),
      (soft_below_iff_unnormalized P (s + ε) W XW).mp (hb X W XW hX q)⟩
  · intro h s ε δ hε hδ
    exact ⟨fun X W XW hX q =>
        (soft_above_iff_unnormalized P (s - ε) W XW).mpr (h s ε δ hε hδ X W XW hX q).1,
      fun X W XW hX q =>
        (soft_below_iff_unnormalized P (s + ε) W XW).mpr (h s ε δ hε hδ X W XW hX q).2⟩

/-- **Hard value-form Reflection — the refuted object.** Both threshold inequalities at the
sharp band `1[E*(X_n) = s]`, i.e. `E^H_n(X_n · 1[E*(X_n) = s]) ≈ₙ s · E^H_n(1[E*(X_n) = s])`
(`hardValueReflection_iff_asympEq`). The exact grade is *false* on the paradoxical family
(LI 4.12.4's discussion: conditional on the future price sitting exactly at the threshold, the
correct credence is `0`, not the threshold — [[reflection-in-li]] §Exactness); the refutation
over FAF is `def-squeeze-diamond`'s root-deference-013 / `def-lattice-arrows`'s
lean-deference-2-015. **Never a hypothesis of any theorem in this run** ([[plan]] §0.4 rule 2).
**Refutability caveat (audit round 1, N8):** a refutation at the LUV level must exhibit a
`WeightQuote` at `hardBand s` for the expert — an e.c. LUV valued at the sharp event
`1[E*(X_n) = s]` in every consistent world — which this package neither builds nor claims; if no
such quote exists the predicate is vacuously true and the refutation must be stated in another
form (e.g. over a quote the refuting package constructs).
Source: [[reflection-in-li]] §What is genuinely unreachable (1); LI 4.12.4 discussion
Kind: D
Fidelity: exact (the refuted exact grade, stated so it can be refuted) -/
def HardValueReflection (E : Expert DP) : Prop :=
  ∀ s : ℚ, ThresholdIneqAbove P DP E (hardBand s) s ∧ ThresholdIneqBelow P DP E (hardBand s) s

/-- `HardValueReflection` is the asymptotic *equality* at the sharp band, per instance.
Source: [[reflection-in-li]] §Exactness
Kind: L
Fidelity: exact -/
theorem hardValueReflection_iff_asympEq (E : Expert DP) :
    HardValueReflection P DP E ↔
      ∀ s : ℚ, ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X →
        WeightQuote DP E X (hardBand s) W XW →
          (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≈ₙ (fun _ => (0 : ℝ)) := by
  unfold HardValueReflection ThresholdIneqAbove ThresholdIneqBelow
  constructor
  · intro h s X W XW hX q
    rw [asympEq_iff_asympLE_asympGE]
    exact ⟨(h s).2 X W XW hX q, (h s).1 X W XW hX q⟩
  · intro h s
    exact ⟨fun X W XW hX q => (asympEq_iff_asympLE_asympGE.mp (h s X W XW hX q)).2,
      fun X W XW hX q => (asympEq_iff_asympLE_asympGE.mp (h s X W XW hX q)).1⟩

end

end Cleanroom.Found.DefLattice
