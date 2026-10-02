import Cleanroom.Li.LiProjection.Defs
import LogicalInduction.Framework.Machine.WriteOutMachine
import LogicalInduction.Framework.Machine.TokenFold
import LogicalInduction.Framework.Machine.Ruler
import LogicalInduction.Framework.Machine.DigitArithFP

/-!
# `li-projection` · Certificate: efficient computability of the mirror traders (T1.5)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 5 of the layout.

FAF's criterion quantifies over `EfficientlyComputable` traders — `∃ F ∈ Complexity.FP` with
`strategyOfOutput n (F (unaryDay n)) = Tr.strat n` (`Framework/Criterion.lean`). The mirror
`Trader.mirror u q b T` and the affine combination `Trader.affineCombo λ T₁ T₂` are therefore
efficiently computable exactly when the machine's output word can be rewritten, in polynomial time,
into one that decodes to the transformed strategy. This file isolates those two obligations as the
named `Complexity.FP` facts `MirrorStreamRewriter` and `AffineComboRewriter` — shaped like FAF's
own `FreezeStreamRewriter` (`Properties/FinitePerturbations.lean`), which FAF names rather than
inlines "because it is the seam between the economic argument and the compiler" — derives the
certificate from them (`EfficientlyComputable.mirror`, `EfficientlyComputable.affineCombo`, the
analogues of FAF's `EfficientlyComputable.freezeOn`), and **states the two obligations as OPEN**
(`mirrorStreamRewriter`, `affineComboRewriter`, listed in `li-projection-open.txt`).

**Status, stated plainly (audit r1, adversarial B1).** The analogy with FAF's seam holds for the
*shape* of the isolation, not for its *status*: FAF **discharges** its `FreezeStreamRewriter`
(`FreezeStep.freezeStreamRewriter_of_runOracle`; it is not a hypothesis of anything public), while
this package does not discharge its two rewriters. And the two derivations
`EfficientlyComputable.mirror` / `.affineCombo` are plumbing, not composition: each hypothesis is
*logically equivalent* to its universally quantified conclusion (`mirrorStreamRewriter_iff`,
`affineComboRewriter_iff` below — the converse takes `T := ⟨fun n => strategyOfOutput n (F (unaryDay n))⟩`),
so they are kind L and the whole content of headline T1.5 is the OPEN pair. T1.5 is therefore
**OPEN**, reduced to two named `FP` facts; what is *proved* in this file is hypothesis (i) for
eventually-constant weights (`MachineRatCodes.ofFiniteTable`).

**Why they are open, and what discharging them needs** (recorded in the report and findings).
The mandate's template — a flat-stream pass, as FAF's freeze — does not transfer, for three
reasons found while sizing it: (1) the trade *frames* `[6, ⌜φ⌝]` must be rewritten too
(`φ ↦ φ⟦u := b⟧`), which FAF's freeze never does (it touches price leaves only; the conditioning
compiler's frame pass rewrites `φ ↦ φ ⋏ ψ` without looking inside `φ`); (2) the substitution looks
*inside* sentence blocks, and a block may be an **escape leaf** `[1, c]` with `c` a Gödel code of
the sentence (`parseRpn`), so the machine must compute `encode ((decode c)⟦u := b⟧)` — a
polynomial-time tree walk over Foundation's `Nat.pair`-nested formula codes, for which FAF has the
pieces (`DigitFP.unpairFstW`, `unpairSndW`, `mulW` in `Complexity.FP`) but no assembled
recursive-descent transducer; (3) the constants `q m` must be emitted for the days `m ≤ n` named in
binary inside the stream, from an emitter that is efficient only on the unary day. None of this is
a mathematical obstruction — each step is polynomial time — but it is a compiler project on the
scale of FAF's own `Construction/Freeze/*` (9 247 lines at the pin; `Construction/Conditioning/*`
is 13 953). This is an FAF API request: an `FP` formula-code transformer
(`c ↦ encode (f (decode c))` for structural `f`). A weaker obligation would also suffice for
`EfficientlyComputable.mirror`: the rewriter only for words `F` whose decoded strategies are those
of some trader — but since every `F ∈ FP` decodes to *some* trader's strategies
(`mirrorStreamRewriter_iff`), the weaker form is the same statement.

The hypothesis (i) of the note's Lemma A — `q` efficiently computable — is rendered as FAF's
`MachineRatCodes q` and is **discharged** for the eventually-constant `q` the note proves
(`MachineRatCodes.ofFiniteTable`): a finite table and a constant are emitted by nested
length-tests on the unary day (`TokenFold.ifEqLen_mem_FP`).

This certificate and `bli-transfer` L1's `rewriteBits ∈ FP` (its `SpliceCertificate`, which
rewrites price leaves through a run-level oracle) are sibling obligations; neither cites the other.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional

/-! ## The two obligations, named -/

/-- **The mirror stream rewriter** — the one `Complexity.FP` fact `EfficientlyComputable.mirror`
turns on: every polynomial-time output word can be rewritten in polynomial time into one whose
decoded day-`n` strategy is the mirror of the original's. Stated at the decoded-strategy level
(uniformly in the machine), the sibling of FAF's `FreezeStreamRewriter`.
Source: [[dose-response]] §6.1 Lemma A ("the mirrors are traders in `𝒞` with polynomial overhead"); mandate T1.5
Kind: D
Fidelity: exact -/
def MirrorStreamRewriter (u : ℕ) (q : ℕ → ℚ) (b : Bool) : Prop :=
  ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
    ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧
      ∀ n, strategyOfOutput n (G (unaryDay n)) =
        Strategy.mirror u q b (strategyOfOutput n (F (unaryDay n)))

/-- **The affine-combination rewriter**: two polynomial-time output words can be combined in
polynomial time into one whose decoded day-`n` strategy is `λ`·(first) joined with `(1 − λ)`·(second).
Source: [[dose-response]] §6.1 Lemma A ([LI 3.4.4] closure under affine combinations); mandate T1.5
Kind: D
Fidelity: exact -/
def AffineComboRewriter (lam : ℚ) : Prop :=
  ∀ F₁ F₂ : List Bool → List Bool, F₁ ∈ Complexity.FP → F₂ ∈ Complexity.FP →
    ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧
      ∀ n, strategyOfOutput n (G (unaryDay n)) =
        Strategy.join
          [Strategy.scaleBy (EF.const lam) (Nat.zero_le n) (strategyOfOutput n (F₁ (unaryDay n))),
           Strategy.scaleBy (EF.const (1 - lam)) (Nat.zero_le n)
             (strategyOfOutput n (F₂ (unaryDay n)))]

/-- **The mirror preserves efficient computability, given the stream rewriter** — the analogue of
FAF's `EfficientlyComputable.freezeOn`. Plumbing: the hypothesis `hrw` is equivalent to the
universally quantified conclusion (`mirrorStreamRewriter_iff`), so this carries no content beyond
the OPEN `mirrorStreamRewriter` (audit r1, adversarial B1).
Source: [[dose-response]] §6.1 Lemma A; mandate T1.5
Kind: L
Fidelity: n/a (hypothesis ⟺ conclusion)
Hyps: `hrw` is the OPEN `FP` obligation `mirrorStreamRewriter` -/
theorem EfficientlyComputable.mirror {u : ℕ} {q : ℕ → ℚ} {b : Bool}
    (hrw : MirrorStreamRewriter u q b) {T : Trader} (hT : EfficientlyComputable T) :
    EfficientlyComputable (Trader.mirror u q b T) := by
  obtain ⟨F, hF, hFspec⟩ := hT
  obtain ⟨G, hG, hGspec⟩ := hrw F hF
  exact ⟨G, hG, fun n => by rw [hGspec n, hFspec n]; rfl⟩

/-- **The affine combination preserves efficient computability, given the rewriter.** Plumbing:
hypothesis ⟺ conclusion (`affineComboRewriter_iff`).
Source: [[dose-response]] §6.1 Lemma A ([LI 3.4.4]); mandate T1.5
Kind: L
Fidelity: n/a (hypothesis ⟺ conclusion)
Hyps: `hrw` is the OPEN `FP` obligation `affineComboRewriter` -/
theorem EfficientlyComputable.affineCombo {lam : ℚ} (hrw : AffineComboRewriter lam)
    {T₁ T₂ : Trader} (h₁ : EfficientlyComputable T₁) (h₂ : EfficientlyComputable T₂) :
    EfficientlyComputable (Trader.affineCombo lam T₁ T₂) := by
  obtain ⟨F₁, hF₁, hs₁⟩ := h₁
  obtain ⟨F₂, hF₂, hs₂⟩ := h₂
  obtain ⟨G, hG, hGspec⟩ := hrw F₁ F₂ hF₁ hF₂
  exact ⟨G, hG, fun n => by rw [hGspec n, hs₁ n, hs₂ n]; rfl⟩

/-- The mirror rewriter **is** closure of e.c. traders under the mirror: `MirrorStreamRewriter u q b`
iff every efficiently computable trader has an efficiently computable mirror. (⟸) takes the trader
`⟨fun n => strategyOfOutput n (F (unaryDay n))⟩`, e.c. by `⟨F, hF, fun _ => rfl⟩`. Ported from the
audit r1 adversarial probe `SqueezeEquiv.lean`.
Source: audit r1 (adversarial) B1
Kind: L
Fidelity: n/a -/
theorem mirrorStreamRewriter_iff (u : ℕ) (q : ℕ → ℚ) (b : Bool) :
    MirrorStreamRewriter u q b ↔
      ∀ T : Trader, EfficientlyComputable T → EfficientlyComputable (Trader.mirror u q b T) := by
  constructor
  · intro h T hT
    exact EfficientlyComputable.mirror h hT
  · intro h F hF
    obtain ⟨G, hG, hGspec⟩ :=
      h ⟨fun n => strategyOfOutput n (F (unaryDay n))⟩ ⟨F, hF, fun n => rfl⟩
    exact ⟨G, hG, fun n => hGspec n⟩

/-- The affine-combination rewriter **is** closure of e.c. traders under affine combination.
Source: audit r1 (adversarial) B1
Kind: L
Fidelity: n/a -/
theorem affineComboRewriter_iff (lam : ℚ) :
    AffineComboRewriter lam ↔
      ∀ T₁ T₂ : Trader, EfficientlyComputable T₁ → EfficientlyComputable T₂ →
        EfficientlyComputable (Trader.affineCombo lam T₁ T₂) := by
  constructor
  · intro h T₁ T₂ h₁ h₂
    exact EfficientlyComputable.affineCombo h h₁ h₂
  · intro h F₁ F₂ hF₁ hF₂
    obtain ⟨G, hG, hGspec⟩ :=
      h ⟨fun n => strategyOfOutput n (F₁ (unaryDay n))⟩
        ⟨fun n => strategyOfOutput n (F₂ (unaryDay n))⟩
        ⟨F₁, hF₁, fun n => rfl⟩ ⟨F₂, hF₂, fun n => rfl⟩
    exact ⟨G, hG, fun n => hGspec n⟩

/-! ## The obligations, open -/

/-- **OPEN.** The mirror stream rewriter exists for every efficiently computable weight `q`
(FAF's `MachineRatCodes q`, the note's hypothesis (i), made explicit). What a proof needs is
in this file's header: a frame pass, an `FP` substitution on escape-leaf Gödel codes, and the
day-indexed constants. Neither proved nor refuted; the statement is believed true (each step is
polynomial time).
Source: [[dose-response]] §6.1 Lemma A ("Legal: … expressible features/strategies [LI 3.4.3–3.4.4] are closed under affine substitution with such constants"); mandate T1.5
Kind: OPEN
Fidelity: exact
Hyps: (a) `hq` is the note's (i) -/
theorem mirrorStreamRewriter (u : ℕ) (q : ℕ → ℚ) (hq : MachineRatCodes q) (b : Bool) :
    MirrorStreamRewriter u q b := by
  sorry

/-- **OPEN.** The affine-combination rewriter exists for every rational `λ`. Needs the run-aware
automaton to locate trade boundaries in the flat stream (a `6` token inside a sentence block is
the atom `1`, not a frame) and to insert the scaling `[1, ⌜λ⌝, 3]` before each frame.
Source: [LI 3.4.4]; mandate T1.5
Kind: OPEN
Fidelity: exact -/
theorem affineComboRewriter (lam : ℚ) : AffineComboRewriter lam := by
  sorry

/-! ## Hypothesis (i) discharged for eventually-constant `q` -/

/-- The digit word of a finite table with a constant tail, selected by nested length tests on
the unary day: `tableWord x K N z` is `⌜x d⌝` for `d = |z| < N` and `⌜K⌝` otherwise.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tableWord (x : ℕ → ℕ) (K : ℕ) : ℕ → List Bool → List Bool
  | 0 => fun _ => digitsToBits (natDigits4 K)
  | N + 1 => fun z =>
      if ((fun z : List Bool => List.replicate z.length false) z).length = N then
        digitsToBits (natDigits4 (x N))
      else tableWord x K N z

/-- `tableWord_mem_FP`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableWord_mem_FP (x : ℕ → ℕ) (K : ℕ) : ∀ N, tableWord x K N ∈ Complexity.FP := by
  intro N
  induction N with
  | zero => exact FPFold.constFn_mem_FP _
  | succ N ih =>
      have hA : (fun z : List Bool => List.replicate z.length false) ∈ Complexity.FP :=
        UnaryRuler.id
      exact TokenFold.ifEqLen_mem_FP hA N (FPFold.constFn_mem_FP _) ih

/-- `tableWord_isDigitWord`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableWord_isDigitWord (x : ℕ → ℕ) (K : ℕ) : ∀ N z, DigitFP.IsDigitWord (tableWord x K N z) := by
  intro N
  induction N with
  | zero => intro z; exact DigitFP.isDigitWord_digitsToBits (natDigits4_lt K)
  | succ N ih =>
      intro z
      simp only [tableWord]
      split_ifs
      · exact DigitFP.isDigitWord_digitsToBits (natDigits4_lt _)
      · exact ih z

/-- `tableWord_wordVal`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableWord_wordVal (x : ℕ → ℕ) (K : ℕ) :
    ∀ N d, DigitFP.wordVal (tableWord x K N (unaryDay d)) = if d < N then x d else K := by
  intro N
  induction N with
  | zero =>
      intro d
      simp only [tableWord, Nat.not_lt_zero, if_false]
      rw [DigitFP.wordVal_digitsToBits (natDigits4_lt K), digitVal_natDigits4]
  | succ N ih =>
      intro d
      simp only [tableWord, List.length_replicate, length_unaryDay]
      by_cases hd : d = N
      · subst hd
        rw [if_pos rfl, if_pos (Nat.lt_succ_self _),
          DigitFP.wordVal_digitsToBits (natDigits4_lt _), digitVal_natDigits4]
      · rw [if_neg hd, ih d]
        by_cases hlt : d < N
        · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
        · rw [if_neg hlt, if_neg (fun h => hlt (lt_of_le_of_ne (Nat.lt_succ_iff.mp h) hd))]

/-- **A finite table with a constant tail is machine-metered.** Hypothesis (i) of Lemma A for the
eventually-constant case, at the digit level.
Source: [[dose-response]] §6.1 Lemma A, hypothesis (i)+(ii) ("finitely many values before")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem MachineDigits.ofFiniteTable (x : ℕ → ℕ) (N K : ℕ) (hx : ∀ n, N ≤ n → x n = K) :
    MachineDigits x :=
  MachineDigits.of_digitWord (D := tableWord x K N) (tableWord_mem_FP x K N)
    (fun d => tableWord_isDigitWord x K N _)
    (fun d => by
      rw [tableWord_wordVal]
      split_ifs with h
      · rfl
      · exact (hx d (not_lt.mp h)).symm)

/-- **An eventually-constant rational weight is efficiently computable** (`MachineRatCodes`):
hypothesis (i) of Lemma A is a theorem for the `q` with finitely many jumps that the note proves
Lemma A for, not a citation.
Source: [[dose-response]] §6.1 Lemma A, hypotheses (i)+(ii); mandate T1.5 ("do not leave it as (b)")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem MachineRatCodes.ofFiniteTable (q : ℕ → ℚ) (N : ℕ) (c : ℚ) (hq : ∀ n, N ≤ n → q n = c) :
    MachineRatCodes q :=
  ⟨MachineDigits.ofFiniteTable _ N (Encodable.encode c.num) (fun n hn => by rw [hq n hn]),
   MachineDigits.ofFiniteTable _ N c.num.natAbs (fun n hn => by rw [hq n hn]),
   MachineDigits.ofFiniteTable _ N c.den (fun n hn => by rw [hq n hn])⟩

end Cleanroom.Li.LiProjection
