import Cleanroom.Bli.BliLeak.Instance
import Cleanroom.Bli.BliLeak.Counterlogical
import Cleanroom.Li.LiPseudorandom.Witnesses

/-!
# `bli-leak` · Witnesses: the N+ rows

* **L3.3/L3.5.** The instance of record is non-degenerate: the stream of record is not eventually
  constant (`leakStream_not_eventuallyConst`, from `li-pseudorandom`'s
  `unionStar_not_eventuallyConst`), the placement is day-varying (`member_injective`), the edit
  is real — the leak market of record differs from the base inductor (under the instance
  hypothesis: else the base would be exploited) — and the leak coordinates are infinitely many.
* **L8.2.** The concrete counterlogical process: `paperDP 𝗜𝚺₁` extended by `bli-found`'s
  day-varying schedule, which refutes `ψ = freshAtom 3 ⟨1, 1⟩` at stage `2`
  (`dayVarying_has_negative`) while being consistent there
  (`extendBy_paperDP_dayVarying_hworld`); the constant markets `0` and `1` are both inductors
  over the adjoined process (`counterlogical_two_inductors_dayVarying`).
* **L3.0.** The transport's non-vacuity is in `Transport.lean` (`cxPerturbed_ne_liaHistory`).
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Cleanroom.Bli.BliFound
open Cleanroom.Li.LiPseudorandom

/-! ## L3.5: the instance is non-degenerate -/

section Theory

variable (T : ArithmeticTheory) [T.Δ₁]

/-- **N+ (L3.5): the stream of record is not eventually constant** — the leaked truths keep
varying, so the leak is not a finite amount of information.
Source: mandate L3.5 (N+: `unionStar_not_eventuallyConst`)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem leakStream_not_eventuallyConst : ¬ ∃ N b, ∀ n ≥ N, leakStream T n = b :=
  unionStar_not_eventuallyConst (paperDP T) member recordDelay recordDelay_lt
    (by norm_num) (by norm_num)

/-- **N+ (L3.5): the leak coordinates are infinitely many** — the edited cells
`(N₀, leakAtom (recordPad N₀) n)` are pairwise distinct.
Source: mandate L3.5 (N+: "the leak coordinates infinite")
Kind: N+
Fidelity: n/a -/
theorem leakCoordinates_infinite (N₀ : ℕ) :
    Set.Infinite {p : ℕ × Sentence | ∃ n, p = (N₀, leakAtom (recordPad N₀) n)} := by
  have hinj : Function.Injective (fun n => ((N₀, leakAtom (recordPad N₀) n) : ℕ × Sentence)) := by
    intro m n h
    exact leakAtom_injective _ (Prod.mk.inj h).2
  have : Set.range (fun n => ((N₀, leakAtom (recordPad N₀) n) : ℕ × Sentence)) =
      {p : ℕ × Sentence | ∃ n, p = (N₀, leakAtom (recordPad N₀) n)} := by
    ext p
    simp only [Set.mem_range, Set.mem_setOf_eq]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩
  rw [← this]
  exact Set.infinite_range_of_injective hinj

/-- **N+ (L3.5): the edit is real** — under the instance hypothesis the leak market of record is
not the base inductor (else the base would be exploited by the trader of record).
Source: mandate L3.5 (N+)
Kind: N+
Fidelity: n/a
Hyps: (OPEN li-pseudorandom T7) the instance `IsLogicalInductor (leakQ T) (leakDP T)` -/
theorem leakMarket_ne_leakQ [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    [hLI : IsLogicalInductor (leakQ T) (leakDP T)] (N₀ : ℕ) : leakMarket T N₀ ≠ leakQ T := by
  intro h
  exact leak_instance_not_logicalInductor T N₀ (h ▸ hLI)

end Theory

/-! ## L8.2: the concrete counterlogical process -/

/-- The refuted sentence of the concrete witness: the day-varying schedule's negative literal
at `⟨1, 1⟩`, entered at stage `2`.
Source: mandate L8.2 (witness: "`bli-found`'s `extendBy_paperDP_dayVarying`")
Kind: D
Fidelity: n/a -/
def dayVaryingRefuted : Sentence := freshAtom 3 (Nat.pair 1 1)

/-- The day-varying extension of `paperDP 𝗜𝚺₁` refutes `dayVaryingRefuted` at stage `2`.
Source: mandate L8.2 (witness); `bli-found` `dayVarying_has_negative`
Kind: L
Fidelity: exact -/
theorem dayVaryingRefuted_mem :
    (∼dayVaryingRefuted) ∈ (extendBy (paperDP 𝗜𝚺₁) dayVaryingSchedule).D 2 :=
  Finset.mem_union_right _ (dayVarying_has_negative (le_refl 1))

/-- **N+ (L8.2): the concrete counterlogical process.** Over `paperDP 𝗜𝚺₁` extended by the
day-varying schedule — computable, consistent at stage `2`, refuting `dayVaryingRefuted` there —
the constant markets `0` and `1`, which disagree everywhere, are both logical inductors over the
process with `dayVaryingRefuted` adjoined; and a world consistent with the base's stage `2`
falsifies the condition (so the vacuity is the adjoined condition's doing).
Source: mandate L8.2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem counterlogical_two_inductors_dayVarying :
    (∃ v : PCWorld, v.ConsistentWith ((extendBy (paperDP 𝗜𝚺₁) dayVaryingSchedule).D 2) ∧
        ¬ v.Holds dayVaryingRefuted) ∧
      IsLogicalInductor (constMarket 0)
        ((extendBy (paperDP 𝗜𝚺₁) dayVaryingSchedule).adjoinSentence dayVaryingRefuted) ∧
      IsLogicalInductor (constMarket 1)
        ((extendBy (paperDP 𝗜𝚺₁) dayVaryingSchedule).adjoinSentence dayVaryingRefuted) ∧
      ∀ n φ, constMarket 0 n φ ≠ constMarket 1 n φ :=
  counterlogical_two_inductors extendBy_paperDP_dayVarying_computable dayVaryingRefuted_mem
    (extendBy_paperDP_dayVarying_hworld 2)

end Cleanroom.Bli.BliLeak
