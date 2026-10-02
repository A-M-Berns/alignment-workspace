import Cleanroom.Bli.BliLeak.Exploit
import Cleanroom.Li.LiPseudorandom.Union
import Cleanroom.Bli.BliFound.PaperInstances
import Cleanroom.Bli.BliFound.Extend

/-!
# `bli-leak` · Instance: the leak market over `paperDP T` (L3.5)

The instance of record of the abstract leak theorem (`Exploit.lean`):

* the process `leakDP T = (paperDP T).union (atomDP member (leakStream T) recordDelay)` — the
  paper's deductive process with `li-pseudorandom`'s atom-deciding process adjoined at the
  placement `member`, deciding member `n` one day late (`recordDelay n = n + 1`);
* the stream `leakStream T = unionStar (paperDP T) member recordDelay (1/2)` —
  `li-pseudorandom`'s family of record inside the union, pseudorandom at frequency `1/2` relative
  to the LIA over the union (`unionStar_pseudorandom`);
* the base inductor `leakQ T = liaHistory (leakDP T)` and the leak market `leakMarket T N₀`
  (`leakHistory` at the pad `4 ^ sizeBound N₀`, all edits on day `N₀`, the leaked values
  `truthR (leakStream T)`), with the trader of record `leakTraderRecord N₀`.

What this file discharges at grade (a): `hworld` for the union — `atomDP member x g` **is** a
`bli-found` literal process (`literalProcess_memberSchedule`), so `extendBy_hworld` applies with
`paperDP_cleanroomFree` (this is the obligation `li-pseudorandom`'s report leaves to dependents);
`hdec` (`union_atomDP_decided`); `MachineSentenceCodes memberAtom`; `pendingBound recordDelay 1`;
the pseudorandomness; the exact agreement on days `< N₀` and `E1x`. What it does **not**: the
inductor certificate `IsLogicalInductor (leakQ T) (leakDP T)`, which needs
`ComputableDeductiveProcess (leakDP T)`, i.e. the computability of the stream —
`li-pseudorandom` T7, OPEN. So `leak_instance_exploits` and `leak_instance_not_logicalInductor`
carry the instance as a hypothesis (proved), and the two OPEN statements of record
(`leakStream_computable`, `leakDP_computable`) feed the closed forms in `Closed.lean`, listed in
`bli-leak-open.txt`.

Scope (mandate L3.4/L3.5): exploitation (a); the counterexample market's computability and the
instance's inductor certificate rest on `li-pseudorandom` T7 (OPEN).
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional Filter Topology
open Cleanroom.Bli.BliFound
open Cleanroom.Li.LiPseudorandom

/-! ## `atomDP member` is a literal process -/

/-- The literal schedule whose literal process is `atomDP member x g`: at stage `s`, the entries
`(memberFamily, ⟨j, 0⟩, x j)` for the members `j ≤ s` with `g j ≤ s`.
Source: mandate L3.5 (`hworld` for the union: "show `atomDP member x g = literalProcess L`")
Kind: D
Fidelity: exact -/
def memberSchedule (x : ℕ → Bool) (g : ℕ → ℕ) : LiteralSchedule where
  lits s := ((Finset.range (s + 1)).filter (fun j => g j ≤ s)).image
    (fun j => (memberFamily, Nat.pair j 0, x j))
  mono s := by
    apply Finset.image_subset_image
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega

/-- Membership in the member schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_memberSchedule_lits {x : ℕ → Bool} {g : ℕ → ℕ} {s : ℕ} {y : ℕ × ℕ × Bool} :
    y ∈ (memberSchedule x g).lits s ↔
      ∃ j, (j ≤ s ∧ g j ≤ s) ∧ (memberFamily, Nat.pair j 0, x j) = y := by
  simp only [memberSchedule, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]

/-- The member schedule is functional: each member has one polarity, `x j`.
Source: mandate L3.5
Kind: L
Fidelity: exact -/
lemma memberSchedule_functional (x : ℕ → Bool) (g : ℕ → ℕ) : (memberSchedule x g).Functional := by
  rintro s f p ⟨hpos, hneg⟩
  rw [mem_memberSchedule_lits] at hpos hneg
  obtain ⟨j, -, hj⟩ := hpos
  obtain ⟨j', -, hj'⟩ := hneg
  simp only [Prod.mk.injEq] at hj hj'
  obtain ⟨-, hpj, hxj⟩ := hj
  obtain ⟨-, hpj', hxj'⟩ := hj'
  have hjj : j = j' := (Nat.pair_eq_pair.mp (hpj.trans hpj'.symm)).1
  subst hjj
  rw [hxj] at hxj'
  exact absurd hxj' (by decide)

/-- `bli-found`'s literal of a member entry is `li-pseudorandom`'s literal of the member.
Source: mandate L3.5 ("check that `Extend.literalOf` and `LiPseudorandom.literalOf` agree")
Kind: L
Fidelity: exact -/
lemma literalOf_memberEntry (x : ℕ → Bool) (j : ℕ) :
    Cleanroom.Bli.BliFound.literalOf (memberFamily, Nat.pair j 0, x j) =
      Cleanroom.Li.LiPseudorandom.literalOf member x j := by
  cases hx : x j <;>
    simp [Cleanroom.Bli.BliFound.literalOf, Cleanroom.Li.LiPseudorandom.literalOf, hx, member,
      freshAtom]

/-- **`atomDP member x g` is the literal process of the member schedule.**
Source: mandate L3.5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem literalProcess_memberSchedule (x : ℕ → Bool) (g : ℕ → ℕ) :
    literalProcess (memberSchedule x g) = atomDP member x g := by
  apply DeductiveProcess.ext
  funext s
  rw [literalProcess_D]
  show ((memberSchedule x g).lits s).image Cleanroom.Bli.BliFound.literalOf =
    ((Finset.range (s + 1)).filter (fun j => g j ≤ s)).image
      (Cleanroom.Li.LiPseudorandom.literalOf member x)
  simp only [memberSchedule]
  rw [Finset.image_image]
  congr 1
  funext j
  exact literalOf_memberEntry x j

/-- The union of a base process with `atomDP member x g` is `bli-found`'s `extendBy`.
Source: mandate L3.5
Kind: L
Fidelity: exact -/
theorem union_atomDP_member_eq (DP₀ : DeductiveProcess) (x : ℕ → Bool) (g : ℕ → ℕ) :
    DP₀.union (atomDP member x g) = extendBy DP₀ (memberSchedule x g) := by
  unfold extendBy
  rw [literalProcess_memberSchedule]

/-- **`hworld` for the union**: a cleanroom-free base process with a consistent world at every
stage keeps one after `atomDP member x g` is adjoined (`extendBy_hworld` through the schedule).
Source: mandate L3.5 (`hworld` for the union — "yours")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem union_atomDP_member_hworld (DP₀ : DeductiveProcess) (hDP₀ : CleanroomFreeProcess DP₀)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP₀.D n)) (x : ℕ → Bool) (g : ℕ → ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP₀.union (atomDP member x g)).D n) := by
  rw [union_atomDP_member_eq]
  exact extendBy_hworld (memberSchedule_functional x g)
    (ProcessFreeOf.of_cleanroomFree hDP₀ _) hworld

/-! ## The instance of record -/

/-- The delay profile of record: member `n` is decided on day `n + 1`.
Source: mandate L3.5 (`g := fun n ↦ n + 1`); K6
Kind: D
Fidelity: exact -/
abbrev recordDelay : ℕ → ℕ := fun n => n + 1

/-- `recordDelay` is strict.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recordDelay_lt (j : ℕ) : j < recordDelay j := Nat.lt_succ_self j

/-- The pad of record for an edit on day `N₀`: `4 ^ sizeBound N₀`.
Source: mandate L3.4/L3.5
Kind: D
Fidelity: exact -/
def recordPad (N₀ : ℕ) : ℕ := 4 ^ sizeBound N₀

section Theory

variable (T : ArithmeticTheory) [T.Δ₁]

/-- **The pseudorandom stream of record**: `li-pseudorandom`'s `unionStar` over `paperDP T` at the
placement `member`, delay `recordDelay`, frequency `1/2`.
Source: mandate L3.5 (`x := unionStar (paperDP T) member g (1/2)`)
Kind: D
Fidelity: exact -/
noncomputable def leakStream : ℕ → Bool := unionStar (paperDP T) member recordDelay (1 / 2)

/-- **The process of record**: `paperDP T` with the member atoms decided one day late.
Source: mandate L3.5 (`DP := (paperDP T).union (atomDP member x g)`)
Kind: D
Fidelity: exact -/
noncomputable def leakDP : DeductiveProcess :=
  (paperDP T).union (atomDP member (leakStream T) recordDelay)

/-- **The base inductor of record**: FAF's LIA over `leakDP T`.
Source: mandate L3.5 (`Q := liaHistory DP`)
Kind: D
Fidelity: exact -/
noncomputable def leakQ : History := liaHistory (leakDP T)

/-- **The leak market of record**: `leakQ T` with, on day `N₀`, the price of `leakAtom (recordPad N₀) n`
replaced by the truth value of member `n`, for every `n`.
Source: mandate L3.4/L3.5
Kind: D
Fidelity: exact -/
noncomputable def leakMarket (N₀ : ℕ) : History :=
  leakHistory (leakQ T) (leakAtom (recordPad N₀)) (fun _ => N₀) (truthR (leakStream T))

/-- `hworld` for the process of record, over any theory `paperDP` is consistent for.
Source: mandate L3.5
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem leakDP_hworld [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((leakDP T).D n) :=
  union_atomDP_member_hworld (paperDP T) (paperDP_cleanroomFree T) (paperDP_hworld T) _ _

/-- Decided with delay, for the process of record.
Source: mandate L3.5 (`hdec`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakDP_decided :
    ∀ n (v : PCWorld) m, recordDelay n ≤ m → v.ConsistentWith ((leakDP T).D m) →
      v.payout (memberAtom n) = truthR (leakStream T) n :=
  union_atomDP_decided (paperDP T) recordDelay_lt (leakStream T)

/-- The stream of record is pseudorandom at frequency `1/2` relative to the base inductor of
record, for every deferral function (`li-pseudorandom`'s `unionStar_pseudorandom`).
Source: mandate L3.5 (`PseudorandomFrequency` by `unionStar_pseudorandom`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakStream_pseudorandom :
    ∀ f : DeferralFunction, PseudorandomFrequency (truthR (leakStream T)) (1 / 2) f (leakQ T) :=
  unionStar_pseudorandom (paperDP T) member recordDelay recordDelay_lt (1 / 2)
    ⟨by norm_num, by norm_num⟩

/-- The leak market of record agrees with the base inductor on every day-small sentence.
Source: mandate L3.5 (`hlarge` by L3.1)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakMarket_E1x (N₀ : ℕ) : E1x (leakQ T) (leakMarket T N₀) :=
  leakHistory_E1x (fun n => leakAtom_large_pow N₀ le_rfl n)

/-- The leak market of record **is** the base inductor on every day `< N₀`.
Source: mandate L3.4
Kind: L
Fidelity: exact -/
theorem leakMarket_agree_before (N₀ : ℕ) :
    ∀ n < N₀, ∀ φ, leakMarket T N₀ n φ = leakQ T n φ :=
  leakHistory_agree_before (fun _ => le_rfl)

/-- The leak market of record is the base inductor on every sentence that is no leak atom.
Source: mandate L3.1 (exact agreement)
Kind: L
Fidelity: exact -/
theorem leakMarket_eq_of_ne (N₀ : ℕ) {φ : Sentence} (h : ∀ n, φ ≠ leakAtom (recordPad N₀) n)
    (m : ℕ) : leakMarket T N₀ m φ = leakQ T m φ :=
  leakHistory_eq_of_ne h m

/-- The trader of record for an edit on day `N₀`.
Source: mandate L3.5
Kind: D
Fidelity: exact -/
def leakTraderRecord (N₀ : ℕ) : Trader :=
  leakTrader (leakAtom (recordPad N₀)) (fun _ => N₀) memberAtom

/-- The trader of record is efficiently computable.
Source: mandate L3.5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakTraderRecord_ec (N₀ : ℕ) : EfficientlyComputable (leakTraderRecord N₀) :=
  leakTrader_record_ec _ _

/-- **L3.5. The instance: the trader of record exploits the leak market of record**, over the
process of record, given the inductor certificate of the base (the instance hypothesis).
Every other hypothesis of L3.3 is discharged here at grade (a): `hworld`
(`leakDP_hworld`), `MachineSentenceCodes memberAtom`, `hdec` (`leakDP_decided`),
`pendingBound recordDelay 1`, pseudorandomness (`leakStream_pseudorandom`, at `succDeferral`),
injectivity and disjointness of the families.
Scope: exploitation (a); the instance's inductor certificate rests on `li-pseudorandom` T7
(OPEN) — see `Closed.lean`.
Source: mandate L3.5 (`leak_instance_exploits`)
Kind: C
Fidelity: exact
Hyps: (OPEN li-pseudorandom T7) the instance `IsLogicalInductor (leakQ T) (leakDP T)` -/
theorem leak_instance_exploits [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    [IsLogicalInductor (leakQ T) (leakDP T)] (N₀ : ℕ) :
    (leakTraderRecord N₀).Exploits (leakMarket T N₀) (leakDP T) :=
  leakTrader_exploits (leakQ T) (leakDP T) (leakDP_hworld T) memberAtom
    machineSentenceCodes_memberAtom (leakStream T) recordDelay (leakDP_decided T) 1
    pendingBound_succ succDeferral (leakStream_pseudorandom T succDeferral)
    (leakAtom (recordPad N₀)) (leakAtom_injective _) (fun n m => memberAtom_ne_leakAtom _ n m)
    (fun _ => N₀) ⟨N₀, fun _ hn => hn⟩

/-- **The leak market of record is no logical inductor** over the process of record, given the
base's inductor certificate: exploitation against `noExploit` with the trader's certificate.
Source: mandate L3.4 (unconditional corollary), L3.5
Kind: C
Fidelity: exact
Hyps: (OPEN li-pseudorandom T7) the instance `IsLogicalInductor (leakQ T) (leakDP T)` -/
theorem leak_instance_not_logicalInductor [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    [IsLogicalInductor (leakQ T) (leakDP T)] (N₀ : ℕ) :
    ¬ IsLogicalInductor (leakMarket T N₀) (leakDP T) :=
  fun h => h.noExploit _ (leakTraderRecord_ec N₀) (leak_instance_exploits T N₀)

/-! ## The two open statements of record (li-pseudorandom T7) -/

/-- **OPEN (li-pseudorandom T7).** The stream of record is computable. This is
`truthStar_computable`'s shape for the union builder: the enumeration inside `unionStar` is
primitive recursive (`genWeighting_primrec`); what remains is an evaluator of the LIA's states
uniform in the process code and the commutation of the diagonal's real comparisons with the
rational cast — see `li-pseudorandom-report.md` § T7.
Source: mandate L3.5/L3.6 (`hx` is T7); `li-pseudorandom-open.txt` (`truthStar_computable`)
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem leakStream_computable : Computable (leakStream T) := by
  sorry

/-- **OPEN (li-pseudorandom T7).** The process of record is computable: `paperDP T` is
(`paperDP_computable`), and `atomDP member (leakStream T) recordDelay` reduces to
`leakStream_computable` through a `Computable` analogue of FAF's `encode_stage_prim_of_list`
(FAF API request; the `Primrec` version is what `li-pseudorandom`'s `atomDP_succ_computable`
uses for primitive recursive streams), plus `extendBy_computable` at a computable rather than
primitive recursive enumeration.
Source: mandate L3.5 (the `[IsLogicalInductor Q DP]` instance is T7); `li-pseudorandom-open.txt`
(`starDP_computable`)
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem leakDP_computable : ComputableDeductiveProcess (leakDP T) := by
  sorry

end Theory

end Cleanroom.Bli.BliLeak
