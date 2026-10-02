import Cleanroom.Found.LiQuoteLane.OneWay
import LogicalInduction.Construction.Conditioning.Endpoints

/-!
# `li-quote-lane` · Conditioning: the conditioning route to the one-way pair (T6.3, stretch)

anson-2-002's alternative construction of `H⁺`: instead of *extending* `H`'s deductive process by
the ledger (T6.1, `OneWay.lean`), *condition* an inductor `H` over `DP_H` on the growing
conjunction of the ledger literals — FAF's `thm:scon` endpoint
`lic_conditioned_growing_ofSequence` (`Construction/Conditioning/Endpoints.lean`), which takes an
inductor over `DP_H` and an efficiently codeable sentence sequence `ψ` (`MachineSentenceCodes ψ`)
and returns `conditionedHistory H (ψ₀ ⋏ ⋯ ⋏ ψₙ)` as an inductor over `DP_H ∪ prefixProcess ψ`.

**The ledger as a conditioning sequence.** `ledgerSeq a e t` unpairs `t` into a ledger payload
`⟨n, ⟨j, c⟩⟩` and a delay `d`; it is the ledger literal `literalOf (ledgerEntry a j n c)` when `c`
codes a rational and the item is published by stage `t` (`(e j).e n ≤ t`), and `⊤` otherwise.
Every ledger literal appears at some index (`d ≥ (e j).e n`), so the conditioned process decides
every threshold of every `ledgerLuv j n` at the published value, exactly as T1.2 does for the
extension route (`ledgerLuv_determinedVia_conditioned`), and its stages are all satisfiable when
T1.5's hypotheses hold (`ledgerConditionedProcess_theoryWorld`: the world T1.5 gives for the
extension route is consistent with every stage here too).

**The (c), explicit.** `MachineSentenceCodes (ledgerSeq a e)` asks for a machine-metered token
stream writing out `ledgerSeq a e t` — whose polarity is `decide (ratOfCode c < a j n)`, i.e. the
published number itself must be produced within the stream's metering. The source
(anson-2-002's existence lemma) obtains this from a *cost-domination* schedule `e(i) ≥ T_A(i)`
(the quote's production cost is absorbed into publication latency; findings F8), which FAF cannot
express: `MarketComputation` carries no runtime. So over FAF the certificate is carried as a
hypothesis `hψ`, classified **(c)** — a hypothesis in place of the source's cost-domination
schedule — and is *not* derived for a LIA table (`conditioningRoute_ofLIA` states the LIA
instance with `hψ` explicit). Compare T6.1, which needs only `ComputableDeductiveProcess` and
no delay: the extension route is simpler over FAF; that is a comparison, not a vindication.

**Not claimed.** No witness of `hψ` is shipped (it would need FAF's write-out calculus for the
literal shell around a poly-time table; not attempted — the row says so). FAF's
`conditionalQuote` is `1` at a zero-price condition (`Properties/Conditioning.lean`), so the
conditioned prices are meaningful only where `H` keeps the growing conjunction at positive
price; the criterion itself (the theorem below) does not need that (the source's obligation
(iii), positivity via uniform non-dogmatism, is about the prices, not the criterion). Scope:
one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc

-- FAF's gotcha (`notes/lean-gotchas.md`, as in `Computability.lean`): keep the unifier from
-- evaluating `Nat.unpair` on open terms when it unfolds `ledgerSeq`.
attribute [local irreducible] Nat.sqrt

/-- The ledger index carried by a conditioning-sequence position `t = ⟨⟨n, ⟨j, c⟩⟩, d⟩`:
`(n, j, c)` (the delay `d` is discarded).
Source: none: infrastructure (T6.3)
Kind: D
Fidelity: n/a -/
def ledgerIndex (t : ℕ) : ℕ × ℕ × ℕ :=
  ((Nat.unpair (Nat.unpair t).1).1, (Nat.unpair (Nat.unpair (Nat.unpair t).1).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair t).1).2).2)

/-- `ledgerIndex` inverts the packing `⟨ledgerPayload j n c, d⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ledgerIndex_pair (j n c d : ℕ) :
    ledgerIndex (Nat.pair (ledgerPayload j n c) d) = (n, j, c) := by
  simp [ledgerIndex, ledgerPayload, Nat.unpair_pair]

/-- **The ledger as a conditioning sequence** (anson-2-002's `Q_A`): position `t` carries the
ledger literal for the payload `⟨n, ⟨j, c⟩⟩` it unpairs to, when `c` codes a rational and the item
is published by stage `t`; otherwise the neutral `⊤`. Every ledger literal occurs at some
position (any delay `d ≥ (e j).e n`).
Source: anson-2-002 (chat 05 `Lemma [Existence]`: the conditioning sequence `Q_A^{(t)}`); mandate T6.3
Kind: D
Fidelity: variant: one literal per position with a delay coordinate, in place of the source's per-stage conjunction of all quotes published so far (the same literals, decided eventually)
Hyps: n/a -/
def ledgerSeq (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (t : ℕ) : Sentence :=
  if (Encodable.decode (α := ℚ) (ledgerIndex t).2.2).isSome = true ∧
      (e (ledgerIndex t).2.1).e (ledgerIndex t).1 ≤ t then
    literalOf (ledgerEntry a (ledgerIndex t).2.1 (ledgerIndex t).1 (ledgerIndex t).2.2)
  else ⊤

/-- At a published, well-coded position the conditioning sequence is the ledger literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ledgerSeq_eq_literal (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (j n c d : ℕ)
    (hc : (Encodable.decode (α := ℚ) c).isSome = true)
    (hd : (e j).e n ≤ Nat.pair (ledgerPayload j n c) d) :
    ledgerSeq a e (Nat.pair (ledgerPayload j n c) d) = literalOf (ledgerEntry a j n c) := by
  simp only [ledgerSeq, ledgerIndex_pair]
  rw [if_pos ⟨hc, hd⟩]

/-- Every position of the conditioning sequence is `⊤` or a published, well-coded ledger literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ledgerSeq_cases (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (t : ℕ) :
    ledgerSeq a e t = ⊤ ∨ ∃ n j c, (Encodable.decode (α := ℚ) c).isSome = true ∧
      (e j).e n ≤ t ∧ ledgerSeq a e t = literalOf (ledgerEntry a j n c) := by
  unfold ledgerSeq
  split_ifs with h
  · exact Or.inr ⟨_, _, _, h.1, h.2, rfl⟩
  · exact Or.inl rfl

/-- The day-`n` condition of the route: the prefix conjunction `ψ₀ ⋏ ⋯ ⋏ ψₙ` of the ledger
sequence (FAF's `sentenceConjunction`, with a harmless `⊤` terminator).
Source: anson-2-002 (`H⁺ := H | Q_A`); FAF `lic_conditioned_growing_ofSequence`
Kind: D
Fidelity: exact
Hyps: n/a -/
def ledgerCondition (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (n : ℕ) : Sentence :=
  sentenceConjunction ((List.range (n + 1)).map (ledgerSeq a e))

/-- The conditioned process of the route: `DP_H ∪ prefixProcess (ledgerSeq a e)` — stage `t`
holds `DP_H`'s stage `t` and the ledger literals at positions `≤ t`.
Source: anson-2-002; FAF `prefixProcess`
Kind: D
Fidelity: exact
Hyps: n/a -/
def ledgerConditionedProcess (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) : DeductiveProcess :=
  DPH.union (prefixProcess (ledgerSeq a e))

/-- The conditioned market of the route: `H⁺ = H | (ψ₀ ⋏ ⋯ ⋏ ψₙ)` on day `n` (FAF's
`conditionedHistory` with its capped `conditionalQuote`).
Source: anson-2-002 (`H⁺ := H | Q_A`); FAF `conditionedHistory`
Kind: D
Fidelity: exact (FAF's capped conditional: `1` at a zero-price condition, module docstring)
Hyps: n/a -/
noncomputable def ledgerConditionedHistory (P : History) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) : History :=
  conditionedHistory P (ledgerCondition a e)

/-- **T6.3 (stretch). The conditioning route, with its certificate explicit:** for any inductor
`P` over `DP_H`, if the ledger sequence is efficiently codeable (`hψ`), conditioning `P` on the
prefix conjunctions of the ledger yields a logical inductor over `DP_H ∪ prefixProcess (ledgerSeq
a e)`. This is FAF's `lic_conditioned_growing_ofSequence` at the ledger sequence; the content of
the route is the (c) `hψ` (module docstring, findings F8). Scope: one-way.
Source: anson-2-002 (chat 05 `Lemma [Existence]`, the `H⁺ = H | Q_A` clause); mandate T6.3; FAF `lic_conditioned_growing_ofSequence`
Kind: L (one application of FAF's endpoint at the ledger sequence; the route's content is the definitions and the (c) — audit r2 adversarial non-blocking 5; the composition with determinacy is `conditioningRoute_ofLIA`, Kind C)
Fidelity: variant: plain trader class; the source's cost-domination schedule replaced by the certificate `hψ`
Hyps: (c) `hψ : MachineSentenceCodes (ledgerSeq a e)` — in place of the source's `e(i) ≥ T_A(i)`, which FAF cannot state; not derived for a LIA table; all else (a) -/
theorem conditioningRoute_inductor (P : History) (DPH : DeductiveProcess)
    [IsLogicalInductor P DPH] (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule)
    (hψ : MachineSentenceCodes (ledgerSeq a e)) :
    IsLogicalInductor (ledgerConditionedHistory P a e) (ledgerConditionedProcess DPH a e) :=
  ConditioningCompile.lic_conditioned_growing_ofSequence P DPH (ledgerSeq a e) hψ

/-- A world consistent with every stage of the conditioned process affirms `⌜α_{j,n} > r⌝` when
`r < a j n` and denies it when `a j n ≤ r`: the literal sits at position
`⟨ledgerPayload j n ⌜r⌝, (e j).e n⟩`.
Source: mandate T6.3 (the route's determinacy, as T1.2's stage form)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ledgerSeq_decides (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (j n : ℕ) (r : ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerConditionedProcess DPH a e)) :
    (r < a j n → v.Holds ((ledgerLuv j n).gt r)) ∧
      (a j n ≤ r → ¬ v.Holds ((ledgerLuv j n).gt r)) := by
  have hc : (Encodable.decode (α := ℚ) (Encodable.encode r)).isSome = true := by simp
  have hd : (e j).e n ≤ Nat.pair (ledgerPayload j n (Encodable.encode r)) ((e j).e n) :=
    Nat.right_le_pair _ _
  have hψ := ledgerSeq_eq_literal a e j n (Encodable.encode r) ((e j).e n) hc hd
  have hholds : v.Holds (literalOf (ledgerEntry a j n (Encodable.encode r))) := by
    rw [← hψ]
    have hmem : ledgerSeq a e (Nat.pair (ledgerPayload j n (Encodable.encode r)) ((e j).e n)) ∈
        (ledgerConditionedProcess DPH a e).D
          (Nat.pair (ledgerPayload j n (Encodable.encode r)) ((e j).e n)) := by
      show _ ∈ DPH.D _ ∪ (prefixProcess (ledgerSeq a e)).D _
      exact Finset.mem_union_right _ (self_mem_prefixProcess _ le_rfl)
    exact hv (Nat.pair (ledgerPayload j n (Encodable.encode r)) ((e j).e n)) _ hmem
  simp only [ledgerEntry, ratOfCode_encode] at hholds
  constructor
  · intro hr
    rw [decide_eq_true hr, literalOf_true] at hholds
    exact hholds
  · intro hr
    rw [decide_eq_false (not_lt.mpr hr), literalOf_false, PCWorld.holds_neg] at hholds
    exact hholds

/-- **The route's determinacy**: every completed-theory world of the conditioned process values
`α_{j,n}` at the published number — T1.2 for the conditioning route.
Source: mandate T6.3; T1.2 (`ledgerLuv_determinedVia`) transported to `prefixProcess`
Kind: C
Fidelity: exact, with T1.1's disclosures (α)(β)
Hyps: (a) none (`hmem` is the `[0,1]` range of the table) -/
theorem ledgerLuv_determinedVia_conditioned (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) (ledgerConditionedProcess DPH a e) (a j n) := by
  intro v hv
  unfold PCWorld.ValuesAt
  refine ⟨by exact_mod_cast (hmem j n).1, by exact_mod_cast (hmem j n).2, fun r => ?_⟩
  have h := ledgerSeq_decides DPH a e j n r v hv
  exact ⟨fun hr => h.1 (by exact_mod_cast hr), fun hr => h.2 (by exact_mod_cast hr.le)⟩

/-- **Non-vacuity of the route's world quantifier**: under T1.5's hypotheses (base free of family
3, every stage satisfiable), the world T1.5 + compactness gives for the extension route
(`ledgerProcess_theoryWorld`) is consistent with every stage of the conditioned process too —
each position of the ledger sequence is `⊤` or a ledger literal that some stage of
`ledgerProcess` holds.
Source: mandate T6.3 (non-vacuity); T1.5
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerConditionedProcess_theoryWorld {DPH : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory (ledgerConditionedProcess DPH a e) := by
  obtain ⟨w, hw⟩ := ledgerProcess_theoryWorld hfree h
  refine ⟨w, fun t φ hφ => ?_⟩
  change φ ∈ DPH.D t ∪ (prefixProcess (ledgerSeq a e)).D t at hφ
  rcases Finset.mem_union.mp hφ with hbase | hpre
  · exact hw t φ (by rw [ledgerProcess_D]; exact Finset.mem_union_left _ hbase)
  · obtain ⟨u, -, rfl⟩ := mem_prefixProcess.mp hpre
    rcases ledgerSeq_cases a e u with h0 | ⟨n, j, c, hc, -, hlit⟩
    · rw [h0]; exact PCWorld.holds_top w
    · rw [hlit]
      have hmemS : ledgerEntry a j n c ∈
          (ledgerSchedule a e).lits (max (max n j) (max c ((e j).e n))) :=
        mem_ledgerSchedule_iff.mpr ⟨n, j, c, le_max_of_le_left (le_max_left _ _),
          le_max_of_le_left (le_max_right _ _), le_max_of_le_right (le_max_left _ _),
          le_max_of_le_right (le_max_right _ _), hc, rfl⟩
      apply hw (max (max n j) (max c ((e j).e n)))
      rw [ledgerProcess_D, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨_, hmemS, rfl⟩)

/-- `hworld` for the conditioned process (the per-stage form of the theory world).
Source: mandate T6.3 (non-vacuity); T1.5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerConditionedProcess_hworld {DPH : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerConditionedProcess DPH a e).D n) :=
  let ⟨v, hv⟩ := ledgerConditionedProcess_theoryWorld hfree h
  fun n => ⟨v, hv n⟩

/-- **T6.3 at a LIA table, the certificate explicit:** with `A := liaHistory DPA` and the table
`a j n := liaQuote DPA n (quoted j n)`, conditioning any inductor `P` over `DP_H` on the ledger
sequence gives an inductor over the conditioned process, in whose every completed-theory world
`α_{j,n}` is valued at `A`'s quote — **given** `hψ : MachineSentenceCodes` of that ledger
sequence, which is the hypothesis FAF cannot discharge for a LIA table (the source discharges it
from a cost-domination schedule; findings F8). Scope: one-way.
Source: anson-2-002 (`Lemma [Existence]`); mandate T6.3
Kind: C
Fidelity: variant: plain trader class; the source's cost-domination schedule replaced by `hψ`
Hyps: (c) `hψ` (as in `conditioningRoute_inductor`); all else (a) -/
theorem conditioningRoute_ofLIA (DPA DPH : DeductiveProcess) (P : History)
    [IsLogicalInductor P DPH] (quoted : ℕ → ℕ → Sentence) (e : ℕ → PublicationSchedule)
    (hψ : MachineSentenceCodes (ledgerSeq (fun j n => liaQuote DPA n (quoted j n)) e)) :
    IsLogicalInductor
        (ledgerConditionedHistory P (fun j n => liaQuote DPA n (quoted j n)) e)
        (ledgerConditionedProcess DPH (fun j n => liaQuote DPA n (quoted j n)) e) ∧
      ∀ j n, LUV.DeterminedVia (ledgerLuv j n)
        (ledgerConditionedProcess DPH (fun j n => liaQuote DPA n (quoted j n)) e)
        (liaQuote DPA n (quoted j n)) :=
  ⟨conditioningRoute_inductor P DPH _ e hψ,
    fun j n => ledgerLuv_determinedVia_conditioned DPH _ e
      (fun j n => liaQuote_mem DPA n (quoted j n)) j n⟩

end Cleanroom.Found.LiQuoteLane
