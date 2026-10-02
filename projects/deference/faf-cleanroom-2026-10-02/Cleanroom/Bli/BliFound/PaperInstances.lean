import Cleanroom.Bli.BliFound.State
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Quotation.ProductDefinition

/-!
# `bli-found` · PaperInstances: disjointness from FAF's atoms, and the `paperDP` instances

The construction-facing half of D1, D2 and D4, kept in its own file because it imports
`Construction.Paper.TheoremDP` (the heaviest import of the package):

* **Disjointness**: a fresh atom is never a quotation atom (`quoteAtom`, tag `2`), a quoted
  product (`productAtom`, tag `3`), a first-order prime (`paperPrimeSentence`, tag `5`) or an
  event atom of `theoremDP` (`eventAtom`: tags `0`–`2` and negations / `⊤`).
* **Process facts**: `theoremDP T`, `paperTheoryDP T` and `paperDP T` are `CleanroomFreeProcess`
  (every atom they emit has tag `< 9`), modelled on FAF's `theoremDP_atomCodes_ne_productTag`;
  instantiated at `T := 𝗜𝚺₁` to show the instances resolve.
* **N+ for D2 / T3**: a day-varying functional schedule (family `3`, payload `⟨n, k⟩`, value
  `k % 2 = 0`, entered at stage `n + 1`) adjoined to `paperDP 𝗜𝚺₁`, with `hworld` inherited
  through `paperDP_hworld`, computability through `paperDP_computable`, and conservativity
  instantiated at a concrete `paperPrimeSentence`.
* **T5.3 at a real process**: `bliDP (paperDP 𝗜𝚺₁) states actual` has a consistent world at
  every stage, for *every* `states`/`actual` (the guard against program §7.4), with exclusivity
  and conservativity; and the N+ witness with two candidates per day and a day-varying actual
  state.

Sources: mandate D1, D2, D4, T2, T3, T5.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## Disjointness from FAF's atom families -/

/-- A fresh atom is never a quotation atom (tag `2`).
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma freshAtom_ne_quoteAtom (f p w : ℕ) : freshAtom f p ≠ quoteAtom w := by
  intro h
  have h2 := sentenceAtomCodes_quoteAtom w (freshAtomCode f p) (by rw [← h]; simp)
  simp [cleanroomBaseTag] at h2
  omega

/-- A fresh atom is never a quoted-product atom (tag `3`).
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma freshAtom_ne_productAtom (f p n : ℕ) (r : ℚ) : freshAtom f p ≠ productAtom n r := by
  intro h
  unfold freshAtom productAtom at h
  have := Formula.atom.inj h
  simp only [freshAtomCode, Nat.pair_eq_pair, productTag, cleanroomBaseTag] at this
  omega

/-- A fresh atom is never a first-order prime (tag `5`).
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma freshAtom_ne_paperPrimeSentence (f p : ℕ) (b : Bool) (φ : LO.FirstOrder.ArithmeticProposition) :
    freshAtom f p ≠ paperPrimeSentence b φ := by
  intro h
  unfold freshAtom paperPrimeSentence at h
  have := congrArg (fun a => a.unpair.1) (Formula.atom.inj h)
  simp only [freshAtomCode_unpair, paperPrimeCode_unpair_tag, paperPrimeTag, cleanroomBaseTag]
    at this
  omega

/-- Every atom of an event atom of `theoremDP` has a tag below `cleanroomBaseTag`: the six
cases are computation claims (tags `0`, `1`), quotation atoms (tag `2`), their negations, and
`⊤`.
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma eventAtom_cleanroomFree (e : ℕ) : CleanroomFreeSentence (eventAtom e) := by
  intro a ha
  unfold eventAtom at ha
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m <;> simp only [h] at ha
  · -- tag 0: halting claim
    simp only [haltingClaimSentence, computationClaimSentence, sentenceAtomCodes_atom,
      Finset.mem_singleton] at ha
    subst ha
    simp [ComputationClaim.godelCode, haltingClaim, ComputationClaimKind.godelCode, cleanroomBaseTag]
  · simp only [haltingClaimSentence, computationClaimSentence, sentenceAtomCodes_neg,
      sentenceAtomCodes_atom, Finset.mem_singleton] at ha
    subst ha
    simp [ComputationClaim.godelCode, haltingClaim, ComputationClaimKind.godelCode, cleanroomBaseTag]
  · simp only [boundedHaltingClaimSentence, computationClaimSentence, sentenceAtomCodes_atom,
      Finset.mem_singleton] at ha
    subst ha
    simp [ComputationClaim.godelCode, boundedHaltingClaim, ComputationClaimKind.godelCode,
      cleanroomBaseTag]
  · simp only [boundedHaltingClaimSentence, computationClaimSentence, sentenceAtomCodes_neg,
      sentenceAtomCodes_atom, Finset.mem_singleton] at ha
    subst ha
    simp [ComputationClaim.godelCode, boundedHaltingClaim, ComputationClaimKind.godelCode,
      cleanroomBaseTag]
  · have := sentenceAtomCodes_quoteAtom _ a ha
    rw [this]; simp [cleanroomBaseTag]
  · rw [sentenceAtomCodes_neg] at ha
    have := sentenceAtomCodes_quoteAtom _ a ha
    rw [this]; simp [cleanroomBaseTag]
  · simp at ha

/-- A fresh atom is never an event atom.
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma freshAtom_ne_eventAtom (f p e : ℕ) : freshAtom f p ≠ eventAtom e := by
  intro h
  have := eventAtom_cleanroomFree e (freshAtomCode f p) (by rw [← h]; simp)
  simp [cleanroomBaseTag] at this

/-- **`theoremDP` is cleanroom-free**: every stage is an image of `eventAtom`.
Source: mandate D1 (modelled on FAF's `theoremDP_atomCodes_ne_productTag`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremDP_cleanroomFree (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] :
    CleanroomFreeProcess (theoremDP T) := by
  classical
  intro k φ hφ
  simp only [theoremDP, dovetailProcess_D, mem_dovetailStage] at hφ
  obtain ⟨e, -, rfl⟩ := hφ
  exact eventAtom_cleanroomFree e

/-- **`paperTheoryDP` is cleanroom-free**: every atom it emits carries tag `5`
(`paperTheoryDP_atom_tag`).
Source: mandate D1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem paperTheoryDP_cleanroomFree (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] :
    CleanroomFreeProcess (paperTheoryDP T) := by
  intro k φ hφ a ha
  rw [paperTheoryDP_atom_tag T hφ ha]
  simp [paperPrimeTag, cleanroomBaseTag]

/-- **`paperDP` is cleanroom-free**: the union of two cleanroom-free processes.
Source: mandate D1/T2
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem paperDP_cleanroomFree (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] :
    CleanroomFreeProcess (paperDP T) := by
  intro k φ hφ
  rw [paperDP, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  exact hφ.elim (theoremDP_cleanroomFree T k φ) (paperTheoryDP_cleanroomFree T k φ)

/-- The instances resolve at `T := 𝗜𝚺₁` (mandate T2). -/
example : CleanroomFreeProcess (paperDP 𝗜𝚺₁) := paperDP_cleanroomFree 𝗜𝚺₁

/-- `paperDP T` is tag-free for every tag this run allocates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paperDP_tagFree (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] {t : ℕ}
    (ht : cleanroomBaseTag ≤ t) : TagFreeProcess t (paperDP T) :=
  (paperDP_cleanroomFree T).tagFree ht

/-- A concrete `quoteAtom`-built family is tag-free for every run tag (the closed-instance
discharge of `TagFreeFamily`, Known issue 8).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tagFreeFamily_quoteAtom {t : ℕ} (ht : cleanroomBaseTag ≤ t) (w : ℕ → ℕ) :
    TagFreeFamily t (fun n => quoteAtom (w n)) := by
  intro n a ha
  rw [sentenceAtomCodes_quoteAtom _ a ha]
  simp only [cleanroomBaseTag] at ht
  omega

/-! ## N+ for the decided-atom extension over `paperDP 𝗜𝚺₁` (T3) -/

/-- The day-varying entries: at stage `s`, for every `n < s` and `k ≤ n`, the atom of family
`3` with payload `⟨n, k⟩` gets polarity `k % 2 = 0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def dayVaryingEntries (s : ℕ) : List (ℕ × ℕ × Bool) :=
  (List.range s).flatMap fun n => (List.range (n + 1)).map fun k => (3, Nat.pair n k, decide (k % 2 = 0))

/-- `mem_dayVaryingEntries`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_dayVaryingEntries {s : ℕ} {x : ℕ × ℕ × Bool} :
    x ∈ dayVaryingEntries s ↔ ∃ n < s, ∃ k < n + 1, x = (3, Nat.pair n k, decide (k % 2 = 0)) := by
  simp only [dayVaryingEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩
  · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩

/-- `dayVaryingEntries_mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayVaryingEntries_mono (s : ℕ) : ∀ x ∈ dayVaryingEntries s, x ∈ dayVaryingEntries (s + 1) := by
  intro x hx
  rw [mem_dayVaryingEntries] at hx ⊢
  obtain ⟨n, hn, k, hk, rfl⟩ := hx
  exact ⟨n, by omega, k, hk, rfl⟩

/-- **The day-varying schedule** (N+ instance of D2): family `3`, payload `⟨n, k⟩`, value
`k % 2 = 0`, entered at stage `n + 1`.
Source: mandate D2 (N+)
Kind: N+
Fidelity: n/a -/
def dayVaryingSchedule : LiteralSchedule :=
  LiteralSchedule.ofList dayVaryingEntries dayVaryingEntries_mono

/-- `dayVaryingSchedule_functional`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayVaryingSchedule_functional : dayVaryingSchedule.Functional := by
  rintro s f p ⟨hpos, hneg⟩
  simp only [dayVaryingSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset,
    mem_dayVaryingEntries, Prod.mk.injEq] at hpos hneg
  obtain ⟨n, -, k, -, -, rfl, hk⟩ := hpos
  obtain ⟨n', -, k', -, -, hp, hk'⟩ := hneg
  rw [Nat.pair_eq_pair] at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp at hk hk'
  omega

/-- `dayVaryingSchedule_families`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayVaryingSchedule_families : ∀ f ∈ dayVaryingSchedule.families, f = 3 := by
  rintro f ⟨s, x, hx, rfl⟩
  simp only [dayVaryingSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset,
    mem_dayVaryingEntries] at hx
  obtain ⟨n, -, k, -, rfl⟩ := hx
  rfl

/-- The schedule genuinely varies with the day: stage `n + 1` adjoins the positive literal of
`⟨n, 0⟩`, which stage `n` does not contain.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayVarying_nondegenerate (n : ℕ) :
    freshAtom 3 (Nat.pair n 0) ∈ (literalProcess dayVaryingSchedule).D (n + 1) ∧
      freshAtom 3 (Nat.pair n 0) ∉ (literalProcess dayVaryingSchedule).D n := by
  constructor
  · rw [literalProcess_D, Finset.mem_image]
    refine ⟨(3, Nat.pair n 0, true), ?_, rfl⟩
    simp only [dayVaryingSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset,
      mem_dayVaryingEntries]
    exact ⟨n, by omega, 0, by omega, by simp⟩
  · rw [literalProcess_D, Finset.mem_image]
    rintro ⟨x, hx, hlit⟩
    simp only [dayVaryingSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset,
      mem_dayVaryingEntries] at hx
    obtain ⟨n', hn', k, -, rfl⟩ := hx
    cases hk : decide (k % 2 = 0)
    · rw [hk] at hlit
      simp only [literalOf_false] at hlit
      rw [Formula.neg_def] at hlit
      unfold freshAtom at hlit
      cases hlit
    · rw [hk] at hlit
      simp only [literalOf_true] at hlit
      obtain ⟨-, hp⟩ := freshAtom_inj.mp hlit
      rw [Nat.pair_eq_pair] at hp
      omega

/-- Stage `n + 1` also carries a *negative* literal (`⟨n, 1⟩` for `n ≥ 1`), so both polarities
occur.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayVarying_has_negative {n : ℕ} (hn : 1 ≤ n) :
    (∼freshAtom 3 (Nat.pair n 1)) ∈ (literalProcess dayVaryingSchedule).D (n + 1) := by
  rw [literalProcess_D, Finset.mem_image]
  refine ⟨(3, Nat.pair n 1, false), ?_, rfl⟩
  simp only [dayVaryingSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset,
    mem_dayVaryingEntries]
  exact ⟨n, by omega, 1, by omega, by simp⟩

/-- `paperDP 𝗜𝚺₁` is free of the day-varying schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paperDP_freeOf_dayVarying : ProcessFreeOf dayVaryingSchedule (paperDP 𝗜𝚺₁) :=
  ProcessFreeOf.of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) _

/-- **N+ (T3): `hworld` of the day-varying extension of `paperDP 𝗜𝚺₁`**, from
`paperDP_hworld` through `extendBy_hworld`.
Source: mandate T3 (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem extendBy_paperDP_dayVarying_hworld :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((extendBy (paperDP 𝗜𝚺₁) dayVaryingSchedule).D n) :=
  extendBy_hworld dayVaryingSchedule_functional paperDP_freeOf_dayVarying (paperDP_hworld 𝗜𝚺₁)

/-- **N+ (T3): conservativity instantiated** at a concrete first-order prime: the day-varying
extension decides `paperPrimeSentence b ψ` iff `paperDP 𝗜𝚺₁` does.
Source: mandate T3 (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem extendBy_paperDP_dayVarying_conservative (b : Bool)
    (ψ : LO.FirstOrder.ArithmeticProposition) :
    (∀ v : PCWorld, v.ConsistentWithTheory (extendBy (paperDP 𝗜𝚺₁) dayVaryingSchedule) →
        v.Holds (paperPrimeSentence b ψ)) ↔
      (∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) → v.Holds (paperPrimeSentence b ψ)) :=
  extendBy_decidesTheory_iff dayVaryingSchedule_functional paperDP_freeOf_dayVarying
    (FreeOf.of_cleanroomFree
      (fun a ha => by
        unfold paperPrimeSentence at ha
        rw [sentenceAtomCodes_atom, Finset.mem_singleton] at ha
        subst ha
        simp [paperPrimeTag, cleanroomBaseTag]) _)

/-- `dayVaryingEntries_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayVaryingEntries_prim : Primrec dayVaryingEntries := by
  have hn : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have hk : Primrec fun r : (ℕ × ℕ) × ℕ => r.2 := Primrec.snd
  have hn' : Primrec fun r : (ℕ × ℕ) × ℕ => r.1.2 := Primrec.snd.comp Primrec.fst
  have hmod : Primrec fun r : (ℕ × ℕ) × ℕ => r.2 % 2 := Primrec.nat_mod.comp hk (Primrec.const 2)
  have hdec : Primrec fun r : (ℕ × ℕ) × ℕ => decide (r.2 % 2 = 0) := by
    obtain ⟨_, h⟩ := Primrec.eq.comp hmod (Primrec.const 0)
    exact h.of_eq fun r => by simp
  have hg : Primrec₂ fun (p : ℕ × ℕ) (k : ℕ) => (3, Nat.pair p.2 k, decide (k % 2 = 0)) :=
    ((Primrec.const 3).pair ((Primrec₂.natPair.comp hn' hk).pair hdec)).to₂
  have hinner : Primrec₂ fun (s n : ℕ) =>
      (List.range (n + 1)).map fun k => (3, Nat.pair n k, decide (k % 2 = 0)) :=
    (Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hn)) hg).to₂
  exact Primrec.list_flatMap Primrec.list_range hinner

/-- **N+ (T3): computability of the day-varying extension**, from `paperDP_computable`.
Source: mandate T3 (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem extendBy_paperDP_dayVarying_computable :
    ComputableDeductiveProcess (extendBy (paperDP 𝗜𝚺₁) dayVaryingSchedule) :=
  extendBy_ofList_computable (paperDP_computable 𝗜𝚺₁) dayVaryingEntries dayVaryingEntries_mono
    dayVaryingEntries_prim

/-! ## T5.3 at `paperDP 𝗜𝚺₁` -/

/-- **`bliDP_hworld` at a real process**: for every `states` and `actual`, every stage of
`bliDP (paperDP 𝗜𝚺₁) states actual` has a consistent world. This is the guard against program
§7.4: a wrong exclusivity clause would make stages unsatisfiable and every market an inductor.
Source: mandate T5.3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem bliDP_paperDP_hworld (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((bliDP (paperDP 𝗜𝚺₁) states actual).D n) :=
  bliDP_hworld (paperDP_tagFree 𝗜𝚺₁ le_rfl) states actual (paperDP_hworld 𝗜𝚺₁)

/-- `bliDP` over `paperDP 𝗜𝚺₁` decides nothing new about state-free sentences.
Source: mandate T5.3
Kind: C
Fidelity: variant: semantic "decided"
Hyps: (a) -/
theorem bliDP_paperDP_conservative (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) {φ : Sentence}
    (hφ : TagFreeSentence stateTag φ) :
    (∀ v : PCWorld, v.ConsistentWithTheory (bliDP (paperDP 𝗜𝚺₁) states actual) → v.Holds φ) ↔
      (∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) → v.Holds φ) :=
  bliDP_conservative (paperDP_tagFree 𝗜𝚺₁ le_rfl) states actual hφ

/-- The N+ state system for T5: two candidates every day, actual state `m % 2` (day-varying).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def twoStates : ℕ → Finset ℕ := fun _ => {0, 1}
/-- The day-varying actual state.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def alternating : ℕ → ℕ := fun m => m % 2

/-- `twoStates_card`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoStates_card (m : ℕ) : (twoStates m).card = 2 := by simp [twoStates]

/-- `alternating_varies`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma alternating_varies : alternating 0 ≠ alternating 1 := by simp [alternating]

/-- **N+ (T5)**: `bliDP (paperDP 𝗜𝚺₁) twoStates alternating` has a consistent world at every
stage, and exclusivity is live at days `0` and `1` with the two different actual states.
Source: mandate T5 (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem bliDP_paperDP_twoStates_hworld :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((bliDP (paperDP 𝗜𝚺₁) twoStates alternating).D n) :=
  bliDP_paperDP_hworld twoStates alternating

/-- `bliDP_paperDP_twoStates_exclusive`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bliDP_paperDP_twoStates_exclusive {v : PCWorld}
    (hv : v.ConsistentWith ((bliDP (paperDP 𝗜𝚺₁) twoStates alternating).D 2)) :
    v.Holds (stateAtom 0 0) ∧ ¬ v.Holds (stateAtom 0 1) ∧
      v.Holds (stateAtom 1 1) ∧ ¬ v.Holds (stateAtom 1 0) := by
  have h := bliDP_exclusive (paperDP 𝗜𝚺₁) twoStates alternating hv
  have h00 := h 0 (by norm_num) 0 (by simp [twoStates])
  have h01 := h 0 (by norm_num) 1 (by simp [twoStates])
  have h11 := h 1 (by norm_num) 1 (by simp [twoStates])
  have h10 := h 1 (by norm_num) 0 (by simp [twoStates])
  simp only [alternating] at h00 h01 h11 h10
  refine ⟨h00.mpr (by decide), fun hh => ?_, h11.mpr (by decide), fun hh => ?_⟩
  · exact absurd (h01.mp hh) (by decide)
  · exact absurd (h10.mp hh) (by decide)

/-- `alternating_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma alternating_prim : Primrec alternating :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 2)

/-- **N+ (T5)**: the two-state `bliDP` over `paperDP 𝗜𝚺₁` is computable.
Source: mandate T5 (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem bliDP_paperDP_twoStates_computable :
    ComputableDeductiveProcess (bliDP (paperDP 𝗜𝚺₁) twoStates alternating) :=
  bliDP_computable (paperDP_computable 𝗜𝚺₁) twoStates (fun _ => [0, 1])
    (fun _ => by simp [twoStates]) (Primrec.const [0, 1]) alternating_prim

/-! ## N+ (T5) in the large regime: candidate codes with `sizeBound m + 1` digits

The `twoStates`/`alternating` witness runs the state process on codes `0`, `1`, whose atoms are
day-small (`stateAtom 2 1` is small on day `2`; audit r2 adversarial N4, probe P5). Since
`bliDP_paperDP_hworld` is universal in `states`/`actual`, the same process runs on codes in
`stateAtom_large`'s regime: two candidates a day with exactly `sizeBound m + 1` base-4 digits,
whose state atoms are large on every day `≤ m`. Both halves of D4 (the size split and the
state process) are exercised at once. -/

/-- Two candidate codes a day in the large regime: `4 ^ sizeBound m` and `4 ^ sizeBound m + 1`.
Source: mandate T5 (N+); audit r2 (adversarial N4, probe P5)
Kind: D
Fidelity: n/a -/
def largeStates : ℕ → Finset ℕ := fun m => {4 ^ sizeBound m, 4 ^ sizeBound m + 1}

/-- The actual large code alternates between the two candidates (`+ m % 2`).
Source: mandate T5 (N+); audit r2 (adversarial N4)
Kind: D
Fidelity: n/a -/
def largeActual : ℕ → ℕ := fun m => 4 ^ sizeBound m + m % 2

/-- `largeActual_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma largeActual_mem (m : ℕ) : largeActual m ∈ largeStates m := by
  have := Nat.mod_lt m (show 0 < 2 by norm_num)
  simp only [largeStates, largeActual, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Every candidate code of `largeStates m` has exactly `sizeBound m + 1` base-4 digits
(`Nat.log 4 q = sizeBound m`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma log_four_of_mem_largeStates {m q : ℕ} (hq : q ∈ largeStates m) :
    Nat.log 4 q = sizeBound m := by
  simp only [largeStates, Finset.mem_insert, Finset.mem_singleton] at hq
  have h1 : 1 ≤ 4 ^ sizeBound m := Nat.one_le_pow _ _ (by norm_num)
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · rcases hq with rfl | rfl <;> omega
  · rw [pow_succ]
    rcases hq with rfl | rfl <;> omega

/-- **Every candidate's state atom is large on every day `≤ m`** (`stateAtom_large` applied to
the large grid): the state process below runs in the regime the size split is about.
Source: mandate T5 (N+); audit r2 (adversarial N4)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem largeStates_stateAtom_large (m : ℕ) :
    ∀ q ∈ largeStates m, ∀ n ≤ m, ¬ SmallOn n (stateAtom m q) :=
  fun _ hq => stateAtom_large (by rw [log_four_of_mem_largeStates hq])

/-- **N+ (T5), large regime**: `bliDP (paperDP 𝗜𝚺₁) largeStates largeActual` has a consistent
world at every stage, with every candidate's state atom large (`largeStates_stateAtom_large`).
Source: mandate T5 (N+); audit r2 (adversarial N4)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem bliDP_paperDP_largeStates_hworld :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((bliDP (paperDP 𝗜𝚺₁) largeStates largeActual).D n) :=
  bliDP_paperDP_hworld largeStates largeActual

/-- Exclusivity is live at days `0` and `1` on the large grid, with the two different actual
codes.
Source: mandate T5 (N+); audit r2 (adversarial N4)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem bliDP_paperDP_largeStates_exclusive {v : PCWorld}
    (hv : v.ConsistentWith ((bliDP (paperDP 𝗜𝚺₁) largeStates largeActual).D 2)) :
    v.Holds (stateAtom 0 (4 ^ sizeBound 0)) ∧ ¬ v.Holds (stateAtom 0 (4 ^ sizeBound 0 + 1)) ∧
      v.Holds (stateAtom 1 (4 ^ sizeBound 1 + 1)) ∧ ¬ v.Holds (stateAtom 1 (4 ^ sizeBound 1)) := by
  have h := bliDP_exclusive (paperDP 𝗜𝚺₁) largeStates largeActual hv
  have h00 := h 0 (by norm_num) (4 ^ sizeBound 0) (by simp [largeStates])
  have h01 := h 0 (by norm_num) (4 ^ sizeBound 0 + 1) (by simp [largeStates])
  have h11 := h 1 (by norm_num) (4 ^ sizeBound 1 + 1) (by simp [largeStates])
  have h10 := h 1 (by norm_num) (4 ^ sizeBound 1) (by simp [largeStates])
  simp only [largeActual] at h00 h01 h11 h10
  refine ⟨h00.mpr (by simp), fun hh => ?_, h11.mpr (by simp), fun hh => ?_⟩
  · have := h01.mp hh
    omega
  · have := h10.mp hh
    omega

/-! ## `atomDay` on FAF's quoted products (audit r2 fidelity B1)

`productAtom n r = ⌜Xₙ · Wₙ > r⌝` (tag `3`, `Construction/Quotation/ProductDefinition.lean`) is
day-indexed. Until repair round 2 `Size.atomDay` read `0` off it, so `Sminus m m` admitted a
product atom of every day `n ≥ m` (the auditor's probe `productAtom_mem_Sminus_self`); now the
day is read exactly and no product atom of a day `≥ m` lies in `Sminus k m`. -/

/-- `atomDay` reads the day `n` off (the one atom of) `productAtom n r`.
Source: FAF `productAtom`; audit r2 (fidelity B1)
Kind: L
Fidelity: exact -/
lemma atomDay_productAtom (n : ℕ) (r : ℚ) :
    ∀ a ∈ sentenceAtomCodes (productAtom n r), atomDay a = n := by
  intro a ha
  simp only [productAtom, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  simp [atomDay, atomDayBase, productTag, cleanroomBaseTag]

/-- A day-`n` product atom lies in `Sminus k m` iff it is small on day `k` and `n < m`.
Source: audit r2 (fidelity B1)
Kind: L
Fidelity: exact -/
lemma productAtom_mem_Sminus_iff {k m n : ℕ} {r : ℚ} :
    productAtom n r ∈ Sminus k m ↔ SmallOn k (productAtom n r) ∧ n < m := by
  rw [mem_Sminus]
  have hmem : Nat.pair productTag (Nat.pair n (Encodable.encode r)) ∈
      sentenceAtomCodes (productAtom n r) := by simp [productAtom]
  constructor
  · rintro ⟨hs, hd⟩
    have := hd _ hmem
    rw [atomDay_productAtom n r _ hmem] at this
    exact ⟨hs, this⟩
  · rintro ⟨hs, hn⟩
    exact ⟨hs, fun a ha => by rw [atomDay_productAtom n r a ha]; exact hn⟩

/-- **No product atom of a day `≥ m` lies in `Sminus k m`**: the scope of faith at day `m`
excludes every quoted product of day `m` or later, as the prose scope does (bli-slides-030 "no
claims about future market states"; [[bli-program]] §2.1). Repair round 2's replacement for the
false "safe direction" claim on tag `3`.
Source: [[bli-program]] §2.1; audit r2 (fidelity B1)
Kind: L
Fidelity: exact -/
theorem productAtom_notMem_Sminus {k m n : ℕ} (r : ℚ) (h : m ≤ n) :
    productAtom n r ∉ Sminus k m := by
  rw [productAtom_mem_Sminus_iff]
  rintro ⟨-, hn⟩
  omega

end Cleanroom.Bli.BliFound
