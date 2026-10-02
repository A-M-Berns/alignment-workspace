import Cleanroom.Li.LiCoupledPair.B.Conditioned
import Cleanroom.Li.LiCoupledPair.Defs

/-!
# `li-coupled-pair` · B · Sibling: the sealed sibling by conditioning (T4.1, angle B's witness)

[[frozen-deliberation-deference-v6]] §2–§6 (anson-016/017): the sibling `H^{[N]}` is the reader
whose process holds `A`'s quotes `a₁, …, a_{N−1}` as facts, **frozen there** — "quotes of index
`≥ N` are never injected". Angle A builds it as FAF's LIA over `extendBy base (siblingSchedule a e N)`
(`Defs.lean`); this file builds it by **conditioning**, so the reconciler has two witnesses: a fixed
inductor `P` over `DPH0` conditioned on the growing conjunction of the **frozen clocked sequence**
`frozenSeq c₁ σ N` — `clockedSeq c₁ σ` with every position whose day is `≥ N` replaced by `⊤`.

* `sibling_inductor_B` — `H^{[N]}` is an inductor over `DPH0 ∪ prefixProcess (frozenSeq c₁ σ N)`.
  Kind C, hypotheses (a) throughout: the certificate is `frozenSeq_codes` (one more `ifZero` on the
  day test, a `UnaryRuler.ite_lt_const`).
* `ledgerLuv_determinedVia_sibling` — for `n < N`, `α_{j,n}` is determined at `a j n`; for `n ≥ N`
  **nothing is stated** and `sibling_frozen` says why: no day-`≥ N` literal is in any stage. No junk
  value (mandate T4 traps).
* `sibling_agree_below` — for `s < N` the sibling's stage `s` **is** the full clocked process's
  stage `s`: the sibling and `H⁺` are the same process until stage `N` (positions `≤ s < N` carry
  days `≤ s < N`). This is the mandate's `sibling_agree_below`, at the level of stages.
* `frozenSeq_literal_mem_siblingSchedule` — every literal the frozen sequence writes is a literal
  of angle A's `siblingSchedule a σ N`: the two witnesses decide the same literal set, at different
  stages.
* N+: `siblingPrefix_ne_succ` — the day-`N` literal (threshold `−1`, affirmed) is in some stage of
  the `(N+1)`-sibling's prefix process and in no stage of the `N`-sibling's, so the family varies
  with `N`.

Scope: one-way per `N` (`A` fixed); the family is the two-way object only once `A` reads it
(`SealedSiblingSystem`, angle A). The table is any computable `[0,1]`-table; at a LIA table
`a j n = liaQuote DPA n (quoted j n)` the program `c₁` is `gateCode_exists` on
`liaQuote_computable` (`ConditionedWitness.lean`).
-/

namespace Cleanroom.Li.LiCoupledPair.B

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc
open Nat.Partrec (Code)

attribute [local irreducible] Nat.sqrt

/-! ## A. The frozen clocked sequence -/

/-- **The frozen clocked sequence**: `clockedSeq c₁ σ` with every position whose day is `≥ N`
replaced by `⊤` — the corpus's `Q^{<N}`, "quotes of index `≥ N` are never injected".
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016, "frozen there"); mandate T4.1 (angle B's route)
Kind: D
Fidelity: exact (freezing); the clocked positions as in `clockedSeq`
Hyps: n/a -/
def frozenSeq (c₁ : Code) (σ : ℕ → PublicationSchedule) (N t : ℕ) : Sentence :=
  if posDay t < N then clockedSeq c₁ σ t else ⊤

/-- The frozen sequence is machine-metered: one `ifZero` on the day test over `clockedSeq_codes`.
Source: mandate T4.1 (angle B); FAF `MachineSentenceCodes.ifZero`, `UnaryRuler.ite_lt_const`
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem frozenSeq_codes (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2) (N : ℕ) :
    MachineSentenceCodes (frozenSeq c₁ σ N) := by
  have ht : UnaryRuler fun t => if posDay t < N then 0 else 1 :=
    (UnaryRuler.ite_lt_const N 0 1).comp posDay_ruler
  refine ((clockedSeq_codes c₁ σ hσ).ifZero (MachineSentenceCodes.const ⊤) ht).of_eq fun t => ?_
  unfold frozenSeq
  by_cases h : posDay t < N <;> simp [h]

/-- **The sealed sibling's process** `DPH0 ⊕ Q^{<N}` by conditioning: the base with the frozen
clocked sequence adjoined through FAF's `prefixProcess`.
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016); mandate T4.1
Kind: D
Fidelity: exact (freezing); clocked positions
Hyps: n/a -/
def siblingProcessB (DPH0 : DeductiveProcess) (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (N : ℕ) : DeductiveProcess :=
  DPH0.union (prefixProcess (frozenSeq c₁ σ N))

/-- The sibling's day-`n` condition: the prefix conjunction of the frozen sequence.
Source: FAF `lic_conditioned_growing_ofSequence`
Kind: D
Fidelity: exact
Hyps: n/a -/
def siblingCondition (c₁ : Code) (σ : ℕ → PublicationSchedule) (N n : ℕ) : Sentence :=
  sentenceConjunction ((List.range (n + 1)).map (frozenSeq c₁ σ N))

/-- **The sealed sibling `H^{[N]}` by conditioning**: `P | (frozen prefix conjunction)`.
Source: [[frozen-deliberation-deference-v6]] §3, §5 (anson-016); mandate T4.1 (angle B)
Kind: D
Fidelity: exact (FAF's capped conditional quote; module docstring of `Conditioned.lean`)
Hyps: n/a -/
noncomputable def siblingHistoryB (P : History) (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (N : ℕ) : History :=
  conditionedHistory P (siblingCondition c₁ σ N)

/-- **T4.1 (angle B's witness): the sealed sibling is a logical inductor** over its frozen process,
for every `N` — FAF's `thm:scon` at the frozen clocked sequence, certificate `frozenSeq_codes`.
Scope: one-way per `N` (`A` fixed).
Source: [[frozen-deliberation-deference-v6]] §2–§6 (anson-016/017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); mandate T4.1
Kind: L (one application of FAF's endpoint; the content is `frozenSeq_codes` with `sibling_frozen`, `sibling_agree_below`, `ledgerLuv_determinedVia_sibling`)
Fidelity: variant: plain trader class; FAF's capped conditional; clocked positions
Hyps: (a) none (`hσ` discharged at the witness) -/
theorem sibling_inductor_B (P : History) (DPH0 : DeductiveProcess) [IsLogicalInductor P DPH0]
    (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2) (N : ℕ) :
    IsLogicalInductor (siblingHistoryB P c₁ σ N) (siblingProcessB DPH0 c₁ σ N) :=
  ConditioningCompile.lic_conditioned_growing_ofSequence P DPH0 (frozenSeq c₁ σ N)
    (frozenSeq_codes c₁ σ hσ N)

/-! ## B. Determined below `N`, frozen at and above -/

/-- Below `N` every ledger literal is eventually written by the frozen sequence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frozenSeq_eventually {a : ℕ → ℕ → ℚ} (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (N j n c : ℕ) (hn : n < N)
    (hd : (Encodable.decode (α := ℚ) c).isSome = true) :
    ∃ t, frozenSeq c₁ σ N t = literalOf (ledgerEntry a j n c) := by
  obtain ⟨t, hp, ht⟩ := clockedSeq_eventually c₁ σ hc j n c hd
  refine ⟨t, ?_⟩
  have hday : posDay t = n := by rw [posDay, hp, ledgerPayload]; simp
  unfold frozenSeq
  rw [hday, if_pos hn, ht]

/-- **Determinacy below `N`**: for `n < N`, every completed-theory world of the sibling's process
values `α_{j,n}` at `a j n`. For `n ≥ N` nothing is stated (`sibling_frozen`).
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016: `a₁ … a_{N−1}` as facts); mandate T4.1 `sibling_determined`
Kind: C
Fidelity: exact (li-quote-lane's disclosures (α)(β))
Hyps: (a) none -/
theorem ledgerLuv_determinedVia_sibling {a : ℕ → ℕ → ℚ} (DPH0 : DeductiveProcess) (c₁ : Code)
    (σ : ℕ → PublicationSchedule) (hc : ∀ p, c₁.eval p = Part.some (gateVal a p))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (N j n : ℕ) (hn : n < N) :
    LUV.DeterminedVia (ledgerLuv j n) (siblingProcessB DPH0 c₁ σ N) (a j n) := by
  intro v hv
  unfold PCWorld.ValuesAt
  refine ⟨by exact_mod_cast (hmem j n).1, by exact_mod_cast (hmem j n).2, fun r => ?_⟩
  obtain ⟨t, ht⟩ := frozenSeq_eventually c₁ σ hc N j n (Encodable.encode r) hn (by simp)
  have hholds : v.Holds (literalOf (ledgerEntry a j n (Encodable.encode r))) := by
    rw [← ht]
    have hmem' : frozenSeq c₁ σ N t ∈ (siblingProcessB DPH0 c₁ σ N).D t :=
      Finset.mem_union_right _ (self_mem_prefixProcess _ le_rfl)
    exact hv t _ hmem'
  simp only [ledgerEntry, ratOfCode_encode] at hholds
  constructor
  · intro hr
    have hr' : r < a j n := by exact_mod_cast hr
    rw [decide_eq_true hr', literalOf_true] at hholds
    exact hholds
  · intro hr
    have hr' : a j n ≤ r := by exact_mod_cast hr.le
    rw [decide_eq_false (not_lt.mpr hr'), literalOf_false, PCWorld.holds_neg] at hholds
    exact hholds

/-- **Frozen: never injected.** No family-3 literal of a day `n ≥ N` is in any stage of the
sibling's prefix process — the corpus's "quotes of index `≥ N` are never injected", exactly.
Source: [[frozen-deliberation-deference-v6]] §3 (anson-016); mandate T4 traps (no junk value for `n ≥ N`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sibling_frozen (c₁ : Code) (σ : ℕ → PublicationSchedule) (N j n c s : ℕ) (hn : N ≤ n)
    (b : Bool) :
    literalOf (ledgerFamily, ledgerPayload j n c, b) ∉ (prefixProcess (frozenSeq c₁ σ N)).D s := by
  intro hmem
  obtain ⟨t, -, ht⟩ := mem_prefixProcess.mp hmem
  unfold frozenSeq at ht
  split_ifs at ht with hlt
  · obtain ⟨hp, -⟩ := clockedSeq_eq_literal_imp c₁ σ t _ b ht
    have hday : posDay t = n := by rw [posDay, ← hp, ledgerPayload]; simp
    omega
  · exact literalOf_ne_top _ b ht.symm

/-- **The sibling is `H⁺` until stage `N`**: for `s < N` the sibling's stage `s` equals the full
clocked process's stage `s` (positions `≤ s` carry days `≤ s < N`, so nothing is frozen yet).
Source: mandate T4.1 `sibling_agree_below` ("the sibling *is* `H⁺` until the day-`N` quote is published"); anson-016
Kind: P
Fidelity: exact (at the level of stages, which is what the LIA/conditioning recursion reads)
Hyps: (a) none -/
theorem sibling_agree_below (DPH0 : DeductiveProcess) (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (N s : ℕ) (hs : s < N) :
    (siblingProcessB DPH0 c₁ σ N).D s = (clockedProcess DPH0 c₁ σ).D s := by
  show DPH0.D s ∪ (prefixProcess (frozenSeq c₁ σ N)).D s =
    DPH0.D s ∪ (prefixProcess (clockedSeq c₁ σ)).D s
  congr 1
  ext φ
  rw [mem_prefixProcess, mem_prefixProcess]
  constructor
  · rintro ⟨t, hts, rfl⟩
    refine ⟨t, hts, ?_⟩
    unfold frozenSeq
    rw [if_pos (by have := posDay_le t; omega)]
  · rintro ⟨t, hts, rfl⟩
    refine ⟨t, hts, ?_⟩
    unfold frozenSeq
    rw [if_pos (by have := posDay_le t; omega)]

/-! ## C. Non-vacuity of the world quantifier, and the relation to angle A's schedule -/

/-- Every literal the frozen sequence writes is a literal of angle A's `siblingSchedule a σ N` at
some stage: the two sibling witnesses decide the same literal set (A's at its scheduled stages,
B's at clocked positions).
Source: mandate T4.1 (two witnesses for the reconciler); angle A `siblingSchedule_mem_iff`
Kind: L
Fidelity: n/a -/
theorem frozenSeq_literal_mem_siblingSchedule {a : ℕ → ℕ → ℚ} (c₁ : Code)
    (σ : ℕ → PublicationSchedule) (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (N t : ℕ) :
    frozenSeq c₁ σ N t = ⊤ ∨
      ∃ s x, x ∈ (Cleanroom.Li.LiCoupledPair.siblingSchedule a σ N).lits s ∧
        frozenSeq c₁ σ N t = literalOf x := by
  unfold frozenSeq
  by_cases hlt : posDay t < N
  · rw [if_pos hlt]
    rcases clockedSeq_cases c₁ σ hc t with h0 | ⟨n, j, c, hd, hs, hp, hlit⟩
    · exact Or.inl h0
    · right
      have hday : posDay t = n := by rw [posDay, hp, ledgerPayload]; simp
      refine ⟨max (max n j) (max c ((σ j).e n)), ledgerEntry a j n c, ?_, hlit⟩
      rw [Cleanroom.Li.LiCoupledPair.siblingSchedule_lits, List.mem_toFinset,
        Cleanroom.Li.LiCoupledPair.mem_siblingEntries, ← List.mem_toFinset, ← ledgerSchedule_lits]
      refine ⟨mem_ledgerSchedule_iff.mpr ⟨n, j, c, le_max_of_le_left (le_max_left _ _),
        le_max_of_le_left (le_max_right _ _), le_max_of_le_right (le_max_left _ _),
        le_max_of_le_right (le_max_right _ _), hd, rfl⟩, ?_⟩
      simp only [Cleanroom.Li.LiCoupledPair.entryDay, ledgerEntry, ledgerPayload, Nat.unpair_pair]
      omega
  · rw [if_neg hlt]; exact Or.inl rfl

/-- **Non-vacuity**: under li-quote-lane T1.5's hypotheses the override world is consistent with
every stage of the sibling's process (each position is `⊤` or a literal of `ledgerSchedule a σ`).
Source: mandate T4.1 `sibling_hworld`; li-quote-lane T1.5
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem siblingProcessB_theoryWorld {a : ℕ → ℕ → ℚ} {DPH0 : DeductiveProcess} {c₁ : Code}
    {σ : ℕ → PublicationSchedule} (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (N : ℕ)
    (hfree : ProcessFreeOf (ledgerSchedule a σ) DPH0)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH0.D n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory (siblingProcessB DPH0 c₁ σ N) := by
  obtain ⟨w, hw⟩ := clockedProcess_theoryWorld hc hfree h
  refine ⟨w, fun t φ hφ => ?_⟩
  rcases Finset.mem_union.mp hφ with hbase | hpre
  · exact hw t φ (by rw [clockedProcess_D]; exact Finset.mem_union_left _ hbase)
  · obtain ⟨u, -, rfl⟩ := mem_prefixProcess.mp hpre
    unfold frozenSeq
    by_cases hlt : posDay u < N
    · rw [if_pos hlt]
      exact hw u _ (by rw [clockedProcess_D]
                       exact Finset.mem_union_right _ (self_mem_prefixProcess _ le_rfl))
    · rw [if_neg hlt]; exact PCWorld.holds_top w

/-- `hworld` for the sibling's process.
Source: mandate T4.1 `sibling_hworld`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem siblingProcessB_hworld {a : ℕ → ℕ → ℚ} {DPH0 : DeductiveProcess} {c₁ : Code}
    {σ : ℕ → PublicationSchedule} (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (N : ℕ)
    (hfree : ProcessFreeOf (ledgerSchedule a σ) DPH0)
    (h : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH0.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((siblingProcessB DPH0 c₁ σ N).D n) :=
  let ⟨v, hv⟩ := siblingProcessB_theoryWorld hc N hfree h
  fun n => ⟨v, hv n⟩

/-! ## D. N+: the family varies with `N` -/

/-- **The sibling family varies with `N`** (N+ grounds): for a `[0,1]`-table the day-`N` literal
at threshold `−1` (affirmed) is in some stage of the `(N+1)`-sibling's prefix process and in no
stage of the `N`-sibling's. So `siblingProcessB … N ≠ siblingProcessB … (N+1)` whenever the base
does not itself contain that literal (every family-3-free base).
Source: mandate T4.1 (N+: `siblingProcess … N ≠ siblingProcess … (N+1)`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem siblingPrefix_ne_succ {a : ℕ → ℕ → ℚ} (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1)
    (N : ℕ) :
    (∃ s, freshAtom ledgerFamily (ledgerPayload 0 N (Encodable.encode (-1 : ℚ))) ∈
        (prefixProcess (frozenSeq c₁ σ (N + 1))).D s) ∧
      ∀ s, freshAtom ledgerFamily (ledgerPayload 0 N (Encodable.encode (-1 : ℚ))) ∉
        (prefixProcess (frozenSeq c₁ σ N)).D s := by
  constructor
  · obtain ⟨t, ht⟩ := frozenSeq_eventually c₁ σ hc (N + 1) 0 N (Encodable.encode (-1 : ℚ))
      (by omega) (by simp)
    refine ⟨t, ?_⟩
    have hlit : literalOf (ledgerEntry a 0 N (Encodable.encode (-1 : ℚ))) =
        freshAtom ledgerFamily (ledgerPayload 0 N (Encodable.encode (-1 : ℚ))) := by
      have : (-1 : ℚ) < a 0 N := by linarith [(hmem 0 N).1]
      simp [ledgerEntry, this]
    rw [← hlit, ← ht]
    exact self_mem_prefixProcess _ le_rfl
  · intro s
    have := sibling_frozen c₁ σ N 0 N (Encodable.encode (-1 : ℚ)) s le_rfl true
    rwa [literalOf_true] at this

end Cleanroom.Li.LiCoupledPair.B
