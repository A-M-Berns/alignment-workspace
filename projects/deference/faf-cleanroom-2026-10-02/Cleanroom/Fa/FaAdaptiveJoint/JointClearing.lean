import Cleanroom.Fa.FaAdaptiveJoint.Witnesses
import LogicalInduction.Construction.MarketMaker

/-!
# `fa-adaptive-joint` · JointClearing: the Brouwer route over FAF (T9, stretch; construction-facing)

[[fa-adaptive-joint-mandate]] T9; [[fa-positive-results-corrected-v3]] §1 (A1) remark 1;
root-fa-022; lean-deference-047; vq-wiki-034/035; [[delay-program]] §1. FAF's `Sentence` is
`LO.Propositional.Formula ℕ`, so a disjoint-union language is an **atom renaming**: even atoms for
`H`'s language (`sentH`), odd for `A`'s (`sentA`). One FAF market `M` over the merged process
`mergedProcess DPH DPA` (`D n := sentH '' DPH.D n ∪ sentA '' DPA.D n`) prices both sides at once;
`H`'s and `A`'s markets are its projections `sideH M` / `sideA M`, and every `EF` trader on it
reads both price streams on the same day: v3's (A1) verbatim. Sections C–E were reshaped in repair
round 1 (audit r1 B1/B2: the old per-day theorem was FAF's lemma plus a tautology; the old carrier
did not tie its families to the two halves). What is proved here:

* the world side of the projection lemma (a): a merged world restricts to one on each half
  (`PCWorld.projH`/`projA`), consistency with a merged stage is consistency with each stage
  (`consistentWith_mergedStage_iff`), and, the halves sharing no atoms, any two half-worlds glue
  (`PCWorld.glue`; `glue_proj`: every merged world *is* a pair), so the merged process is
  satisfiable iff both are (`mergedProcess_hworld_iff`);
* the per-day joint fixed point (`jointClearing_perDay_fixedPoint`): a day-`n` strategy trading
  only `H`-tagged sentences and one trading only `A`-tagged ones — both reading merged prices —
  clear together under one `[0,1]` valuation against **every pair of half-worlds**, each side
  valued by its own world. The Brouwer content is FAF's `fixed_point_lemma` on the concatenated
  strategy; what is added is the concatenation and the gluing — which is why v3's "fixed point over
  the pair of price vectors at once" needs no new Brouwer argument;
* the trader side of the projection lemma (a) (`jointClearing_criterion_projection`, the
  mandate's deliverable): an `H`-tagged merged trader's plausible assessments against
  `mergedProcess DPH DPA` are its assessments by `H`'s worlds alone
  (`plausibleAssessments_merged_of_tradesIn_H`), so a merged inductor is not exploited, in
  `H`-world terms, by any e.c. trader reading both streams and trading only `H`'s sentences —
  "`H` satisfies the criterion against the joint class relative to `Γ_H`" (the `A` side
  symmetric, `jointClearing_criterion_projection_A`);
* the carrier `JointClearingPair`: one merged inductor over a process containing the merged
  stages, the families in their **own** languages (`X`, `Y`) traded on the merged market as the
  tagged `LUV.tagH (X n)`, `LUV.tagA (Y n)` — the two-sidedness is in the type, not in field
  names — and the self-ledger `pkg.reflected`; and **v3 under joint clearing as a statement**
  (`v3Theorems_of_jointClearing`): Theorem 2 for `h_n := 𝔼^{sideH M}_n(X_n)` and
  `a_n := quote^{sideA M}_n(Y_n)`, the two projections of `M`, with `hbridge` on the merged
  market. Its engine is the same-market theorem on the tagged families — that is what "joint
  clearing is one market" means — so the row is graded `L`;
* the existence row **OPEN** (`jointClearingPair_exists`, with `X` pinned so a degenerate family
  cannot meet it): the merged inductor must live over a process that ledgers the merged market's
  *own* earlier prices (the self-ledger `reflected`), which is `li-coupled-pair`'s well-founded
  day-step recursion (`UniformLIAEvaluator`, OPEN there). FAF's LIA over the *fixed* merged
  process gives an inductor but not the ledger.

Not built, `flagged` in the ledger: `jointClearingPair_exists_of_twoWay`. A `TwoWayPair` is two
separate inductors over two ledgered processes; a merged inductor is non-exploitation by the
*merged* trader class, which two separate inductors do not give; and the conditional from
`UniformLIAEvaluator` needs the self-ledgered merged process constructed in Lean — the construction
`li-coupled-pair` left open. **Disclosed as `variant`**: in the merged model both sides face the
same trader class (all e.c. traders over the merged language), stronger for `H` than the corpus's
`𝒞_H ⊊ 𝒞_A`; the "hard-code poly-time constants" clause of v3's class is FAF's
`EfficientlyComputable` as it stands. K8: the merged market has continuity in *all* merged prices
(stronger than both readings of lean-deference-047).
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology

/-! ## A. The atom renaming and the merged process -/

/-- `H`'s language on the even atoms: the substitution `a ↦ #(2a)`.
Source: [[fa-adaptive-joint-mandate]] § T9 ("a disjoint-union language is an atom renaming")
Kind: D
Fidelity: exact
Hyps: n/a -/
def renameH : LO.Propositional.Substitution ℕ := fun a => LO.Propositional.Formula.atom (2 * a)

/-- `A`'s language on the odd atoms: `a ↦ #(2a + 1)`.
Source: [[fa-adaptive-joint-mandate]] § T9
Kind: D
Fidelity: exact
Hyps: n/a -/
def renameA : LO.Propositional.Substitution ℕ := fun a => LO.Propositional.Formula.atom (2 * a + 1)

/-- An `H`-sentence tagged into the merged language.
Source: [[fa-adaptive-joint-mandate]] § T9
Kind: D
Fidelity: exact
Hyps: n/a -/
def sentH (φ : Sentence) : Sentence := LO.Propositional.Formula.subst renameH φ

/-- An `A`-sentence tagged into the merged language.
Source: [[fa-adaptive-joint-mandate]] § T9
Kind: D
Fidelity: exact
Hyps: n/a -/
def sentA (φ : Sentence) : Sentence := LO.Propositional.Formula.subst renameA φ

/-- The merged stage: both tagged stages.
Source: [[fa-adaptive-joint-mandate]] § T9 (`mergedProcess`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def mergedStage (DH DA : Finset Sentence) : Finset Sentence :=
  DH.image sentH ∪ DA.image sentA

/-- **The merged deductive process** `D n := sentH '' DPH.D n ∪ sentA '' DPA.D n`.
Source: [[fa-positive-results-corrected-v3]] §1 (A1) remark 1; [[fa-adaptive-joint-mandate]] § T9
Kind: D
Fidelity: exact
Hyps: n/a -/
def mergedProcess (DPH DPA : DeductiveProcess) : DeductiveProcess where
  D n := mergedStage (DPH.D n) (DPA.D n)
  mono n := Finset.union_subset_union (Finset.image_subset_image (DPH.mono n))
    (Finset.image_subset_image (DPA.mono n))

/-! ## B. Worlds: projection and gluing (the world side of the projection lemma) -/

/-- The `H`-half of a merged world: the even atoms.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: D
Fidelity: exact
Hyps: n/a -/
def PCWorld.projH (v : PCWorld) : PCWorld := fun a => v (2 * a)

/-- The `A`-half of a merged world: the odd atoms.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: D
Fidelity: exact
Hyps: n/a -/
def PCWorld.projA (v : PCWorld) : PCWorld := fun a => v (2 * a + 1)

/-- Two half-worlds glued into a merged world (the halves share no atoms).
Source: [[fa-adaptive-joint-mandate]] § T9 (a) ("the atom-disjointness lemma is the content")
Kind: D
Fidelity: exact
Hyps: n/a -/
def PCWorld.glue (vH vA : PCWorld) : PCWorld :=
  fun a => if a % 2 = 0 then vH (a / 2) else vA (a / 2)

/-- A merged world holds a tagged `H`-sentence iff its `H`-half holds the sentence (Foundation's
substitution lemma `iff_subst_self`).
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem holds_sentH (v : PCWorld) (φ : Sentence) : v.Holds (sentH φ) ↔ PCWorld.Holds (PCWorld.projH v) φ := by
  unfold PCWorld.Holds sentH
  rw [← LO.Propositional.Formula.Boolean.models_iff_val,
    ← LO.Propositional.Formula.Boolean.models_iff_val,
    ← LO.Propositional.Formula.Boolean.iff_subst_self]
  rfl

/-- A merged world holds a tagged `A`-sentence iff its `A`-half holds the sentence.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem holds_sentA (v : PCWorld) (φ : Sentence) : v.Holds (sentA φ) ↔ PCWorld.Holds (PCWorld.projA v) φ := by
  unfold PCWorld.Holds sentA
  rw [← LO.Propositional.Formula.Boolean.models_iff_val,
    ← LO.Propositional.Formula.Boolean.models_iff_val,
    ← LO.Propositional.Formula.Boolean.iff_subst_self]
  rfl

/-- **Consistency with a merged stage is consistency with each stage separately** (the world side
of the projection lemma (a)).
Source: [[fa-adaptive-joint-mandate]] § T9 (a); [[fa-positive-results-corrected-v3]] §1 (A1) remark 1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem consistentWith_mergedStage_iff (v : PCWorld) (DH DA : Finset Sentence) :
    v.ConsistentWith (mergedStage DH DA) ↔
      PCWorld.ConsistentWith (PCWorld.projH v) DH ∧ PCWorld.ConsistentWith (PCWorld.projA v) DA := by
  simp only [PCWorld.ConsistentWith, mergedStage, Finset.mem_union, Finset.mem_image]
  constructor
  · intro h
    exact ⟨fun φ hφ => (holds_sentH v φ).1 (h _ (Or.inl ⟨φ, hφ, rfl⟩)),
      fun φ hφ => (holds_sentA v φ).1 (h _ (Or.inr ⟨φ, hφ, rfl⟩))⟩
  · rintro ⟨hH, hA⟩ ψ (⟨φ, hφ, rfl⟩ | ⟨φ, hφ, rfl⟩)
    · exact (holds_sentH v φ).2 (hH φ hφ)
    · exact (holds_sentA v φ).2 (hA φ hφ)

/-- Gluing then projecting to the `H`-half is the identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem glue_projH (vH vA : PCWorld) : PCWorld.projH (PCWorld.glue vH vA) = vH := by
  funext a
  have h1 : 2 * a % 2 = 0 := by omega
  have h2 : 2 * a / 2 = a := by omega
  show (if 2 * a % 2 = 0 then vH (2 * a / 2) else vA (2 * a / 2)) = vH a
  rw [if_pos h1, h2]

/-- Gluing then projecting to the `A`-half is the identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem glue_projA (vH vA : PCWorld) : PCWorld.projA (PCWorld.glue vH vA) = vA := by
  funext a
  have h1 : ¬ (2 * a + 1) % 2 = 0 := by omega
  have h2 : (2 * a + 1) / 2 = a := by omega
  show (if (2 * a + 1) % 2 = 0 then vH ((2 * a + 1) / 2) else vA ((2 * a + 1) / 2)) = vA a
  rw [if_neg h1, h2]

/-- **The merged process is satisfiable at every stage iff both base processes are** (the
atom-disjointness lemma: half-worlds glue).
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem mergedProcess_hworld_iff (DPH DPA : DeductiveProcess) :
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((mergedProcess DPH DPA).D n)) ↔
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) ∧
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) := by
  constructor
  · intro h
    refine ⟨fun n => ?_, fun n => ?_⟩
    · obtain ⟨v, hv⟩ := h n
      exact ⟨PCWorld.projH v, ((consistentWith_mergedStage_iff v _ _).1 hv).1⟩
    · obtain ⟨v, hv⟩ := h n
      exact ⟨PCWorld.projA v, ((consistentWith_mergedStage_iff v _ _).1 hv).2⟩
  · rintro ⟨hH, hA⟩ n
    obtain ⟨vH, hvH⟩ := hH n
    obtain ⟨vA, hvA⟩ := hA n
    refine ⟨PCWorld.glue vH vA, (consistentWith_mergedStage_iff _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [glue_projH]; exact hvH
    · rw [glue_projA]; exact hvA

/-! ## C. Strategies over the disjoint-union language, and the per-day joint fixed point -/

/-- A day-`n` strategy **trades only in** the sentences `S`; its coefficients may read any price.
Source: [[fa-adaptive-joint-mandate]] § T9 (a) ("a trader whose trades are all `H`-tagged")
Kind: D
Fidelity: exact
Hyps: n/a -/
def TradesIn {n : ℕ} (T : Strategy n) (S : Set Sentence) : Prop :=
  ∀ p ∈ T.trades, p.2 ∈ S

/-- Two day-`n` strategies played together: the concatenated trade list (FAF's `Strategy` is a
list of `(coefficient, sentence)` pairs, so this is the merged market's one strategy).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def appendStrat {n : ℕ} (T U : Strategy n) : Strategy n where
  trades := T.trades ++ U.trades
  rank_le := by
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact T.rank_le p h
    · exact U.rank_le p h

/-- The value of the concatenation is the sum of the values.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem value_appendStrat {n : ℕ} (T U : Strategy n) (V : History) (w : Sentence → ℝ) :
    (appendStrat T U).value V w = T.value V w + U.value V w := by
  simp [Strategy.value, appendStrat, List.map_append, List.sum_append]

/-- The support of the concatenation is the union of the supports.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem support_appendStrat {n : ℕ} (T U : Strategy n) :
    (appendStrat T U).support = T.support ∪ U.support := by
  simp [Strategy.support, appendStrat, List.toFinset_append, Finset.image_union]

/-- A strategy's value depends on the payout only at its traded sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem value_congr_payout {n : ℕ} (T : Strategy n) (V : History) {w w' : Sentence → ℝ}
    (h : ∀ p ∈ T.trades, w p.2 = w' p.2) : T.value V w = T.value V w' := by
  unfold Strategy.value
  congr 1
  exact List.map_congr_left (fun p hp => by rw [h p hp])

/-- Projecting then gluing is the identity: every merged world *is* a pair of half-worlds.
Source: [[fa-adaptive-joint-mandate]] § T9 (a) (the atom-disjointness lemma)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem glue_proj (v : PCWorld) : PCWorld.glue (PCWorld.projH v) (PCWorld.projA v) = v := by
  funext a
  show (if a % 2 = 0 then v (2 * (a / 2)) else v (2 * (a / 2) + 1)) = v a
  split_ifs with h
  · exact congrArg v (by omega)
  · exact congrArg v (by omega)

/-- A glued world pays an `H`-tagged sentence as its `H`-half pays the sentence.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem payout_glue_sentH (vH vA : PCWorld) (φ : Sentence) :
    (PCWorld.glue vH vA).payout (sentH φ) = vH.payout φ := by
  unfold PCWorld.payout
  by_cases h : vH.Holds φ
  · rw [if_pos h, if_pos ((holds_sentH _ _).2 (by rwa [glue_projH]))]
  · rw [if_neg h, if_neg (fun h' => h (by have := (holds_sentH _ _).1 h'; rwa [glue_projH] at this))]

/-- A glued world pays an `A`-tagged sentence as its `A`-half pays the sentence.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem payout_glue_sentA (vH vA : PCWorld) (φ : Sentence) :
    (PCWorld.glue vH vA).payout (sentA φ) = vA.payout φ := by
  unfold PCWorld.payout
  by_cases h : vA.Holds φ
  · rw [if_pos h, if_pos ((holds_sentA _ _).2 (by rwa [glue_projA]))]
  · rw [if_neg h, if_neg (fun h' => h (by have := (holds_sentA _ _).1 h'; rwa [glue_projA] at this))]

/-- An `H`-tagged strategy's value against a glued world does not depend on the `A`-half.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem value_glue_of_tradesIn_H {n : ℕ} (T : Strategy n) (hT : TradesIn T (Set.range sentH))
    (V : History) (vH vA vA' : PCWorld) :
    T.value V (PCWorld.glue vH vA).payout = T.value V (PCWorld.glue vH vA').payout := by
  apply value_congr_payout
  intro p hp
  obtain ⟨φ, hφ⟩ := hT p hp
  rw [← hφ, payout_glue_sentH, payout_glue_sentH]

/-- An `A`-tagged strategy's value against a glued world does not depend on the `H`-half.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem value_glue_of_tradesIn_A {n : ℕ} (T : Strategy n) (hT : TradesIn T (Set.range sentA))
    (V : History) (vH vH' vA : PCWorld) :
    T.value V (PCWorld.glue vH vA).payout = T.value V (PCWorld.glue vH' vA).payout := by
  apply value_congr_payout
  intro p hp
  obtain ⟨φ, hφ⟩ := hT p hp
  rw [← hφ, payout_glue_sentA, payout_glue_sentA]

/-- An `H`-world read as a merged world. Its `A`-half is immaterial for `H`-tagged trades
(`value_glue_of_tradesIn_H`), so it is taken to be `vH` itself.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: D
Fidelity: exact
Hyps: n/a -/
def PCWorld.liftH (vH : PCWorld) : PCWorld := PCWorld.glue vH vH

/-- An `A`-world read as a merged world (its `H`-half immaterial for `A`-tagged trades).
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: D
Fidelity: exact
Hyps: n/a -/
def PCWorld.liftA (vA : PCWorld) : PCWorld := PCWorld.glue vA vA

/-- `H`'s side of a merged market: its prices of the `H`-tagged sentences.
Source: [[fa-adaptive-joint-mandate]] § T9 ("`H A : History` as the two projections of one merged inductor")
Kind: D
Fidelity: exact
Hyps: n/a -/
def sideH (M : History) : History := fun n φ => M n (sentH φ)

/-- `A`'s side of a merged market: its prices of the `A`-tagged sentences.
Source: [[fa-adaptive-joint-mandate]] § T9
Kind: D
Fidelity: exact
Hyps: n/a -/
def sideA (M : History) : History := fun n φ => M n (sentA φ)

/-- The day-`n` prices of `H`'s side are the `H`-projection of the day-`n` merged valuation.
Source: [[fa-positive-results-corrected-v3]] §1 (A1) remark 1 ("the pair of price vectors")
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem sideH_update (prior : History) (n : ℕ) (V : Valuation) :
    sideH (Function.update prior n V) = Function.update (sideH prior) n (fun φ => V (sentH φ)) := by
  funext m φ
  by_cases h : m = n
  · subst h; simp [sideH]
  · simp [sideH, h]

/-- The day-`n` prices of `A`'s side are the `A`-projection of the day-`n` merged valuation.
Source: [[fa-positive-results-corrected-v3]] §1 (A1) remark 1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem sideA_update (prior : History) (n : ℕ) (V : Valuation) :
    sideA (Function.update prior n V) = Function.update (sideA prior) n (fun φ => V (sentA φ)) := by
  funext m φ
  by_cases h : m = n
  · subst h; simp [sideA]
  · simp [sideA, h]

/-- **The per-day joint fixed point** (v3's (A1) remark 1, "the joint version takes the fixed
point over the pair of price vectors at once"): a day-`n` strategy `TH` trading only `H`-tagged
sentences and a day-`n` strategy `TA` trading only `A`-tagged ones — each reading *both* price
streams — clear together: one `[0,1]` valuation `V` on the merged language, supported on their
traded sentences, under which, against **every pair of half-worlds** `(vH, vA)` — `vH` valuing
`TH`'s trades, `vA` valuing `TA`'s — the two sides' values sum to `≤ 0`. The sides' day-`n` prices
are the projections `V ∘ sentH`, `V ∘ sentA` (`sideH_update`, `sideA_update`). The Brouwer content
is FAF's `fixed_point_lemma` on the concatenated strategy; what this adds is the concatenation
(`value_appendStrat`), that world pairs are merged worlds (`PCWorld.glue`), and that each side's
value depends on its own world only (`value_glue_of_tradesIn_H/A`, where the tagging hypotheses
enter) — which is why no *new* Brouwer argument is needed for the joint fixed point. Repair round
1 replaced the earlier statement (FAF's lemma plus a definitional projection clause, audit r1 B1).
Scope: two-way (the construction of record; partial: over the OPEN pair).
Source: [[fa-positive-results-corrected-v3]] §1 (A1) remark 1; root-fa-022; [[delay-program]] §1 ("needs a new Brouwer argument": FAF's suffices once the merged language is an atom renaming); FAF `lem:fpl`
Kind: C
Fidelity: variant: one merged valuation whose projections are "the pair of price vectors"; both strategies read both streams (the merged trader class, disclosed)
Hyps: (a) none -/
theorem jointClearing_perDay_fixedPoint {n : ℕ} (TH TA : Strategy n)
    (hTH : TradesIn TH (Set.range sentH)) (hTA : TradesIn TA (Set.range sentA)) (prior : History) :
    ∃ V : Valuation, (∀ φ, 0 ≤ V φ ∧ V φ ≤ 1) ∧
      (∀ φ, φ ∉ TH.support ∪ TA.support → V φ = 0) ∧
      ∀ vH vA : PCWorld,
        TH.value (Function.update prior n V) (PCWorld.liftH vH).payout
          + TA.value (Function.update prior n V) (PCWorld.liftA vA).payout ≤ 0 := by
  obtain ⟨V, h1, h2, h3⟩ := fixed_point_lemma (appendStrat TH TA) prior
  refine ⟨V, h1, fun φ hφ => h2 φ (by rwa [support_appendStrat]), fun vH vA => ?_⟩
  have := h3 (PCWorld.glue vH vA)
  rw [value_appendStrat, value_glue_of_tradesIn_H TH hTH _ vH vA vH,
    value_glue_of_tradesIn_A TA hTA _ vH vA vA] at this
  exact this

/-! ## D. The trader side of the projection lemma: the criterion projects to each half -/

/-- A trader trades only in `S` when every day's strategy does.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: D
Fidelity: exact
Hyps: n/a -/
def TraderTradesIn (Tr : Trader) (S : Set Sentence) : Prop :=
  ∀ n, TradesIn (Tr.strat n) S

/-- An `H`-tagged trader's net worth against a glued world does not depend on the `A`-half.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem netWorth_glue_of_tradesIn_H (Tr : Trader) (hTr : TraderTradesIn Tr (Set.range sentH))
    (M : History) (vH vA vA' : PCWorld) (n : ℕ) :
    Tr.netWorth M (PCWorld.glue vH vA) n = Tr.netWorth M (PCWorld.glue vH vA') n := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl (fun i _ => value_glue_of_tradesIn_H _ (hTr i) M vH vA vA')

/-- An `A`-tagged trader's net worth against a glued world does not depend on the `H`-half.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem netWorth_glue_of_tradesIn_A (Tr : Trader) (hTr : TraderTradesIn Tr (Set.range sentA))
    (M : History) (vH vH' vA : PCWorld) (n : ℕ) :
    Tr.netWorth M (PCWorld.glue vH vA) n = Tr.netWorth M (PCWorld.glue vH' vA) n := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl (fun i _ => value_glue_of_tradesIn_A _ (hTr i) M vH vH' vA)

/-- **The plausible assessments of a merged trader by `H`'s worlds**: its net worth on day `n`
(at merged prices) as valued by any world consistent with `DPH.D n`, read as a merged world.
Source: [[fa-adaptive-joint-mandate]] § T9 (a) ("the same plausible assessments … as against `DPH`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def plausibleAssessmentsH (Tr : Trader) (M : History) (DPH : DeductiveProcess) : Set ℝ :=
  { x | ∃ (n : ℕ) (vH : PCWorld), vH.ConsistentWith (DPH.D n) ∧
      x = Tr.netWorth M (PCWorld.liftH vH) n }

/-- **The plausible assessments of a merged trader by `A`'s worlds.**
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: D
Fidelity: exact
Hyps: n/a -/
def plausibleAssessmentsA (Tr : Trader) (M : History) (DPA : DeductiveProcess) : Set ℝ :=
  { x | ∃ (n : ℕ) (vA : PCWorld), vA.ConsistentWith (DPA.D n) ∧
      x = Tr.netWorth M (PCWorld.liftA vA) n }

/-- **The trader side of the projection lemma (a), `H`**: an `H`-tagged merged trader's plausible
assessments against the merged process are exactly its assessments by `H`'s worlds, provided
`A`'s process is satisfiable (so every `H`-world extends to a merged world).
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem plausibleAssessments_merged_of_tradesIn_H (Tr : Trader)
    (hTr : TraderTradesIn Tr (Set.range sentH)) (M : History) (DPH DPA : DeductiveProcess)
    (hA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) :
    Tr.plausibleAssessments M (mergedProcess DPH DPA) = plausibleAssessmentsH Tr M DPH := by
  ext x
  simp only [Trader.plausibleAssessments, plausibleAssessmentsH, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, v, hv, rfl⟩
    have hv' := (consistentWith_mergedStage_iff v _ _).1 hv
    refine ⟨n, PCWorld.projH v, hv'.1, ?_⟩
    unfold PCWorld.liftH
    rw [← netWorth_glue_of_tradesIn_H Tr hTr M _ (PCWorld.projA v) (PCWorld.projH v) n, glue_proj]
  · rintro ⟨n, vH, hvH, rfl⟩
    obtain ⟨vA, hvA⟩ := hA n
    refine ⟨n, PCWorld.glue vH vA, ?_, ?_⟩
    · exact (consistentWith_mergedStage_iff _ _ _).2 ⟨by rwa [glue_projH], by rwa [glue_projA]⟩
    · exact (netWorth_glue_of_tradesIn_H Tr hTr M vH vA vH n).symm

/-- **The trader side of the projection lemma (a), `A`.**
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem plausibleAssessments_merged_of_tradesIn_A (Tr : Trader)
    (hTr : TraderTradesIn Tr (Set.range sentA)) (M : History) (DPH DPA : DeductiveProcess)
    (hH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    Tr.plausibleAssessments M (mergedProcess DPH DPA) = plausibleAssessmentsA Tr M DPA := by
  ext x
  simp only [Trader.plausibleAssessments, plausibleAssessmentsA, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, v, hv, rfl⟩
    have hv' := (consistentWith_mergedStage_iff v _ _).1 hv
    refine ⟨n, PCWorld.projA v, hv'.2, ?_⟩
    unfold PCWorld.liftA
    rw [← netWorth_glue_of_tradesIn_A Tr hTr M (PCWorld.projH v) (PCWorld.projA v) _ n, glue_proj]
  · rintro ⟨n, vA, hvA, rfl⟩
    obtain ⟨vH, hvH⟩ := hH n
    refine ⟨n, PCWorld.glue vH vA, ?_, ?_⟩
    · exact (consistentWith_mergedStage_iff _ _ _).2 ⟨by rwa [glue_projH], by rwa [glue_projA]⟩
    · exact (netWorth_glue_of_tradesIn_A Tr hTr M vH vA vA n).symm

/-- **`H` satisfies the criterion against the joint class relative to `Γ_H`** (the mandate's
`jointClearing_criterion_projection`): if `M` is a logical inductor over the merged process, then
no e.c. trader that reads both price streams and trades only `H`-tagged sentences has `H`-world
assessments that are bounded below and unbounded above — FAF's non-exploitation, projected to
`H`'s worlds through `plausibleAssessments_merged_of_tradesIn_H`. The corpus's "joint class" is
the merged class, disclosed `variant` (stronger for `H` than `𝒞_H ⊊ 𝒞_A`).
Scope: two-way (the construction of record; partial: over the OPEN pair — a merged inductor with
the self-ledger is `jointClearingPair_exists`; a merged inductor over the *fixed* merged process
is FAF's LIA, not imported here).
Source: [[fa-adaptive-joint-mandate]] § T9 (a); root-fa-016; vq-wiki-035 (a)
Kind: C
Fidelity: variant: the joint class is the merged class; the merged inductor is a hypothesis (instance), not constructed here
Hyps: (a) none beyond the instance -/
theorem jointClearing_criterion_projection {M : History} {DPH DPA : DeductiveProcess}
    [hLI : IsLogicalInductor M (mergedProcess DPH DPA)]
    (hA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (Tr : Trader) (hec : EfficientlyComputable Tr) (hTr : TraderTradesIn Tr (Set.range sentH)) :
    ¬ (BddBelow (plausibleAssessmentsH Tr M DPH) ∧ ¬ BddAbove (plausibleAssessmentsH Tr M DPH)) := by
  have h := hLI.noExploit Tr hec
  unfold Trader.Exploits at h
  rwa [plausibleAssessments_merged_of_tradesIn_H Tr hTr M DPH DPA hA] at h

/-- **`A` satisfies the criterion against the joint class relative to `Γ_A`** (symmetric).
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: C
Fidelity: variant: as `jointClearing_criterion_projection`
Hyps: (a) none beyond the instance -/
theorem jointClearing_criterion_projection_A {M : History} {DPH DPA : DeductiveProcess}
    [hLI : IsLogicalInductor M (mergedProcess DPH DPA)]
    (hH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (Tr : Trader) (hec : EfficientlyComputable Tr) (hTr : TraderTradesIn Tr (Set.range sentA)) :
    ¬ (BddBelow (plausibleAssessmentsA Tr M DPA) ∧ ¬ BddAbove (plausibleAssessmentsA Tr M DPA)) := by
  have h := hLI.noExploit Tr hec
  unfold Trader.Exploits at h
  rwa [plausibleAssessments_merged_of_tradesIn_A Tr hTr M DPH DPA hH] at h

/-! ## E. Tagged LUVs, the carrier, and v3 under joint clearing -/

/-- A LUV of `H`'s language tagged into the merged language: its threshold sentences renamed.
Source: [[fa-adaptive-joint-mandate]] § T9; audit r1 B2 (the families must be tied to their halves)
Kind: D
Fidelity: exact
Hyps: n/a -/
def LUV.tagH (X : LUV) : LUV := ⟨fun r => sentH (X.gt r)⟩

/-- A LUV of `A`'s language tagged into the merged language.
Source: [[fa-adaptive-joint-mandate]] § T9; audit r1 B2
Kind: D
Fidelity: exact
Hyps: n/a -/
def LUV.tagA (Y : LUV) : LUV := ⟨fun r => sentA (Y.gt r)⟩

/-- The merged market's expectation of an `H`-tagged LUV is `H`'s side's expectation of the LUV.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem expect_tagH (X : LUV) (M : History) (n : ℕ) :
    (LUV.tagH X).expect M n = X.expect (sideH M) n := rfl

/-- The merged market's expectation of an `A`-tagged LUV is `A`'s side's expectation of the LUV.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem expect_tagA (Y : LUV) (M : History) (n : ℕ) :
    (LUV.tagA Y).expect M n = Y.expect (sideA M) n := rfl

/-- The merged market's quote of an `A`-tagged family is `A`'s side's quote of the family.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem quoteSeq_tagA (Y : ℕ → LUV) (M : History) :
    quoteSeq (fun n => LUV.tagA (Y n)) M = quoteSeq Y (sideA M) := rfl

/-- A merged world values an `H`-tagged LUV at `x` iff its `H`-half values the LUV at `x`.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem valuesAt_tagH (v : PCWorld) (X : LUV) (x : ℝ) :
    v.ValuesAt (LUV.tagH X) x ↔ PCWorld.ValuesAt (PCWorld.projH v) X x := by
  simp only [PCWorld.ValuesAt, LUV.tagH, holds_sentH]

/-- **A joint-clearing pair**: one merged inductor `M` over a process `DPM` containing the merged
stages of two base processes (disjoint atoms, `merged_sub`: so every `DPM`-world projects to a
`DPH`-world and a `DPA`-world, `consistent_projH`), `H`'s family `X` and `A`'s quote family `Y`
**in their own languages**, traded on the merged market as the tagged `LUV.tagH (X n)` and
`LUV.tagA (Y n)` — the tagging is in the type, so the two sides are `sideH M` and `sideA M`
(`JointClearingPair.H`, `.A`) and not one market wearing two names — with the **self-ledger**
`pkg.reflected` (the merged process determines `A`'s tagged quote at the merged market's own
realized day-`f n` expectation of `H`'s tagged family, `= 𝔼^{sideH M}_{f n}(X_n)` by
`expect_tagH` — `A` proving `H`'s outputs, v3's (A3)). Both sides face the same trader class
(disclosed `variant`). Existence is `jointClearingPair_exists` (OPEN). Repair round 1 replaced
untagged families `XM`, `YM` (audit r1 B2).
Source: [[fa-positive-results-corrected-v3]] §1 (A1), (A3); vq-wiki-034/035; [[fa-adaptive-joint-mandate]] § T9
Kind: D
Fidelity: variant: both sides the same trader class (stronger for `H` than `𝒞_H ⊊ 𝒞_A`); families tagged into their halves by construction
Hyps: n/a -/
structure JointClearingPair (DPH DPA : DeductiveProcess) (f : DeferralFunction) where
  /-- The merged market. -/
  M : History
  /-- The merged process with the self-ledger. -/
  DPM : DeductiveProcess
  /-- It contains the merged stages of the two base processes. -/
  merged_sub : ∀ n, (mergedProcess DPH DPA).D n ⊆ DPM.D n
  /-- The merged market is an inductor over it. -/
  inductor : IsLogicalInductor M DPM
  /-- Every stage is satisfiable. -/
  hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPM.D n)
  /-- `H`'s family, in `H`'s own language; traded on the merged market as `LUV.tagH (X n)`. -/
  X : ℕ → LUV
  /-- `A`'s quote family, in `A`'s own language; traded as `LUV.tagA (Y n)`. -/
  Y : ℕ → LUV
  /-- The tagged `H`-family is e.c. -/
  hcode : LUV.MachineThresholdCodeSeq (fun n => LUV.tagH (X n))
  /-- The quote package on the merged market: e.c. tagged quotes, and the self-ledger `reflected`. -/
  pkg : CrossQuotePackage M DPM f (fun n => LUV.tagH (X n)) (fun n => LUV.tagA (Y n))
  /-- Every completed-theory world values the tagged `H`-family. -/
  hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPM → ∃ x : ℝ, v.ValuesAt (LUV.tagH (X n)) x

/-- `H`'s market: the `H`-projection of the merged market.
Source: [[fa-adaptive-joint-mandate]] § T9 ("`H A : History` as the two projections")
Kind: D
Fidelity: exact
Hyps: n/a -/
def JointClearingPair.H {DPH DPA : DeductiveProcess} {f : DeferralFunction}
    (P : JointClearingPair DPH DPA f) : History := sideH P.M

/-- `A`'s market: the `A`-projection of the merged market.
Source: [[fa-adaptive-joint-mandate]] § T9
Kind: D
Fidelity: exact
Hyps: n/a -/
def JointClearingPair.A {DPH DPA : DeductiveProcess} {f : DeferralFunction}
    (P : JointClearingPair DPH DPA f) : History := sideA P.M

/-- A world of the pair's process projects to a world of `H`'s base process (`merged_sub`).
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem JointClearingPair.consistent_projH {DPH DPA : DeductiveProcess} {f : DeferralFunction}
    (P : JointClearingPair DPH DPA f) {n : ℕ} {v : PCWorld} (hv : v.ConsistentWith (P.DPM.D n)) :
    PCWorld.ConsistentWith (PCWorld.projH v) (DPH.D n) :=
  ((consistentWith_mergedStage_iff v _ _).1 (fun φ hφ => hv φ (P.merged_sub n hφ))).1

/-- A world of the pair's process projects to a world of `A`'s base process.
Source: [[fa-adaptive-joint-mandate]] § T9 (a)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem JointClearingPair.consistent_projA {DPH DPA : DeductiveProcess} {f : DeferralFunction}
    (P : JointClearingPair DPH DPA f) {n : ℕ} {v : PCWorld} (hv : v.ConsistentWith (P.DPM.D n)) :
    PCWorld.ConsistentWith (PCWorld.projA v) (DPA.D n) :=
  ((consistentWith_mergedStage_iff v _ _).1 (fun φ hφ => hv φ (P.merged_sub n hφ))).2

/-- **v3 under joint clearing, as a statement** (vq-wiki-034): for a joint-clearing pair, v3's
Theorem 2 holds for `h_n := 𝔼^{H}_n(X_n)` on `H`'s market `P.H = sideH M` and
`a_n := quote^{A}_n(Y_n)` on `A`'s market `P.A = sideA M` — the two projections of the merged
market — with the bridge as a hypothesis on the merged market. The engine is the same-market
theorem `v3Theorem2_self_of_bridge` on the **tagged** families: on the merged market both are
same-market quotes, so `hjoint` is discharged by `legibleOn_viol_self`, and the sides' readings
are the definitional projections `expect_tagH`, `quoteSeq_tagA`. That is what "joint clearing is
one market" means, and why the row is graded `L`: its content is the carrier — two base processes
with disjoint atoms, the families tagged into their halves, the self-ledger — not the proof.
Repair round 1: the earlier statement read one market's own expectation and quote of two untagged
families (audit r1 B2).
Scope: two-way (partial: over the OPEN pair — existence is `jointClearingPair_exists`).
Source: vq-wiki-034; [[fa-adaptive-joint-mandate]] § T9 ("v3 under joint clearing as a statement")
Kind: L
Fidelity: variant: the sides are the projections of one merged inductor; the bridge is asked on the merged market (the merged class)
Hyps: (c) `P` (the pair: `pkg.reflected`, the self-ledger); `hbridge` (T4 on the merged market, OPEN). -/
theorem v3Theorems_of_jointClearing {DPH DPA : DeductiveProcess} {f : DeferralFunction}
    (P : JointClearingPair DPH DPA f) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hbridge : AdaptiveBridgeHolds P.M f (fun n => LUV.tagH (P.X n))) :
    Tendsto (viol (fun n => (P.X n).expect P.H n) (quoteSeq P.Y P.A) t ε δ) atTop (𝓝 0) :=
  haveI := P.inductor
  v3Theorem2_self_of_bridge P.pkg P.hcode P.hworld P.hval t ε hδ hε hbridge

/-- **OPEN (T9, the existence row): a joint-clearing pair exists over any two satisfiable base
processes, for every admissible `H`-family `X`** (pinned, so a degenerate constant family cannot
meet the row). FAF's LIA gives an inductor over the *fixed* merged process (`mergedProcess_hworld_iff`
supplies its satisfiability), but the self-ledger `pkg.reflected` asks the merged process to
determine, at stage `s`, the merged market's *own* earlier output — `li-coupled-pair`'s
well-founded day-step recursion (`UniformLIAEvaluator`, OPEN there; `twoWayPair_exists`). So this
row reduces to that one; the Brouwer half is not where the difficulty is
(`jointClearing_perDay_fixedPoint`). Listed in `fa-adaptive-joint-open.txt`.
Scope: two-way (partial: over the OPEN pair).
Source: [[fa-positive-results-corrected-v3]] §1 (A1) remark 1 ("an assumption, not a citation"); root-fa-022; [[delay-program]] §1; [[fa-adaptive-joint-mandate]] § T9 (b)
Kind: OPEN
Fidelity: exact
Hyps: (a) `hH`, `hA`, `hcode`, `hval`. -/
theorem jointClearingPair_exists (DPH DPA : DeductiveProcess)
    (hH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (f : DeferralFunction)
    (X : ℕ → LUV) (hcode : LUV.MachineThresholdCodeSeq (fun n => LUV.tagH (X n)))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory (mergedProcess DPH DPA) →
      ∃ x : ℝ, v.ValuesAt (LUV.tagH (X n)) x) :
    ∃ P : JointClearingPair DPH DPA f, P.X = X := by
  sorry

end Cleanroom.Fa.FaAdaptiveJoint
