import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Marginal
import Cleanroom.Li.LiProjection.Fragments
import Cleanroom.Li.LiProjection.Underdetermination
import Cleanroom.Found.LiQuoteLane.Conditioning
import LogicalInduction.Properties.Conditioning
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `li-projection` · Recover: No-Forced-Trust — the record does not determine the limit (T6)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 12 of the layout.

* **T6.1 U1/U2 over FAF.** Take the *record* of a base inductor `H` to be its conditioned histories
  `conditionedHistory H ψ` on a `u`-free conditioning family `ψ`, restricted to `u`-free sentences
  (`li-quote-lane`'s `ledgerSeq a e` is such a family: family-`3` literals or `⊤`). With
  `H' := project H u (fun _ => c)`: **(U1)** the records are identical
  (`conditionedHistory_project_eq`: every `φ ⋏ ψ n` and `ψ n` is `u`-free, so `project_restrict`),
  while **(U2)** the limiting beliefs on the evaluative atom differ for a suitable rational `c`
  (`exists_const_limit_ne`: two of the three rationals `1/4, 1/2, 3/4` work, since `H_∞(u)` may be
  irrational). The **headline is `u1_u2_inductor`**: `H'` is an *inductor* with the same record and
  a different limit, so the map inductor ↦ record is not injective — the inductor conjunct is
  Lemma A and rests on the OPEN certificate. Without that conjunct the statement is a triviality
  about histories (`project_record_eq_limit_ne` for the projection; `exists_history_same_record_ne_limit`
  for *any* history, by overwriting the atom's own price — audit r1, fidelity B1), which is why U1
  is kind L. **Fidelity `weaker`** (repair round 2, audit r2 fidelity B1): the record here is the
  conditioned histories on `u`-free sentences *only*, and the sentence whose limit differs (`u`) is
  outside it by construction — the probe `audit-r2-probes/RecordAtAtom.lean` kernel-checks that the
  two records differ *at* `u`. The source's record is `H_t(· | Q_A)` on the whole language, the
  evaluative sentence included, and its target — same conditioned record at `φ` too, different
  limit at `φ`, by a modification "only on `¬Q_A`-worlds" — is **not proved**; it is stated OPEN as
  `conditioned_record_not_injective` (`Open.lean`) and discussed in [[li-projection-findings]] F14.
  The mandate's clause "the same conclusion by a cleaner route" is overruled by [[STANDARDS]] §3 and
  withdrawn. U3 (prediction vs influence non-identifiability) is not attempted.
* **T6.2, the LI side over `paperDP T`, complete.** For every inductor over `paperDP T`,
  `limitingBelief P (paperPrimeDecompose σ) = 1 ↔ T ⊢ σ` (`limitingBelief_paperPrime_eq_one_iff`):
  provable ⇒ `1` through FAF's coverage of theorems by the paper process and T4.1's biconditional
  (`limitingBelief_paperPrime_of_provable`); unprovable ⇒ `< 1` through a model of `T + ∼σ`
  (consistency, completeness) carried to a world of `paperDP T` by FAF's `paperDP_hworld_of_model`
  and falsifying the decomposition, then non-dogmatism (`limitingBelief_paperPrime_lt_one_of_unprovable`).
  The recursion-theoretic half (Church) and the theorem `limit_non_recoverable` itself are in
  `Church.lean` (repair rounds 1–2).
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Filter Topology
open LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-! ## T6.1 U1: the conditioned record is identical -/

/-- The `u`-free conditioned record reads only `u`-free prices: any two histories agreeing on every
`u`-free sentence have the same conditioned histories on a `u`-free conditioning family, at every
`u`-free sentence. No criterion anywhere — this is what makes U1 definitional (audit r1, fidelity
B1, probe `RecordTrivial.lean`).
Source: audit r1 (fidelity) B1; mandate T6.1
Kind: L
Fidelity: n/a -/
theorem conditionedHistory_eq_of_agree_atomFree (H H' : History) (u : ℕ)
    (hagree : ∀ n φ, AtomFreeSentence u φ → H' n φ = H n φ) (ψ : ℕ → Sentence)
    (hψ : ∀ n, AtomFreeSentence u (ψ n)) (n : ℕ) {φ : Sentence} (hφ : AtomFreeSentence u φ) :
    conditionedHistory H' ψ n φ = conditionedHistory H ψ n φ := by
  simp only [conditionedHistory, conditionalQuote]
  rw [hagree n _ (hφ.and (hψ n)), hagree n _ (hψ n)]

/-- **U1 for the projection.** The conditioned histories of `H` and of its projection on a `u`-free
conditioning family agree at every `u`-free sentence, on every day: the observable record is
identical. Definitional: `φ ⋏ ψ n` and `ψ n` are `u`-free, so the projection *is* `H` there
(`project_restrict`); the criterion plays no part (`conditionedHistory_eq_of_agree_atomFree`).
Source: [[anson-2-inventory]] 018 (U1, chat 05 L10646–10652); [[root-deference-inventory]] 024 (R1); mandate T6.1
Kind: L
Fidelity: weaker: the record is restricted to `u`-free sentences — the source's record is the conditioned market on the whole language, and at `u` itself the two records differ (audit r2 probe `RecordAtAtom.lean`); the modification is on `u`-sentences, not "only on `¬Q_A`-worlds"
Hyps: (a) -/
theorem conditionedHistory_project_eq (H : History) (u : ℕ) (q : ℕ → ℚ) (ψ : ℕ → Sentence)
    (hψ : ∀ n, AtomFreeSentence u (ψ n)) (n : ℕ) {φ : Sentence} (hφ : AtomFreeSentence u φ) :
    conditionedHistory (project H u q) ψ n φ = conditionedHistory H ψ n φ :=
  conditionedHistory_eq_of_agree_atomFree H _ u (fun n _ hφ => project_restrict H u q n hφ) ψ hψ n hφ

/-- A decided literal of a family other than `4` is free of every projection atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atomFreeSentence_literalOf_of_ne (k : ℕ) (x : ℕ × ℕ × Bool) (hx : x.1 ≠ 4) :
    AtomFreeSentence (projAtomCode k) (literalOf x) := by
  rcases x with ⟨f, p, b⟩
  cases b
  · exact (atomFreeSentence_freshAtom_of_ne hx k).neg
  · exact atomFreeSentence_freshAtom_of_ne hx k

/-- `li-quote-lane`'s ledger conditioning sequence is free of every projection atom (each member is a
family-`3` literal or `⊤`).
Source: mandate T6.1 ("`ledgerSeq a e`, which is family-3, hence `u`-free")
Kind: L
Fidelity: exact -/
theorem atomFreeSentence_ledgerSeq (k : ℕ) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (t : ℕ) :
    AtomFreeSentence (projAtomCode k) (ledgerSeq a e t) := by
  unfold ledgerSeq
  split_ifs
  · exact atomFreeSentence_literalOf_of_ne k _ (by simp [ledgerEntry, ledgerFamily])
  · exact atomFreeSentence_top _

/-! ## T6.1 U2: the limits differ -/

/-- For any real `L` there is a rational `c ∈ (0,1)` with `c ≠ L` (`1/2` unless `L = 1/2`, else `1/4`).
Source: mandate T6.1 ("two of three rationals in `(0,1)` work; pick by cases")
Kind: L
Fidelity: n/a -/
lemma exists_rat_Ioo_ne (L : ℝ) : ∃ c : ℚ, 0 < c ∧ c < 1 ∧ (c : ℝ) ≠ L := by
  by_cases h : L = 1 / 2
  · exact ⟨1 / 4, by norm_num, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨1 / 2, by norm_num, by norm_num, by push_cast; exact Ne.symm h⟩

/-- **U2.** For any base inductor `H` over `DP` with `u` fresh there is a rational `c ∈ (0,1)` such
that the projection's limiting belief on `u` differs from `H`'s.
Source: [[anson-2-inventory]] 018 (U2); [[trust-lab-inventory]] 067; mandate T6.1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_const_limit_ne (H : History) (DP : DeductiveProcess) [IsLogicalInductor H DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧
      limitingBelief (project H u (fun _ => c)) (Formula.atom u) ≠
        limitingBelief H (Formula.atom u) := by
  obtain ⟨c, hc0, hc1, hne⟩ := exists_rat_Ioo_ne (limitingBelief H (Formula.atom u))
  exact ⟨c, hc0, hc1, by rw [limitingBelief_project_const_atom H DP hworld u c]; exact hne⟩

/-- **U1 + U2 for the projection, without the criterion** (before repair round 1 this carried the
name `record_identical_limit_differs` and was rowed as the T6.1 headline — audit r1, fidelity B1).
For a base inductor `H` over `DP` and a `u`-free conditioning family `ψ`: there is a rational
`c ∈ (0,1)` such that the projection `H' := project H u (fun _ => c)` has the *same* conditioned
record as `H` on every `u`-free sentence (U1) and a *different* limiting belief on `u` (U2). This
says nothing about inductors: U1 holds for every history agreeing with `H` off `u`
(`conditionedHistory_eq_of_agree_atomFree`), and a history with the same record and a different
limit exists for *any* `H` (`exists_history_same_record_ne_limit`). The content of T6.1 — that `H'`
is an *inductor* — is `u1_u2_inductor`, the headline.
Source: [[anson-2-inventory]] 018 (U1/U2, the two halves); mandate T6.1
Kind: L
Fidelity: weaker: no criterion on `H'`; the record identity is definitional and `u`-free only (see `u1_u2_inductor`). Scope: one-way
Hyps: (a) -/
theorem project_record_eq_limit_ne (H : History) (DP : DeductiveProcess)
    [IsLogicalInductor H DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ)
    (ψ : ℕ → Sentence) (hψ : ∀ n, AtomFreeSentence u (ψ n)) :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧
      (∀ n φ, AtomFreeSentence u φ →
        conditionedHistory (project H u (fun _ => c)) ψ n φ = conditionedHistory H ψ n φ) ∧
      limitingBelief (project H u (fun _ => c)) (Formula.atom u) ≠
        limitingBelief H (Formula.atom u) := by
  obtain ⟨c, hc0, hc1, hne⟩ := exists_const_limit_ne H DP hworld u
  exact ⟨c, hc0, hc1, fun n φ hφ => conditionedHistory_project_eq H u _ ψ hψ n hφ, hne⟩

/-- **U1 + U2 without any inductor** — the triviality the T6.1 headline must not be confused with
(audit r1, fidelity B1, probe `RecordTrivial.lean`, ported): for *every* history `H` and `u`-free
conditioning family `ψ` there is a history with the same `u`-free conditioned record and a different
limiting belief on `u` — overwrite the atom's own price by a constant. No criterion involved; so the
map history ↦ record is never injective, and the content of T6.1 is entirely that the second
history can be chosen to be an *inductor* (`u1_u2_inductor`).
Source: audit r1 (fidelity) B1
Kind: L
Fidelity: n/a (the degenerate reading, recorded so it cannot be mistaken for the headline) -/
theorem exists_history_same_record_ne_limit (H : History) (u : ℕ) (ψ : ℕ → Sentence)
    (hψ : ∀ n, AtomFreeSentence u (ψ n)) :
    ∃ H' : History,
      (∀ n φ, AtomFreeSentence u φ → conditionedHistory H' ψ n φ = conditionedHistory H ψ n φ) ∧
      limitingBelief H' (Formula.atom u) ≠ limitingBelief H (Formula.atom u) := by
  obtain ⟨c, -, -, hne⟩ := exists_rat_Ioo_ne (limitingBelief H (Formula.atom u))
  have hagree : ∀ n φ, AtomFreeSentence u φ →
      (fun (m : ℕ) (χ : Sentence) => if χ = Formula.atom u then (c : ℝ) else H m χ) n φ = H n φ := by
    intro n φ hφ
    have hne' : φ ≠ Formula.atom u := by
      intro h
      subst h
      exact hφ (by rw [sentenceAtomCodes_atom]; exact Finset.mem_singleton_self u)
    simp [hne']
  refine ⟨fun m χ => if χ = Formula.atom u then (c : ℝ) else H m χ, ?_, ?_⟩
  · intro n φ hφ
    exact conditionedHistory_eq_of_agree_atomFree H _ u hagree ψ hψ n hφ
  · have hconst : limitingBelief (fun m χ => if χ = Formula.atom u then (c : ℝ) else H m χ)
        (Formula.atom u) = c := by
      simp only [limitingBelief, if_true]
      exact Filter.limsup_const _
    rw [hconst]
    exact hne

/-- **T6.1, U1 + U2 over FAF: the record does not determine the limit, among inductors.** For a
base inductor `H` over `DP`, `u` fresh for `DP`, and a `u`-free conditioning family `ψ`: there is a
rational `c ∈ (0,1)` such that `H' := project H u (fun _ => c)` is itself a logical inductor over
`DP`, has the *same* conditioned record as `H` on every `u`-free sentence (U1), and a *different*
limiting belief on `u` (U2). So the map **inductor** ↦ `u`-free record is not injective, and `H_∞`
on the evaluative atom is not a function of the `u`-free record. The inductor conjunct is Lemma A
and rests on the OPEN certificate; U1 is definitional and U2 is the limit computation
(`project_record_eq_limit_ne`). **What this does not say** (audit r2 fidelity B1): the record
excludes the very sentence `u` whose limit differs — at `u` the two conditioned records *differ*
(probe `audit-r2-probes/RecordAtAtom.lean`), and a record blind to `u` determines `u`'s limit for
no history at all (`exists_history_same_record_ne_limit`). The source's target — same conditioned
record at the evaluative sentence too, different limit there — is the OPEN
`conditioned_record_not_injective` (`Open.lean`; findings F14).
Source: [[anson-2-inventory]] 018 (U1/U2, "two base LIs … identical conditionals … different limit"); [[root-deference-inventory]] 024 (R1, No-Forced-Trust); [[trust-lab-inventory]] 067; [[deference-in-logical-induction-v6]] §4.1
Kind: C
Fidelity: weaker: the record is the conditioned histories on `u`-free sentences only, so the sentence whose limit differs is outside the record; the source's record is `H_t(· | Q_A)` on the whole language, `φ` included, and its target (same record at `φ`, different limit at `φ`) is not proved (OPEN `conditioned_record_not_injective`); the modification is on `u`-sentences, not "only on `¬Q_A`-worlds"; U3 not attempted. Scope: one-way
Hyps: (a) throughout; the inductor conjunct rests on the OPEN rewriters -/
theorem u1_u2_inductor (H : History) (DP : DeductiveProcess) [IsLogicalInductor H DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP)
    (ψ : ℕ → Sentence) (hψ : ∀ n, AtomFreeSentence u (ψ n)) :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧ IsLogicalInductor (project H u (fun _ => c)) DP ∧
      (∀ n φ, AtomFreeSentence u φ →
        conditionedHistory (project H u (fun _ => c)) ψ n φ = conditionedHistory H ψ n φ) ∧
      limitingBelief (project H u (fun _ => c)) (Formula.atom u) ≠
        limitingBelief H (Formula.atom u) := by
  obtain ⟨c, hc0, hc1, hrec, hne⟩ := project_record_eq_limit_ne H DP hworld u ψ hψ
  exact ⟨c, hc0, hc1, project_const_isLogicalInductor H DP u hu c hc0 hc1, hrec, hne⟩

/-! ## T6.2, the LI side: provable sentences have limit `1` over the paper process -/

/-- **Provable ⇒ limit `1`.** Over `paperDP T`, every inductor's limiting belief on the prime
decomposition of a `T`-theorem is `1`: FAF's paper process eventually contains the decomposition
(`paperTheoryDP_covers_outer_provable`, `paperDP_covers_of_paperTheoryDP`), so every completed-theory
world holds it, and T4.1's biconditional applies.
Source: mandate T6.2 ("`limit = 1 ↔ T ⊢ σ`, through `lic_provind` + `paperDP_covers…` one way"); [[anson-inventory]] 029
Kind: C
Fidelity: exact (one direction; the converse is `limitingBelief_paperPrime_lt_one_of_unprovable` below)
Hyps: (a) -/
theorem limitingBelief_paperPrime_of_provable (T : ArithmeticTheory) [T.Δ₁]
    [𝗣𝗔⁻ ⪯ T] [Consistent T]
    (P : History) [IsLogicalInductor P (paperDP T)] (σ : ArithmeticSentence)
    (hσ : T ⊢ σ) : limitingBelief P (paperPrimeDecompose σ) = 1 := by
  rw [limitingBelief_eq_one_iff P (paperDP T) (paperDP_hworld T)]
  intro v hv
  exact hv.holds_of_mem_stage
    (paperDP_covers_of_paperTheoryDP T (paperTheoryDP_covers_outer_provable T σ hσ))

/-- `T + ∼σ` is consistent when `T ⊬ σ` (Foundation's `consistent_cons_of_unprovable`, restated here
because its module `Incompleteness/Dense` is outside FAF's import closure).
Source: none: infrastructure (Foundation `Entailment.consistent_cons_of_unprovable`)
Kind: L
Fidelity: n/a -/
lemma consistent_adjoin_neg_of_unprovable (T : ArithmeticTheory) (σ : ArithmeticSentence)
    (h : T ⊬ σ) : Consistent (adjoin (∼σ) T) := by
  apply LO.Entailment.consistent_iff_exists_unprovable.mpr
  refine ⟨⊥, ?_⟩
  apply LO.Entailment.deduction_iff.not.mpr
  contrapose! h
  cl_prover [h]

/-- **Unprovable ⇒ limit `< 1`.** Over `paperDP T`, if `T ⊬ σ` then every inductor's limiting belief
on `paperPrimeDecompose σ` is below `1`: `T + ∼σ` is consistent (`consistent_cons_of_unprovable`),
hence has a model (completeness), whose extension world is consistent with every stage of
`paperDP T` (FAF's `paperDP_hworld_of_model`) and falsifies the decomposition
(`paperPrimeWorld_holds_decompose`, `eval_emb`); non-dogmatism (`lic_exists_limit_lt_one`) does the rest.
Source: mandate T6.2 ("`lic_exists_limit_lt_one` + `consistent_cons_of_unprovable` … the other way"); [[anson-inventory]] 029
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_paperPrime_lt_one_of_unprovable (T : ArithmeticTheory) [T.Δ₁]
    [𝗣𝗔⁻ ⪯ T] [Consistent T]
    (P : History) [IsLogicalInductor P (paperDP T)] (σ : ArithmeticSentence)
    (hσ : T ⊬ σ) : limitingBelief P (paperPrimeDecompose σ) < 1 := by
  have hcons : Consistent (adjoin (∼σ) T) := consistent_adjoin_neg_of_unprovable T σ hσ
  have hs : Satisfiable (adjoin (∼σ) T) :=
    LO.FirstOrder.Theory.small_satisfiable_of_consistent (T := adjoin (∼σ) T) hcons
  rcases satisfiable_iff.mp hs with ⟨M, hMne, hMstr, hT'⟩
  letI : Nonempty M := hMne
  letI : Structure ℒₒᵣ M := hMstr
  let f : ℕ → M := fun _ => Classical.choice hMne
  have hT : M ↓[ℒₒᵣ] ⊧* T := LO.Semantics.modelsSet_iff.mpr fun ψ hψ =>
    LO.Semantics.modelsSet_iff.mp hT' (AdjunctiveSet.mem_cons_iff.mpr (Or.inr hψ))
  have hneg : M ↓[ℒₒᵣ] ⊧ ∼σ :=
    LO.Semantics.modelsSet_iff.mp hT' (AdjunctiveSet.mem_cons_iff.mpr (Or.inl rfl))
  have hw : (paperTheoryExtensionWorld T M f).ConsistentWithTheory (paperDP T) :=
    paperDP_hworld_of_model T hT f
  have hwσ : ¬ (paperTheoryExtensionWorld T M f).Holds (paperPrimeDecompose σ) := by
    rw [paperTheoryExtensionWorld_holds_paper_iff, paperPrimeWorld_holds_decompose]
    have hR : ¬ σ.Realize M := by simpa [models_iff] using hneg
    simpa [Semiformula.Evalf, Semiformula.Realize] using hR
  obtain ⟨L, hL, hL1⟩ := lic_exists_limit_lt_one P (paperDP T) (paperPrimeDecompose σ)
    (fun n => ⟨_, hw n, hwσ⟩)
  have hlim : limitingBelief P (paperPrimeDecompose σ) = L := hL.limsup_eq
  rw [hlim]
  exact hL1

/-- **The limit biconditional over the paper process**: `limitingBelief P (paperPrimeDecompose σ) = 1 ↔ T ⊢ σ`,
for every inductor over `paperDP T`. The LI side of T6.2 and of the extension, complete.
Source: mandate T6.2; [[anson-2-inventory]] 004(i); [[anson-inventory]] 029
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_paperPrime_eq_one_iff (T : ArithmeticTheory) [T.Δ₁]
    [𝗣𝗔⁻ ⪯ T] [Consistent T]
    (P : History) [IsLogicalInductor P (paperDP T)] (σ : ArithmeticSentence) :
    limitingBelief P (paperPrimeDecompose σ) = 1 ↔ T ⊢ σ := by
  constructor
  · intro h1
    by_contra hσ
    have := limitingBelief_paperPrime_lt_one_of_unprovable T P σ hσ
    linarith
  · exact limitingBelief_paperPrime_of_provable T P σ

end Cleanroom.Li.LiProjection
