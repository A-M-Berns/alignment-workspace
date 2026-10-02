import Cleanroom.Corrigibility.CorrLegitGeneral.TwoCell

/-!
# corr-legit-general — T4(d): fn 65's open direction, settled

DDB's one stated open problem (fn 65): local Total Trust with respect to `Q` ⟹ local Value with
respect to `Q`. The package settles it negatively in every reading it considered:

1. **In fn 64's literal reading it is false, already for two cells** (`tie4`,
   `WitnessesFn66.lean`): `localTotalTrust_imp_localValue_refuted` below packages the
   counterexample to the mandate's open statement `∀ Q π F, π ∈ stdSimplex → TotalTrustWrt Q π F →
   ValuesWrt Q π F`.
2. **The weak reading** (`WeakValuesWrt`: some recommended strategy beats every fixed option) is
   a theorem for two cells (`weakValuesWrt_questionOf_of_simpleTrustOn`) and for the finest
   question (`totalTrust_imp_weakValuesWrt_id` below), and **false at three cells**: a
   seven-world frame on a three-cell question has local Total Trust and no weak local Value on a
   three-option menu whose recommended strategy is forced
   (`localTotalTrust_imp_weakLocalValue_refuted`, `ThreeCellRefuted.lean`; found by the round-3
   adversarial audit's LP, which fixes the menu and minimises the forced strategy's Value slack
   over the trust polytope — the reverse of the round-0 search order). Through repair round 2
   this case was the package's OPEN `localTotalTrust_imp_weakLocalValue_open`; its statement is
   false (`weakLocalValue_open_statement_false`), it is withdrawn, and the open list is empty.
3. The literal reading restricted to `hdet`-frames (rows on the support determined by the
   pushforward `Q_* P_w`, where every recommended strategy is tie-consistent) is a theorem at
   two cells (`valuesWrt_questionOf_of_simpleTrustOn`) and **implies** the weak form on all
   frames (replace each row by a canonical representative of its pushforward class; local Total
   Trust depends only on `(Q w, Q_* P_w, π w)` and transfers; a winning recommended strategy for
   the `hdet`-frame is a function of the pushforward, hence a recommended strategy for the
   original frame with the same value), so it falls with it — and directly: the refuting frame
   is itself an `hdet`-frame (`localTotalTrust_imp_localValue_hdet_refuted`).

So fn 65's conjecture breaks exactly at three cells: at two cells it holds in the weak and the
`hdet` readings (and fails literally, by ties); at three cells it fails in all three readings,
by a wedge phenomenon with interior types in which no tie is involved.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

/-- **fn 65's conjecture in fn 64's literal reading is refuted**: there is a two-cell question,
a simplex deferrer and a frame with local Total Trust and without local Value.
Source: [[Deference Done Better]] fn 65 l. 1237 (the open direction), fn 64 l. 1235 (the
definition); mandate T4(d) (`localTotalTrust_imp_localValue_open`, refuted rather than open)
Kind: N+
Fidelity: exact (refutation of the universal statement by one instance)
Hyps: (a) none -/
theorem localTotalTrust_imp_localValue_refuted :
    ∃ (Q : Fin 4 → Bool) (π : Fin 4 → ℝ) (F : Frame (Fin 4)),
      π ∈ stdSimplex ℝ (Fin 4) ∧ TotalTrustWrt Q π F ∧ ¬ ValuesWrt Q π F :=
  ⟨questionOf qtie, πtie, tie4, tie4_refutes_two_cell.1, tie4_refutes_two_cell.2.1,
    tie4_refutes_two_cell.2.2⟩

/-- **The finest question**: on a simplex deferrer, Total Trust gives weak Value with respect to
`id` — DDB Theorem 2.2 (`value_iff_totalTrust`) with Lemma 7.5 (`value_iff_weakValue`). With
the two-cell theorem this is the true part of the weak reading; the three-cell case is refuted
(`ThreeCellRefuted.lean`).
Source: [[Deference Done Better]] Theorem 2.2, Lemma 7.5; audit r1 N12
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex ℝ W`, `TotalTrust π F` -/
theorem totalTrust_imp_weakValuesWrt_id {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}
    {F : Frame W} (hπ : π ∈ stdSimplex ℝ W) (h : TotalTrust π F) :
    WeakValuesWrt (id : W → W) π F :=
  weakValue_iff_weakValuesWrt_id.1 ((value_iff_weakValue hπ F).1 ((value_iff_totalTrust hπ F).2 h))

/- The OPEN `localTotalTrust_imp_weakLocalValue_open` (fn 65's conjecture in the weak reading,
`∀ Q π F, π ∈ stdSimplex → TotalTrustWrt Q π F → WeakValuesWrt Q π F`, `sorry`) stood here
through repair round 2. Its statement is false — `ThreeCellRefuted.lean`,
`localTotalTrust_imp_weakLocalValue_refuted` / `weakLocalValue_open_statement_false` (repair
round 3, after audit r3 adversarial B1) — so it is withdrawn rather than kept as a listed open
statement. -/

end

end Cleanroom.Corrigibility.CorrLegitGeneral
