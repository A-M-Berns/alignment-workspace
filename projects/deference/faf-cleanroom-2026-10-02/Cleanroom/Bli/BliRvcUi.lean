import Cleanroom.Bli.BliRvcUi.Rvc.Defs
import Cleanroom.Bli.BliRvcUi.Rvc.Antitone
import Cleanroom.Bli.BliRvcUi.Rvc.Finite
import Cleanroom.Bli.BliRvcUi.Rvc.Grid
import Cleanroom.Bli.BliRvcUi.Rvc.Process
import Cleanroom.Bli.BliRvcUi.Limit
import Cleanroom.Bli.BliRvcUi.Rvc.LimitB
import Cleanroom.Bli.BliRvcUi.Rvc.Paper
import Cleanroom.Bli.BliRvcUi.Rvc.Linearity
import Cleanroom.Bli.BliRvcUi.Ui.Defs
import Cleanroom.Bli.BliRvcUi.Ui.Limit
import Cleanroom.Bli.BliRvcUi.Ui.Finite
import Cleanroom.Bli.BliRvcUi.Ui.Lia
import Cleanroom.Bli.BliRvcUi.Ui.Paper
import Cleanroom.Bli.BliRvcUi.Ui.Free
import Cleanroom.Bli.BliRvcUi.Hm.Defs
import Cleanroom.Bli.BliRvcUi.Hm.Paper

/-!
# `bli-rvc-ui`: real-value coherence, universal instantiation, hypothetical marginalization

Root module of the package `bli-rvc-ui` (area `bli`, namespace `Cleanroom.Bli.BliRvcUi`). A
dependent imports this one name and gets, over FAF's objects (`LUV`, `expectApprox`, `ValuesAt`,
`DeductiveProcess.union`, `limitingBelief`, `paperDP T`, `BooleanQuoteCode`/`RationalQuoteCode`)
and the run's `bli-found` / `bli-finite`:

* **Rvc/Defs** — the objects of record for real-value coherence: `thresholdAtoms`, `monoFacts`,
  `rangeFacts`, `RVC_B` (a finite mixture of point values), `ThresholdAntitone`, `SumValued`,
  `RVC_E_exact`, `RVC_E_eps`; a valued world holds the monotonicity facts always and the range
  facts when `1 ∉ R` (the boundary threshold is undetermined by FAF's cut semantics, F-12).
* **Rvc/Antitone** — `rvcB_iff_antitone`: `RVC_B` ⟺ threshold beliefs in `[0,1]`, antitone,
  `1` below `0`, `0` at or above `1` (the mixture built by induction on the sorted thresholds,
  points strictly inside the gaps).
* **Rvc/Finite** — **T2.1** `rvcB_iff_twoAxiom` (load-bearing): `RVC_B` ⟺ a two-axiom-coherent
  extension on the threshold algebra relative to the monotonicity and range facts
  (`bli-finite`'s `TwoAxiomCoherent`), with `rvcB_of_twoAxiom` needing no injectivity; **T2.2**
  `rvcB_witness` (N+, mixture exhibited) and `rvcB_fails_increasing` (N−).
* **Rvc/Grid** — **T1.1** `rvcE_exact_fails` (refuted, N+: exact additivity of the grid
  expectation fails at a single world valuing `Z = X + Y`, for every precision `k ≥ 1`); **T1.2**
  `rvcE_eps_of_worldMixture` / `rvcE_eps_of_worldMarginal` (ε = `3/k`, the mesh).
* **Rvc/Process** — **T2.4** `rvcB_of_D_PC` (D-RVC(B) is D-PC on the threshold atoms plus the
  process's facts; the facts are a disclosed (c) at finite days) and T1.2's bridge to
  `Constraints.CoherentOn` / `D_PC` (`rvcE_eps_of_coherentOn`, `expect_eps_of_D_PC`).
* **Limit** — semantic monotonicity of `limitingBelief` in completed-theory worlds
  (`limitingBelief_le_of_theory_imp`) and the limit forms of provability induction and
  non-dogmatism.
* **Rvc/LimitB**, **Rvc/Paper** — **T2.3** `rvcB_limit` (every inductor's limiting belief is
  `RVC_B` on every LUV its completed worlds value, `1 ∉ R`), `rvcB_limit_lia` at
  `liaHistory (paperDP T)` for `bli-found`'s quote LUVs, and T2.1 for quote LUVs.
* **Rvc/Linearity** — **T1.3** `rvcE_limit`: FAF's `thm:loe` at `a = b = 1` (hypotheses (b)).
* **Ui/Defs** — `UIFamily`, `AxProcess` (Soto's schema 1 as a computable process), `UIAt`,
  `UILimit`, `UITwoSided` (refutation target), one-atom override worlds.
* **Ui/Limit** — **T3.3** `ui_imp_limit_one`, `ui_limit_of_union` (load-bearing: UI in the limit
  for every inductor over the augmented process); **T3.7 (a)** `twoSided_ui_unsat`; the generic
  second-limit refutation; `ui_perDay_open` (OPEN).
* **Ui/Finite** — **T3.4** `uiAt_of_coherentOn` (exact UI at a day from stage coherence),
  `coherentOn_of_uiAt_atoms` (the converse for pairwise distinct instance atoms, by the product
  mixture over `C.powerset`), `uiAt_not_coherent_shared` (N−: the converse fails on shared primes).
* **Ui/Lia** — **T3.2** `lia_union_ax_isLI`: FAF's construction over the augmented process is a
  logical inductor (Soto's Step 1 without the trade-elimination argument).
* **Ui/Paper** — **T3.5** `ui_strict_fresh` / `ui_strict_fresh_lia` (N−: the universal-role atom
  stays `< 1` while every instance `→ 1`, but the instances are theorems, so the schema is inert
  in the limit — F-19); **T3.6** `ui_limit_paperDP` (D-UI in the limit over `paperDP T` with no
  schema process); **T3.7** `twoSided_ui_unsat_paper`, `secondLimit_fails_ax` (N−: the sibling
  is inert at theorem instances); `ui_strict_paper_open` (OPEN).
* **Ui/Free** (repair round 1) — free instance atoms (family `9`, payloads `⟨2, c⟩`) tied to
  `u := freshAtom 9 ⟨1, 0⟩` / sibling `⟨1, 1⟩` only by the schema: **the N+ for T3.3**
  `ui_free_nontrivial` / `ui_free_paper` / `ui_free_paper_lia` (`0 < P∞(u) < P∞(inst c) < 1`,
  strict by `limitingBelief_lt_of_theory_imp`); **the N+ for the sibling mechanism of T3.7 (b)**
  `secondLimit_fails_free` / `_paper` / `_paper_lia` with `free2_inst_lt_one` (the instances stay
  undecided); the block override `famWorld`.
* **Hm/Defs**, **Hm/Paper** — `hmSentence`/`hmLuv`/`HMExact` (code-level, no market);
  **T4.2** `hm_reflected` (load-bearing), **T4.3** `hm_exact_of_coherentOn` (load-bearing: exact
  HM is D-PC relative to the process from the entry day), **T4.4** `hm_limit`/`hm_seq_true`/
  `hm_seq_false`/`hm_lia_seq_true`, **T4.5** `hmLuv_valuesAt`/`hmLuv_expect_near`, **T4.6**
  `hm_witness`/`hmLuv_witness` (N+), **T4.7** `ReflectionSoto` (ATTRIBUTION-UNVETTED, `rfl`).

Fresh-atom families used (for `bli-found`'s registry): family `9` (UI atoms: universal-role
payloads `⟨0, 0⟩`, `⟨0, 1⟩`, `⟨0, 2⟩`, `⟨1, 0⟩`, `⟨1, 1⟩`, free instances `⟨2, c⟩`; the mandate said
`7`, which the registry now assigns to `bli-transfer`), family `8` (RVC witness thresholds,
payloads `⟨0, ⟨j, encode r⟩⟩`).
-/
