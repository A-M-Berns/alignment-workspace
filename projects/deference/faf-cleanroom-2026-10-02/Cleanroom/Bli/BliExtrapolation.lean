import Cleanroom.Bli.BliExtrapolation.Syntax
import Cleanroom.Bli.BliExtrapolation.Chain
import Cleanroom.Bli.BliExtrapolation.Measure
import Cleanroom.Bli.BliExtrapolation.Soto
import Cleanroom.Bli.BliExtrapolation.Gaifman
import Cleanroom.Bli.BliExtrapolation.Witnesses
import Cleanroom.Bli.BliExtrapolation.Refutations
import Cleanroom.Bli.BliExtrapolation.Conditioning
import Cleanroom.Bli.BliExtrapolation.Extension
import Cleanroom.Bli.BliExtrapolation.ConstraintWitnesses
import Cleanroom.Bli.BliExtrapolation.Dyadic
import Cleanroom.Bli.BliExtrapolation.Decay
import Cleanroom.Bli.BliExtrapolation.Product

/-!
# `bli-extrapolation`: Soto's extrapolation — the conditional-chaining measure, its Gaifman
property and the limit inequalities

Root module of the package `bli-extrapolation` (area `bli`, namespace
`Cleanroom.Bli.BliExtrapolation`). A dependent imports this one name and gets:

* **Syntax** — the abstract quantifier structure `UnivStructure` (design decision 1), `Ax`,
  semantic `AxEntails`/`AxConsistent` (decision 2), `Ax_satisfiable`, the enumerated coordinates
  `conj`/`enumWorld`/`level` (decision 3), the locality structure `UnivStructure.Local` and the
  transfer lemma `axEntails_decidable` (claim (ii) is locality-relative; `Local` is inhabited in
  `Witnesses` by `mkAtomicLocal` for the fresh-atomic template: `halvingS_local`, `enumS_local`).
* **Chain** — `CondRule`, `chainPMF`, `chainVal`, projectivity, the four Gaifman clauses in
  rational form, the cylinder value, and the conditioning-is-definitional lemma
  `chainVal_and_atom` (a finitely additive content; never called a measure).
* **Measure** — `chainVal_gaifman`, **`chainMeasure := gaifmanMeasure _ …`** (FAF's σ-additive
  object, route α), `chainMeasure_sentence`, `chainMeasure_conj`, `chainMeasure_unique`, the a.e.
  lemmas.
* **Soto** — `axClause`, `sotoRule`, `sotoPMF`, `extrapolate`, `extrapolateVal`,
  `BaseAxConsistent`; `sotoPMF_eq_baseMarginal`, `extrapolate_extends`, `extrapolateVal_eq_base`,
  `sotoPMF_zero_of_inconsistent`, **`extrapolate_ae_Ax`**, `extrapolate_gaifman` (claim (i)),
  `extrapolateVal_eq_sum_axEntails` (3b), `extrapolate_conditional_small` (3d).
* **Gaifman** — `univEvent`/`instEvent`; **`gaifman_le`** (4a), `tendsto_conj_instances`;
  `HiddenUniversal`, **`gaifman_lt_of_hiddenUniversal`** (4d); `HalvingCondition`,
  **`gaifman_eq_of_halving`** (4b); `FreshInstances`, `halving_of_fresh_instances` (4e);
  `tendsto_first_counterexample` (4c(i)).
* **Witnesses** — family-`8` fresh atoms, `freshEnum`, the template `mkStructure`,
  `halving_witness`/`halving_measures` (4b, N+), `extrapolate_depends_on_enumeration` (3e, N+).
* **Refutations** — `refute_second_inequality` (2-006; `refuted`) and `refute_propagation`
  (057 (ii)), both N+ with positive base mass.
* **Conditioning** — `chainMeasure_cond_cylinder` (5a), `constraint2Rule`/
  `constraint2_definitional` (5b; sentence-valued price events, exclusive almost everywhere
  under the base) and `introspectionRule`/`introspection_definitional` (5b),
  `chain_inside_support_fixed`, `partition_gives_balance` (5c; a.e.-exclusive cells).
* **Extension** — `FullSupport`, `extrapolate_pos_of_axConsistent`, `sotoPMF_pos_of_prefix_pos`,
  `extrapolate_zero_iff` (target 10).
* **ConstraintWitnesses** — `constraint2_witness` (5b/5c, N+: a two-price grid on two
  a.e.-exclusive atoms with masses `⅓`, `⅔`, balance `7/12`), `halving_fullSupport` and
  `halving_pos_of_axConsistent` (10, N+).
* **Dyadic** — `dyadicSentence`, `digitSentence`, the one-sided cell lemmas, the off-grid iff,
  `digitSentence_holds_iff`, and the held-cell sequence `cellIdx` (existence, uniqueness,
  nesting) giving `values_eq_of_digits`, the soundness of Soto's rewrite of `X = Y` (target 6),
  and `not_digits_of_values_eq` (the converse fails on the grid). No `OPEN` declarations remain
  in the package.
* **Decay** — `instPrefix`, `negUnivPrefix_val_pow`, `extrapolateVal_univ_and_instPrefix`,
  **`decay_scheme_pow`**, **`decay_scheme_is_half_rule`** (PDF 06 eq. (1) is the ½-rule under the
  halving hypotheses), `decay_scheme_of_halvingCondition`, `decay_witness` (N+) (target 4c(ii)).
* **Product** — `productRule`, `CondRule.IsProduct`, `chainPMF_productRule`,
  **`chainMeasure_productRule_indep`** (coordinates independent via cylinder factorisation),
  `UnivStructure.TrivialAx`, `IsProductBase`, `SotoIsProductAe`,
  **`sotoRule_eq_productRule_iff`** (on positive-mass prefixes), `sotoRule_isProduct_iff_of_pos`
  (the literal form under full support), and the guard counterexample
  `sotoRule_guard_not_isProduct` showing the literal iff is false in general (target 5d; F-13).

Not landed (recorded in the report): the `Primrec` form of 3c, target 8 (`paperUnivStructure`)
and target 9 (`truncatedFirm`).
-/
