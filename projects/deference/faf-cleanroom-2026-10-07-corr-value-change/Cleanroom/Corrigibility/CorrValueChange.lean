import Cleanroom.Corrigibility.CorrValueChange.Model
import Cleanroom.Corrigibility.CorrValueChange.Table
import Cleanroom.Corrigibility.CorrValueChange.TwoStep
import Cleanroom.Corrigibility.CorrValueChange.Product
import Cleanroom.Corrigibility.CorrValueChange.Examples14
import Cleanroom.Corrigibility.CorrValueChange.Update
import Cleanroom.Corrigibility.CorrValueChange.Epist
import Cleanroom.Corrigibility.CorrValueChange.Good
import Cleanroom.Corrigibility.CorrValueChange.Fine
import Cleanroom.Corrigibility.CorrValueChange.Epistemicize
import Cleanroom.Corrigibility.CorrValueChange.Teacher
import Cleanroom.Corrigibility.CorrValueChange.Variants
import Cleanroom.Corrigibility.CorrValueChange.Modest
import Cleanroom.Corrigibility.CorrValueChange.CondLegit
import Cleanroom.Corrigibility.CorrValueChange.AltForm
import Cleanroom.Corrigibility.CorrValueChange.JeffreyBolker
import Cleanroom.Corrigibility.CorrValueChange.Prop58
import Cleanroom.Corrigibility.CorrValueChange.Supercond
import Cleanroom.Corrigibility.CorrValueChange.TotalTrustTwo
import Cleanroom.Corrigibility.CorrValueChange.Savage
import Cleanroom.Corrigibility.CorrValueChange.RadonNikodym

/-!
# corr-value-change — root module

Value change as epistemic update (faf-cleanroom run, 2026-10-07). Source:
[[value-change-as-epistemic-update]]. Files: `Model` (the finite Kolmogorov model of record and the
simple argument, T1), `Table` (the three-term decomposition, abstractly), `TwoStep` (the evidential
two-step decision, T2), `Product` (facts × configuration, information and payment, T3),
`Examples14` (the §1.4 example and its variants, T4), `Update` ((R), (M), (Z), (R∣L)), `Epist`
(epistemicization, T5), `Good` (Good's theorem for value change, the (A) term, the grades, the
act-value form, T6/T9/T10(e)), `Fine` (Claim 4 and the fine Kolmogorov picture, T6(f), T10),
`Epistemicize` (the two-step model as an epistemic model; (A) = 0 iff epistemicizable, T10(d)),
`Teacher` (the parametrized worked example, T7), `Variants` (coin, pill, the numbers, the tie
counterexamples), `Modest` (the modest teacher, T9(c)), `CondLegit` (reflection conditional on
legitimacy, T8), `AltForm` (its alternative formalization, T8(e)), `JeffreyBolker` (T11 (a)–(e), (g)), `Prop58` (Proposition 5.8, T11(f)), `Supercond`
(radical probabilism and superconditioning, T12), `TotalTrustTwo` (Total Trust for the two-world
source, T9(d), T12(i)(j)), `Savage` (the causal version, T13), `RadonNikodym` (E4, the Radon–Nikodym step of the infinite translation in measure-space form; imports Mathlib measure theory and is reached only through this root). Open list
(`run/wp/corr-value-change/corr-value-change-open.txt`) is empty. Deliverables in
`run/wp/corr-value-change/`.
-/
