import Cleanroom.Corrigibility.CorrGeneralObject.Defs
import Cleanroom.Corrigibility.CorrGeneralObject.Bridge
import Cleanroom.Corrigibility.CorrGeneralObject.Support
import Cleanroom.Corrigibility.CorrGeneralObject.Endorse
import Cleanroom.Corrigibility.CorrGeneralObject.Conjunction
import Cleanroom.Corrigibility.CorrGeneralObject.ExampleA
import Cleanroom.Corrigibility.CorrGeneralObject.PerQ
import Cleanroom.Corrigibility.CorrGeneralObject.Shutdown
import Cleanroom.Corrigibility.CorrGeneralObject.Resist
import Cleanroom.Corrigibility.CorrGeneralObject.ActAdopt
import Cleanroom.Corrigibility.CorrGeneralObject.Path
import Cleanroom.Corrigibility.CorrGeneralObject.Inclusion
import Cleanroom.Corrigibility.CorrGeneralObject.Sigma
import Cleanroom.Corrigibility.CorrGeneralObject.Judge
import Cleanroom.Corrigibility.CorrGeneralObject.Faking
import Cleanroom.Corrigibility.CorrGeneralObject.Witnesses
import Cleanroom.Corrigibility.CorrGeneralObject.Blackwell

/-!
# corr-general-object — root module

The general object of corrigibility (a proposed modification as a pair: push kernel `k` and
target `Q ≪ P`), its three response coordinates, and the general-`Q` dictionary — over
`corr-three-step`'s Setting S (through the bridge `toThreeStep`) and `corr-reflect-frames`'
predicates (faf-cleanroom run, 2026-09-30).

* `Defs` (T0): kernels, product-form push quantities, `AbsCont`, `Endorsed`, `postPush`,
  decision variables and correctness events, `ValueLegit`/`FunLegit`, the value quantities
  (`priorValue`, `informedValue`, `voiPush`, `cellRegret`, `modifiedValue`, `resistanceValue`,
  `procureValue`), the record `Response`.
* `Bridge` (T0): `toThreeStep` and the inherited identities.
* `Support` (T1): a null event raised by the target fails reflection under every anticipation and
  every legitimacy event.
* `Endorse` (T2, T8(a)): the density kernel, existence of an endorsing kernel for every `Q ≪ P`,
  the barycentre theorem (`ReflectiveFor` ⟺ barycentric representation), CE2; dogmatic targets.
* `Conjunction` (T3): acting on `Q` as a conjunction of below-threshold inequalities, the
  base-rate/odds form, the two-action reduction and its three-action failure (A′).
* `ExampleA`: the shared witness carrier.
* `PerQ` (T4): `h_L` read off the target, the per-`Q` rule and threshold through the bridge, the
  adoption bridge, homogeneity, E2, CE1.
* `Shutdown` (T5): the convex shutdown class, desideratum 1 as the conjunction, CE3 through
  `corr-three-step`'s `ce3`.
* `Resist` (T6, T18, T19): the resistance value identity, Good's theorem, decision-local trust,
  the four Example A witnesses, the empty-interior genericity theorem, `R = 0` characterised.
* `ActAdopt` (T7): cellwise (C-act) ⟺ Value (immodest), cellwise literal (C-adopt) = Reflection,
  the informed expert as a `postPush`.
* `Path` (T9): compliance along a convex path is a step function.
* `Inclusion` (T10): common prior plus information inclusion makes every push endorsed.
* `Sigma` (T11): σ-algebra change through `udt-supercondition`'s repaired Thm 2.4.
* `Judge` (T12, T13): the legitimacy judge is `P_t`; self-observation fixed points.
* `Faking` (T14–T17): alignment faking as the compliance rule; `e`-dependence; probes; Brier.
* `Witnesses`: the immodest and modest announcement frames (T7), Example B (T8(b)).
* `Blackwell` (T19(c), repair round 1): `procureValue` is monotone under label-preserving
  garblings of the push and not under relabelling — the Blackwell clause proved in its labelled
  form and refuted as stated, over `lit-ddb-frames`' `BlackwellLE`.
-/
