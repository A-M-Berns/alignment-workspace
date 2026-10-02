import Cleanroom.Bli.UdtBliLearning.Defs
import Cleanroom.Bli.UdtBliLearning.TheoremA
import Cleanroom.Bli.UdtBliLearning.TheoremB
import Cleanroom.Bli.UdtBliLearning.Calibration
import Cleanroom.Bli.UdtBliLearning.LogWealth
import Cleanroom.Bli.UdtBliLearning.LearningUdt
import Cleanroom.Bli.UdtBliLearning.Shadow
import Cleanroom.Bli.UdtBliLearning.EpsCorr
import Cleanroom.Bli.UdtBliLearning.EpsCorrWitness
import Cleanroom.Bli.UdtBliLearning.Conventions
import Cleanroom.Bli.UdtBliLearning.Omu

/-!
# `udt-bli-learning` · root module

Learning over a BLI prior, on `udt-bli-tiling`'s sequential single-coin iterated mugging
(`SingleCoin.scPrior`): the learning predicates of record over a belief-state sequence and
realized tables (`ActsAs`, `StrongLearnsAt`, `StrongLearns`, `WeakLearns`, `FUpdateful`), the
single-coin belief sequence *derived* by `conditionOn` on the deciding class, the guards (not
universal, not vacuous, horizon-dependent, the all-`n` strong reading self-inconsistent, the
dilemma in the stakes) (`Defs`); Theorem A — strong learning at the decided state and
prior-optimality incompatible, each half inhabited (`TheoremA`); Theorem B's learning half — the
re-frozen policy weakly learns, does not strongly learn at the frozen state, and does not tile
(`TheoremB`); calibrated versus uncalibrated under the external criterion, the full Venn diagram
(`Calibration`); the log-wealth agent's three regimes (none / exactly one / all) by starting
wealth, with the real threshold `w*` (`LogWealth`); "Learning UDT" in two readings, the prefix
reading uninhabitable, the current-state reading inhabited (`LearningUdt`); PDF 14's conjectures
refuted in the finite shadow (`Shadow`); ε-bounded correlations give ε-updateful behaviour, the
asymptotic clause approximate, the exact form stated as a proposition (`EpsCorr`) and refuted on
core's two-table carrier, where the asymptotic headlines' N+/N− witnesses also live
(`EpsCorrWitness`; the package has no open statement since repair round 2); the utility conventions and the
`U_{>n}` claim tested (`Conventions`); open-minded updatelessness on a finite awareness-growth
model of Chicken — EA-OMU's threshold, exploitability, UE-OMU, the b.333 check in two models
(`Omu`). Dependents: none.
-/
