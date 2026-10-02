import Cleanroom.Info.InfoVoiLatents.Finite
import Cleanroom.Info.InfoVoiLatents.Coverage
import Cleanroom.Info.InfoVoiLatents.Voi
import Cleanroom.Info.InfoVoiLatents.VoiWitness
import Cleanroom.Info.InfoVoiLatents.Bridge
import Cleanroom.Info.InfoVoiLatents.Shannon
import Cleanroom.Info.InfoVoiLatents.Eig
import Cleanroom.Info.InfoVoiLatents.EigWitness
import Cleanroom.Info.InfoVoiLatents.Split
import Cleanroom.Info.InfoVoiLatents.SplitWitness
import Cleanroom.Info.InfoVoiLatents.SplitValuePart
import Cleanroom.Info.InfoVoiLatents.SplitComposed
import Cleanroom.Info.InfoVoiLatents.SplitInfoForm
import Cleanroom.Info.InfoVoiLatents.VoiHarmMass
import Cleanroom.Info.InfoVoiLatents.Mediation
import Cleanroom.Info.InfoVoiLatents.MediationAssembly
import Cleanroom.Info.InfoVoiLatents.Hazard
import Cleanroom.Info.InfoVoiLatents.HazardMeans
import Cleanroom.Info.InfoVoiLatents.NaturalLatents
import Cleanroom.Info.InfoVoiLatents.NaturalLatentsWitness
import Cleanroom.Info.InfoVoiLatents.NaturalLatentsWitnessFour
import Cleanroom.Info.InfoVoiLatents.NaturalLatentsStochastic
import Cleanroom.Info.InfoVoiLatents.Turner
import Cleanroom.Info.InfoVoiLatents.Psi
import Cleanroom.Info.InfoVoiLatents.Open

/-!
# info-voi-latents — root module

Information bounds over FAF's `ShannonInformation` and `Condensation`, for the corrigibility
generalization thread: Pinsker on the finite simplex (`Finite`), coverage (`Coverage`), the VOI
bound chain over `Blackwell.Experiment` with its witnesses and the bridge to PFR's mutual
information (`Voi`, `VoiWitness`, `Bridge`), generic Shannon lemmas FAF lacks (`Shannon`), the EIG
identity over `condMutualInfo` (`Eig`, `EigWitness`), the value/empirical split and the θ hole
(`Split`, `SplitWitness`) with what "the value part" can and cannot mean (`SplitValuePart`) and
the composed Target 4(v) bound refuted, attained, and `HVal` versus its information form
(`SplitComposed`), H_val's information form `I[θ : S | Λ] = 0` on the joint measure
(`SplitInfoForm`), harm mass versus regret mass with the binary case where S2's sentence is true
(`VoiHarmMass`), the repaired S5 pieces (`Mediation`) and their assembly under H3–H4
(`MediationAssembly`), the component-hazard chain (`Hazard`) with the inert press in product form
and the Pinsker clause in expectation (`HazardMeans`), the
exact two-variable natural-latents theorem over Condensation (`NaturalLatents`, the N− `Λ = X₁`
instance `NaturalLatentsWitness`, the N+ four-bit witness `NaturalLatentsWitnessFour`, and the
stochastic form with the approximate `2ε₃` bound, `NaturalLatentsStochastic`), Turner's
corrigibility as a channel capacity (`Turner`), Ψ (`Psi`), and the open statements (`Open`).
Dependents import this one name.
-/
