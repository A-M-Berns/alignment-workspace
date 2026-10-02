import Cleanroom.Bli.UdtBliSist.Defs
import Cleanroom.Bli.UdtBliSist.Sist
import Cleanroom.Bli.UdtBliSist.SistWitness
import Cleanroom.Bli.UdtBliSist.Skeleton
import Cleanroom.Bli.UdtBliSist.Independence
import Cleanroom.Bli.UdtBliSist.Crux
import Cleanroom.Bli.UdtBliSist.CruxWitness
import Cleanroom.Bli.UdtBliSist.Freedom
import Cleanroom.Bli.UdtBliSist.Homework
import Cleanroom.Bli.UdtBliSist.FourTables
import Cleanroom.Bli.UdtBliSist.Inert
import Cleanroom.Bli.UdtBliSist.SymWitness
import Cleanroom.Bli.UdtBliSist.PhCm
import Cleanroom.Bli.UdtBliSist.Iterated
import Cleanroom.Bli.UdtBliSist.ModelB

/-!
# `udt-bli-sist` · root module

SIST and its relatives with honest hypotheses, over `udt-bli-core`'s `FiniteBLIPrior`: the
class-cut and the two-step objects (`Defs`), the SIST verdict identity with its named models
(`Sist`), and the hand-typed three-table family with the `44.1` instance and the auditor's
alternative table (`SistWitness`), and the verdict over `ofSkeleton` with derived branch beliefs
and the tent instance (`Skeleton`, the N+ of record), and non-degeneracy versus independence: the
Bayes lemma, face constancy ⟹ certainty, the artifact check and Soto's re-weighting
(`Independence`); the finite crux one-step = two-step = `N`-step under the independence hypotheses
with the mugging N− and the abstract partition cut for FIST (`Crux`) and its N+ on the tent prior
(`CruxWitness`); freedom of action, the
`ρ`-threshold at Rec (`Freedom`); and the homework mugging, the written-out versus the term reading
of the policy point (`Homework`). Repair round 1 added the four `0/1` tables (`FourTables`), the
per-node class lemma for reference-point utilities under independent points (`Inert`), the
two-ask-table family inhabiting the symmetric model at `ρ̄ = (1+ρ)/2` (`SymWitness`), the CM/PH
witness and its responsive N− (`PhCm`), the `K`-node family with SIST at every node
(`Iterated`), and the hand-built three-branch Model B beside Model A — cross-branch utility versus
branch re-weighing (`ModelB`). Dependents import this one name.
-/
