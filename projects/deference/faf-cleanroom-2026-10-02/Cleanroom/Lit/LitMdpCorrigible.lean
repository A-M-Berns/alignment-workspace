import Cleanroom.Lit.LitMdpCorrigible.Mdp
import Cleanroom.Lit.LitMdpCorrigible.Limit
import Cleanroom.Lit.LitMdpCorrigible.Hudson
import Cleanroom.Lit.LitMdpCorrigible.HardButton
import Cleanroom.Lit.LitMdpCorrigible.Worked
import Cleanroom.Lit.LitMdpCorrigible.WorkedMdp
import Cleanroom.Lit.LitMdpCorrigible.Grid
import Cleanroom.Lit.LitMdpCorrigible.Interrupt
import Cleanroom.Lit.LitMdpCorrigible.Holtman
import Cleanroom.Lit.LitMdpCorrigible.Nayebi
import Cleanroom.Lit.LitMdpCorrigible.Reconcile

/-!
# `lit-mdp-corrigible`: MDP-level corrigibility — Hudson, Holtman, Orseau–Armstrong, Nayebi

Root module. A dependent imports this one name and gets the finite MDP carrier over FAF's `Distr`
(`FinMDP`, horizon-indexed `Vpol`/`Vopt`, `optSet`, the pathwise kernel-agreement lemma, the
Bellman-fixed-point horizon limit), Hudson's goal-in-state MDPs with the definitions of record
(`Corrigible`, `Interruptible`, `P_C` as a `Distr.map` push-forward, Condition 1, equilibrium
optimality, goal tampering, the split action space and the transformation `R_C`), Theorem 3.1's
corrigibility half in both readings (`T` in reading A, `C` in reading B), accept-dominance,
Propositions 3.3 and 3.4, the performance clause stated; the hard button and the hurry incentive
(T5) with the non-interruptible instance; the one-MDP worked example in both coordinates
(`Worked`, `WorkedMdp`) and Hudson's Figure-2 gridworld with the physical-channel finding
(`Grid`); Orseau–Armstrong's safe interruptibility with Theorem 8 on Figure 2 at constant `θ`
(`Interrupt`; sequence form OPEN); Holtman 2020's S1 by his horizon induction with the car-factory
witness (`Holtman`); Nayebi's Proposition 1 anatomy (`Nayebi`) and the Hudson–Nayebi reconciliation
witness (`Reconcile`).

Files: `Mdp` (carrier), `Limit` (T20 elementary), `Hudson` (T1–T4), `HardButton` (T5), `Worked`
(T6–T9, T11, ThreeStep side), `WorkedMdp` (T6–T8, T11, Hudson side), `Grid` (T10), `Interrupt`
(T12), `Holtman` (T13), `Nayebi` (T14), `Reconcile` (T18).
-/
