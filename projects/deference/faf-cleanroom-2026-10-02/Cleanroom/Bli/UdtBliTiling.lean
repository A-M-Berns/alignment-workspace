import Cleanroom.Bli.UdtBliTiling.Defs
import Cleanroom.Bli.UdtBliTiling.Independent
import Cleanroom.Bli.UdtBliTiling.GapWitness
import Cleanroom.Bli.UdtBliTiling.MuggingTiles
import Cleanroom.Bli.UdtBliTiling.IndepCalc
import Cleanroom.Bli.UdtBliTiling.SingleCoin
import Cleanroom.Bli.UdtBliTiling.Refreeze
import Cleanroom.Bli.UdtBliTiling.Layered
import Cleanroom.Bli.UdtBliTiling.Vingean
import Cleanroom.Bli.UdtBliTiling.Omega

/-!
# `udt-bli-tiling` · root module

Tiling and the learning dilemma over a BLI-structured prior, over `udt-bli-core`'s
`FiniteBLIPrior`: the definition of record "no strict preference for precommitment" as a
comparison of ex-ante values of positive-mass policies, the re-frozen prior, self-trust (`Defs`);
one-step tiling under independent points and local utility, derived from core's bridges, with the
full-support independent N+ and the guard that every hypothesis fails somewhere (`Independent`);
the failure without independence on the full-support correlated prior, with the hypothesis audit
(`GapWitness`); the mugging prior tiling for one-step and not for the updateful rule, outside
T1's package, with the tie witness (`MuggingTiles`); the values of an `IndepData` prior for a
utility reading the whole policy (`IndepCalc`); the sequential single-coin iterated mugging with
its verdict, two-step value and re-frozen prior in closed form (`SingleCoin` — the file
`udt-bli-learning` imports alone); the re-freezing dilemma, both directions, "stability iff the
re-freeze changes no decision", self-trust, and the numeric instance (`Refreeze`); the layered
form with Policy Fairness, the implementation-bit layer and the fair/unfair witnesses
(`Layered`); the Vingean obstruction on the mugging at the cross table, with the mandate's
`(Ask, Ask)` form shown to hold (`Vingean`); "don't outthink Omega" as two readings with opposite
verdicts (`Omega`). Dependents import this one name, except `udt-bli-learning`.
-/
