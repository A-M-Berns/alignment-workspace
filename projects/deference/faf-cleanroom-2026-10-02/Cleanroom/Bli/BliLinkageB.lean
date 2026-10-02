import Cleanroom.Bli.BliLinkageB.Defs
import Cleanroom.Bli.BliLinkageB.Mixture
import Cleanroom.Bli.BliLinkageB.Bracket
import Cleanroom.Bli.BliLinkageB.Determination
import Cleanroom.Bli.BliLinkageB.Dissolve
import Cleanroom.Bli.BliLinkageB.InstanceB2
import Cleanroom.Bli.BliLinkageB.Witness
import Cleanroom.Bli.BliLinkageB.Faith
import Cleanroom.Bli.BliLinkageB.FaithB2
import Cleanroom.Bli.BliLinkageB.Trader
import Cleanroom.Bli.BliLinkageB.Degenerate
import Cleanroom.Bli.BliLinkageB.TraderCells
import Cleanroom.Bli.BliLinkageB.DegenerateCells
import Cleanroom.Bli.BliLinkageB.InstanceCells
import Cleanroom.Bli.BliLinkageB.Trilemma
import Cleanroom.Bli.BliLinkageB.InstanceMoves
import Cleanroom.Bli.BliLinkageB.ProductLaw
import Cleanroom.Bli.BliLinkageB.Existence

/-!
# bli-linkage, angle B — root module

Interval linkage with overlapping open cells (bli-found F-16), and the decisive question of
whether the linkage trilemma dissolves under it. See `run/wp/bli-linkage/attempt-b/` for the
report, findings and ledger. Modules: `Defs` (definitions of record), `Mixture` (the partition
engine), `Bracket` (the bracket determination theorem and the two-sided bracket balance),
`Determination` (the exact determination theorem at the stage level and `D_NNUcell` forced),
`Dissolve` (the N+ witness that interval-only linkage forces nothing exact), `InstanceB2` (the
B2 instances at `𝗜𝚺₁`, `halfRound`, `fixedStates`, with the pinned set eventually non-empty and
K2 instantiated), `Witness` (the N+ witness inhabiting the determination theorem's package), `Faith` (K4: faith at
a decided sentence pins the value; K4a abstract; the vacuity mechanism), `FaithB2` (K4 over
FAF's diagonal: the liar's reflection, K4b's scope lemma, K4a at B2), `Trader` (K3b: the
one-share trader, its certificate, exploitation with `hmove` explicit), `Degenerate` (K3a under
interval linkage and in literal form; the conclusions of record, first form). Continuation 1
added `TraderCells` (the price-reading trader `sellCells`, whose certificate needs no metering
of today's cell — findings FB-14), `DegenerateCells` (K3's conclusion of record in instantiable
form), `InstanceCells` (K3 at FAF's LIA over `paperDP 𝗜𝚺₁`, `hmove` the only underived
hypothesis), `Trilemma` (the three horns T1–T3 inhabited, T0 at the witness base, sharpness;
FB-15: "drop coherence" is not a free horn), `InstanceMoves` (the OPEN
`leakQ_rounded_price_moves`; the package's only cross-package import, `BliLeak.Instance`),
`ProductLaw` (K5a/b over function-tables: the product coupling, its marginals and balance, the
abstract finite iff, support and positivity) and `Existence` (K5a on the package's coded
tables: `exists_superbelief_of_d_nnucell`, the product coupling of record, with its N+).
-/
