import Cleanroom.Trust.TrustMerge.Defs
import Cleanroom.Trust.TrustMerge.SelfInstance
import Cleanroom.Trust.TrustMerge.MirrorFeedback
import Cleanroom.Trust.TrustMerge.Merge
import Cleanroom.Trust.TrustMerge.MergeUniversal
import Cleanroom.Trust.TrustMerge.Hop2
import Cleanroom.Trust.TrustMerge.Hop2Finite
import Cleanroom.Trust.TrustMerge.Classwise
import Cleanroom.Trust.TrustMerge.ClasswiseLUV
import Cleanroom.Trust.TrustMerge.OneBigLie
import Cleanroom.Trust.TrustMerge.Treacherous
import Cleanroom.Trust.TrustMerge.HardCertificate
import Cleanroom.Trust.TrustMerge.Aumann
import Cleanroom.Trust.TrustMerge.Stretch
import Cleanroom.Trust.TrustMerge.WeightClass

/-!
# trust-merge — root module

Cross-agent LUV-Total-Trust and the merge model ([[trust-merge-mandate]]), namespace
`Cleanroom.Trust.TrustMerge`. The definition of record in two grades (`Defs`: `Observable`,
`LUVTotalTrustDay`, `LUVTotalTrustAvg`, `CalibratedAnticipation`; the `Est` notions and
`MergeExpert`); the self instance and the averaged engine (`SelfInstance`); Prop A over the mirror
ledger, Routes A and B (`MirrorFeedback`); `H` endorses `B` on hedged two-option menus (`Merge`);
Hop 2 — the dichotomy, the two-sided bundle and Route A in the averaged grade (`Hop2`), the finite
two-weighting-class lemma (`Hop2Finite`); classwise Value (`Classwise`, `ClasswiseLUV`); the one
big lie (`OneBigLie`); priced out but on no fixed day (`Treacherous`); no hard certificate
(`HardCertificate`); two-agent Aumann, preorder averaging (the closed reading of the modest
disagreement refuted), the no-common-knowledge instance and the non-transitive closed-event
witness (`Aumann`);
non-transitivity stated OPEN (`Stretch`). Dependents import this one name; `MirrorFeedback` and
`Treacherous` are the files importing `Construction.*` (`LIACompiler` via `MirrorPair`;
`Freeze.Oracle`), `Hop2Finite`, `Aumann`, `Classwise`, `OneBigLie` are Mathlib /
`li-asymp-calc` / `TtFiniteFrames.Corr` only.
-/
