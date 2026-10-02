import Cleanroom.Corrigibility.CorrScimCid.Scim
import Cleanroom.Corrigibility.CorrScimCid.Expect
import Cleanroom.Corrigibility.CorrScimCid.Shutdown
import Cleanroom.Corrigibility.CorrScimCid.Benefit
import Cleanroom.Corrigibility.CorrScimCid.NonObstruction
import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Cleanroom.Corrigibility.CorrScimCid.Incentives
import Cleanroom.Corrigibility.CorrScimCid.FinModel
import Cleanroom.Corrigibility.CorrScimCid.Fig1
import Cleanroom.Corrigibility.CorrScimCid.DSep
import Cleanroom.Corrigibility.CorrScimCid.ThreeNode
import Cleanroom.Corrigibility.CorrScimCid.Dictionary
import Cleanroom.Corrigibility.CorrScimCid.DictionaryRows
import Cleanroom.Corrigibility.CorrScimCid.Eisenstat
import Cleanroom.Corrigibility.CorrScimCid.Bridge
import Cleanroom.Corrigibility.CorrScimCid.Fig1Fin
import Cleanroom.Corrigibility.CorrScimCid.RocksDiamonds
import Cleanroom.Corrigibility.CorrScimCid.Fig1Link
import Cleanroom.Corrigibility.CorrScimCid.TwoLatent
import Cleanroom.Corrigibility.CorrScimCid.CpdWitness

/-!
# `corr-scim-cid`: finite SCIMs and causal influence diagrams with decision nodes

Root module. Files: `Scim` (the SCIM layer over FAF's `Digraph`/`Distr`: CIDs, closed models,
deterministic policies, well-founded evaluation, hard/soft interventions, the master congruence lemma
with consistency and ancestor invariance), `Expect` (product-form conditional expectations and the
support conversions), `Shutdown` (Carey–Everitt's definitions of record), `Benefit` (the alignment
identity, Props 6/8/9, Theorem 10 and its vacuity), `NonObstruction` (Theorem 14 ⟺ with Lemma 22
and the repaired Lemma 23), `Ancestors` (T2: ancestor invariance in CPD form over FAF's `tau`/`tauInv`,
nested counterfactuals, Thm 18 soundness, Holtman's property), `Incentives` (T3: the TI-ignoring class
and the one theorem behind Claims 3/9 and Holtman's ITC), `FinModel` (helpers for the finite
witnesses), `Fig1` (the running example: `π^ro`, `π^mi`, Prop. 15, the entrenching agent), `DSep`
(fully updated deference as d-separation over FAF's `DSeparated`), `ThreeNode` (the converse of
Holtman's property fails), `Dictionary`/`DictionaryRows` (T9: the dictionary SCIM family and its
numbered rows, Prop. I12), `Eisenstat` (T10: the observation node and the martingale condition), `Bridge` (the FAF bridge:
the law of a closed model factorizes over its DAG in FAF's sense).

Added in repair round 1 (after audit r1): `Fig1Fin` (the finite-valued twin of Fig. 1 on which the
FAF bridge is instantiated), `RocksDiamonds` (T3(c): the standard agent tampers, the TI-ignoring
agent does not — the contrast behind Claims 1/3/8), `Fig1Link` (T8(b): on Fig. 1 with `L → O`, an
optimal policy ignoring `H` exists and the mandate's universal fails — Everitt's Def. 10 response
incentive), `TwoLatent` (T9(f): which node the button reads; the I16.1 rows with one number
corrected), `CpdWitness` (the N+ witness for the CPD form of ancestor invariance). `Scim.lean` now
gives the policy space a `Fintype` from finiteness at the decision nodes and their parents alone
(`policyFintype`), so `exists_isOptimal` and every `hopt` are discharged on the models of record.
-/
