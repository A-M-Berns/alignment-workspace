import Cleanroom.Decision.DpFairnessReloc.Iso
import Cleanroom.Decision.DpFairnessReloc.Fair
import Cleanroom.Decision.DpFairnessReloc.Fork
import Cleanroom.Decision.DpFairnessReloc.Relocate
import Cleanroom.Decision.DpFairnessReloc.RelocateThms
import Cleanroom.Decision.DpFairnessReloc.Output
import Cleanroom.Decision.DpFairnessReloc.Singleton
import Cleanroom.Decision.DpFairnessReloc.Witnesses
import Cleanroom.Decision.DpFairnessReloc.LawSets
import Cleanroom.Decision.DpFairnessReloc.Relations
import Cleanroom.Decision.DpFairnessReloc.RelationsThms
import Cleanroom.Decision.DpFairnessReloc.RelationsChain
import Cleanroom.Decision.DpFairnessReloc.RelationsStats
import Cleanroom.Decision.DpFairnessReloc.RelationsWitnesses
import Cleanroom.Decision.DpFairnessReloc.MoreWitnesses
import Cleanroom.Decision.DpFairnessReloc.LawSetsThms
import Cleanroom.Decision.DpFairnessReloc.AuditWitnesses
import Cleanroom.Decision.DpFairnessReloc.TopRepair

/-!
# `dp-fairness-reloc`: fairness grades, relocation and equivalence of subtrees

Root module of the package `Cleanroom.Decision.DpFairnessReloc` (over `dp-core-tree`, imported as
one root module; nothing of it restated). See `run/wp/dp-fairness-reloc/`.

* `Iso`: labelled isomorphism `≅` (`LabIso`), node count, `mapWorld`, the leaf-bijection
  transport of every label Definition 6 reads.
* `Fair`: `subtreeAt`, the continuation `(λ, r)`-law `contLaw` (a finsupp), the grades
  `StronglyFair` / `LawFair` / `ValueFair`, FR-1(i), `NestedFiber`, `Pruned`, T1.
* `Fork`: `StronglyFair → LawFair → ValueFair`, Lemma 1's decompositions over minimal / all
  `d`-nodes, `θ_q`, EQ-5 fork closure.
* `Relocate`: the relocation types, `FinDistr.pi`, `lift`, `resolve`/`relocRoot` with the
  canonical leaf and node maps, leaf invariants, the resolution lemma.
* `RelocateThms`: SE-5(1), FR-7(a), nesting transfer, SE-7′, FR-6, `queried Rel`.
* `Output`: T5 (FR-4 repaired: strong fairness of the output in the pre-enrichment sense) and
  T6 (`O_{d̂} = ⊤`, records at `d̂`, `ρ` derived).
* `Singleton`: Claim B (singleton fibers under EC + FRec + realized observations).
* `Witnesses`: GR-9 (2)/(3), Claim 1.2/L2, the AMD obstruction, the null repair, Claim F's tree,
  Claim B's witnesses.
* `LawSets`: `lawOfW`, the four law-set grades, `∼`, `⊑`, `𝓗`; UN-2, C.1, FR-10, EQ-11, EQ-12,
  E5.
* `Relations`: `≃`, `flatDist`, `≃_Δ`, `≈_tr`, `≈_law`, `≈_val`; the proved links of the chain;
  E1, E2, E3, SL-β0.
* `RelationsThms` (repair round 1): coupling composition; `≃` and `≃_Δ` are equivalences; flat
  couplings as total functions.
* `RelationsChain` (repair round 1): `≃ ⊆ ≃_Δ` (the chain closed);
  `Fair_≅ ⟹ Fair_≃ ⟹ Fair_{≃Δ} ⟹ Fair_{≈tr} ⟹ Fair_{≈law}`.
* `RelationsStats` (repair round 1): trace functionals and EQ-6's per-statistic clauses; EQ-4
  for `≈_tr`, `≃_Δ`, `≃` on pruned trees; EQ-3's corollary (open direction stated, with the
  attempt record); EQ-6's Definition-7 clause (OPEN).
* `RelationsWitnesses` (repair round 1): E4 `recombination` (`≈_tr` holds, `≃_Δ` fails).
* `MoreWitnesses` (repair round 1): `coinSeq` (Claim B with chance, N+), `dd` (realized
  observations load-bearing), `gr3W` (fork closure with a non-trivial event, N+), `cb` (T5
  between the trivial ends; FR-4 as stated refuted).
* `LawSetsThms` (repair round 1): EQ-10 at the function level on almost-fair trees; E5 as the
  witness that the pure grade does not exclude nesting and that EQ-10 fails with nesting.
* `AuditWitnesses` (repair round 2): EQ-4's `≈_val` clause (`degen_fairValEq`; the source's
  witness E5 fails it, `e5_not_fairValEq`, but is `ValueFair` in the act-value grade,
  `e5_valueFair`) and `≈_law` clause (`spur_lawFair`); each hypothesis of Claim B load-bearing
  (`ec_load_bearing`, `fair_load_bearing`); `Pruned` load-bearing in EQ-4
  (`pruned_load_bearing`); the closure clause of `Closed` load-bearing — FR-3 in one step
  (`closure_load_bearing`).
* `TopRepair` (repair round 2): SP-3 — the top repair's act values are the input's pure values
  (`value_deviate_root`) and its best act attains the optimum on almost-fair inputs
  (`AlmostFair.topRepair_best_act`), with the mugging's act values `(y − x)/2` and `0`; V1/V2
  not almost fair and V2 nested at both points (T1); the TN-V2 numbers `V = m(5 − m)`,
  `V′ = 4m`, relocated `4m` (T4(f)).
-/
