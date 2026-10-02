import Cleanroom.Bli.BliLinkage.Defs
import Cleanroom.Bli.BliLinkage.Bridge
import Cleanroom.Bli.BliLinkage.Determination
import Cleanroom.Bli.BliLinkage.Trilemma
import Cleanroom.Bli.BliLinkage.Degenerate
import Cleanroom.Bli.BliLinkage.Faith
import Cleanroom.Bli.BliLinkage.Existence
import Cleanroom.Bli.BliLinkage.Asymptotic
import Cleanroom.Bli.BliLinkage.InstanceB2
import Cleanroom.Bli.BliLinkage.Interval
import Cleanroom.Bli.BliLinkage.InstanceB2Point
import Cleanroom.Bli.BliLinkage.InstanceK3
import Cleanroom.Bli.BliLinkage.LiaSupport
import Cleanroom.Bli.BliLinkage.LiaPackage
import Cleanroom.Bli.BliLinkage.InstanceK3Grid
import Cleanroom.Bli.BliLinkage.InstanceK3Local
import Cleanroom.Bli.BliLinkage.AttemptA
import Cleanroom.Bli.BliLinkageB

/-!
# `bli-linkage` — Linkage: 4′ forced, the determination theorem and trilemma, no degenerate
linked BLI, faith scope, B2 existence (reconciled package)

Root module of the dual package `bli-linkage` (area `bli`, namespace `Cleanroom.Bli.BliLinkage`),
reconciled from attempt A (`Cleanroom.Bli.BliLinkage.AttemptA`, exact cell-literal linkage) and
attempt B (`Cleanroom.Bli.BliLinkageB`, interval linkage), both kept as evidence and imported
here. Report, findings, ledger and open list: `run/wp/bli-linkage/`.

* **Defs** — the definitions of record (attempt B's, re-exported, with the reasons) and the
  faith predicate `E2xσIdx` (attempt A's).
* **Bridge** — the definitional conversion `ofB` from the record family to attempt A's, under
  which `stateOf`, `cellMass`, `D_NNUcell`, `Degenerate`, `PCPσTheory` agree.
* **Determination** (K1/K2) — the per-day partition engine, `forced_marginal` (4′ forced),
  `determination` (the theorem of record: plain stage coherence, `SpuriousEntails`, `E2xσIdx`),
  `trilemma_T0`, `no_T2_over_coherent_base` (this run's), `determination_partition` (A's variant).
* **Trilemma** (K2) — the horns T1/T2/T3, T0 at the witness base, sharpness, the N+ package
  inhabitant, `no_T2_over_dP`, the decoupled-literal witness `dissolution` (N−; see
  **Interval**), the bracket determination theorems and `theory_coherent_e1x_decides`.
* **Interval** (repair round 1, audit r1 B1) — the dissolution artifact made exact (the
  literals are decoupled from the price; the same package over price-coupled literals has
  `D_NNUcell` true), and the **transfer theorem** `interval_determination`: with
  price-reflected literals the interval-state package forces the exact identity — the trilemma
  stands under interval linkage over mixtures of worlds that reflect the literals (angle B's
  decisive question, answered with that qualifier; no B2 instance of the transfer theorem);
  N+ at the abstract witness.
* **Degenerate** (K3) — K3a's indicator, the price-reading trader `sellCells` (certificate,
  exploitation with `hmove` explicit), the conclusion of record `no_degenerate_linked_bli`;
  attempt A's `buyOne` engine and the summability N−.
* **Faith** (K4) — the pinning mechanism, K4a abstract and at B2 over FAF's diagonal (both
  attempts' forms), K4b `liar_notMem_Sminus`, `halfRound_cell_excludes_truth`, K4c scoped (N−).
* **Existence** (K5a/b) — the abstract finite iff, the product coupling of record on the coded
  tables, support and positivity, the N+.
* **Asymptotic** (K5c) — FAF's `thm:ceu` in threshold form (a citation).
* **InstanceB2** — K1/K2 at `𝗜𝚺₁`, `halfRound`, the fixed grid over `E2xσIdx`; the pinned set
  eventually non-empty; the refutations deciding which faith predicate a B2 instance can carry
  (`E2xσ` never, `E2xσIdx` at most a point mass on `[⌜⊥⌝, ⌜⊤⌝]`); K3 at FAF's LIA (fixed
  coordinate).
* **InstanceB2Point** (repair round 1, audit r1 adversarial B2) — the B2 package at `rep01`
  inhabited by the point mass on a completed-theory world, conditional on the LIA's rounded
  prices of `⊥`/`⊤` being `0`/`1` on every day `m ≥ 1`, which holds from some day on
  (provability induction, `tbl01_eventually`), and that condition sharp
  (`pointMass_faith_forces_rep`); the superbelief-side K3 predicates jointly satisfiable with
  the base equal to the superbelief in the no-move regime (`pointMass_degenerate_of_still` —
  **not** an inhabitant of any K3 instance's package, repair r2).
* **InstanceK3** (repair round 1, audit r1 fidelity B2) — for a fixed coordinate `hmove` forces
  the limit price to be exactly `1/2` (`hmove_fixed_forces_limit_half`) and is false at `⊥`/`⊤`
  (`not_hmove_falsum`/`_verum`); the **family form** `no_degenerate_linked_bli_LIA_family` over a
  machine-metered coordinate family, of which the fixed-`c` instance is the constant case; on
  the fixed grid's index its `hpin ∧ hmove` is contradictory for every family
  (`family_hmove_false_on_witnessIndex`, repair r2).
* **LiaSupport** (repair round 3) — FAF plumbing: the LIA's day-`n` belief state lists at
  most `∑_{j ≤ n} (progClock j n + 1) ≤ ∑_{j ≤ n} (j (n+1)^j + j + 1)` sentences, for every
  deductive process (`liaStates_support_card_le`, `_poly`; `2945` on day `4`) — the maker's
  support lies in the firm's, the firm is a join of clocked enumerated traders, and the
  decoder emits at most one trade per token.
* **LiaPackage** (repair round 2, audit r2 B1 of both lenses; repair round 3, audit r3 B1) —
  what the K3 package demands of the base: exact finite-day coherence on the small sentences
  (`⊥` at `0`, `⊤` at `1`, every small stage theorem and **every small tautology** at `1`,
  every small complementary pair priced to `1`), at FAF's LIA in support form (all of them
  listed keys: `2^(2^n − 2)` on day `n`); the point mass cannot carry the LIA's `E1x`; and the
  **refutation** `not_lia_small_coherent_mixture_exists` (every `DP`): no stage mixture on the
  small sentences agrees with FAF's LIA — the round-2 OPEN is false, and the three K3
  instances at the LIA are vacuous.
* **InstanceK3Local** (repair round 3) — the vacuity made explicit (each LIA instance's
  conclusion with `hχ` and `hmove` dropped), and the K3 instances **with content**: the local
  form `Degenerate.no_degenerate_linked_bli_lit` (`E1xLit`, agreement on the pinned cell
  literals only, which is all K3 uses) at FAF's LIA, family and one-coordinate forms, with
  `hχ` and `hmove` the hypotheses; what its package demands of the LIA is one listed sentence
  a day with exact quote `1` (`lit_package_forces_today_listed`), not counted out.
* **InstanceK3Grid** (repair round 2, audit r2 adversarial B2) — the one-coordinate grid
  listing a varying machine-metered family (`oneIndex`/`oneStates`/`oneSystem`, `degOne`),
  its grid condition and eventual pinning discharged, and the instance
  `no_degenerate_linked_bli_LIA_oneCoord` whose only hypotheses are `hχ` and `hmove`; the
  point mass on this grid carries the superbelief-side package **iff** the family's rounded
  price never moves (`pointMass_oneCoord_package_iff_still`, base = the point mass itself).
* One OPEN: `BliLinkageB.InstanceMoves.leakQ_rounded_price_moves` (K3's "moves" clause at
  `bli-leak`'s family; stated once, in attempt B; as stated it instantiates no K3 instance at
  `paperDP`, see `InstanceK3`), listed in `bli-linkage-open.txt`. The round-2 OPEN
  `lia_small_coherent_mixture_exists` is **refuted** (`LiaPackage.not_lia_small_coherent_mixture_exists`).

Module count after repair round 3: 17 main modules (this root + 16), attempt A's 10, attempt
B's 19 — 46 in all.
-/
