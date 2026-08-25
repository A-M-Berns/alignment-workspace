# Repair audit

The dispatch supplied a candidate specification and a hostile audit of it whose
verdict was `LOCAL-REPAIR-REQUIRED` with the architecture surviving. **The
red-team context holding the verbatim text of repairs R1–R5 was lost.** Their
necessary consequences survived in the audit's recap and rerun, which is
authoritative here. What follows reconstructs the minimal repairs directly
against the candidate; it does not reproduce R1–R5 and does not claim to.

Recoverable numbering: the recap states "structural assumptions D1–D2 plus seed
clause Z6 (R1), with seven smaller local fixes (R2–R8)". R6, R7 and R8 survive
verbatim, as does the fragment "§16: for every q ∈ Roots_t", which is R5's
repair text. R2, R3 and R4 are known only through the rerun's dependence on
them: the rerun's EP base cites `Z3'`, and its Norm step cites "R3 guaranteeing
fresh subjects". Everything else below is derived from the candidate plus the
rerun, and is labelled as reconstructed.

## Findings

| finding | source | repair | validation | architecture changed? |
|---|---|---|---|---|
| Demand D1/D2 | surviving hostile recap (R1) | §10: monotonicity under multiset and cited-digest extension; disposition gating, with `Closed ⇒ ∃a. Disposes(a,q)` as its theorem-level form | `test_demand_interface` (10 cases, including the non-monotone and ungated refusals); `test_seed_and_episodes.test_ungated_seed_demand_breaks_episode_uniqueness` executes the one-object counterexample | No |
| Seed strengthening Z3′/Z6 | reconstructed from the hostile rerun + candidate | §4: `Z3'` — every seed root's subject exists; `Z6` — `L_0 = R_0 = N_0 = ∅` | `test_seed_and_episodes.TestSeed` (7 cases) | No |
| Fresh standing and root ids | reconstructed from the hostile rerun + candidate (R3) | §13: F1 allocator injectivity, F2 seed disjointness for standing, F3 the same for root ids; Fresh Allocation theorem | `test_freshness.TestAllocator` (5 cases, including the necessity witness that drops the time component) | No |
| WF / `effect(a)` evaluation order | hostile R6 + candidate | §14: G1–G6 as an ordered conjunction with `effect(a)` defined at G4, after `schemaRef` resolves in the strict pre-state | `test_reason_and_schema.TestSchemaInterface` (4 cases) | No |
| Due-Witness root quantifier | surviving hostile report (R5) | §24: stated for `q ∈ Roots_t`; §19 trichotomy likewise | `test_due_witness` (10 cases; the biconditional is swept over every scenario at every state, and the off-domain case is exhibited) | No |
| Inference-step licensing | R6 | §8: `steps : Derivation → Finset StandingId`; `G3` checks active `PAuth` and never reads the code | `test_reason_and_schema.TestLicensingProvenance` (5 cases) | No |
| Transfer "admissibility" wording | R7 | §16: admissibility via authorization; valid custody assignment ≠ recipient consent | `test_custody.TestTransfer.test_transfer_admissibility_is_not_recipient_consent` | No |
| Cohort notation | R8 | `StandingChanges` defined exactly (§12.3); the cohort package demoted — Source Closure retained as a derived lemma with `I_s^{A_s}` and `New_t^{A_s}` defined (§33), and clause (8) dropped from the main theorem | `test_reaudit.test_source_closure`, `test_reaudit.test_target_coverage` | No |
| `Supersede`/`Transfer` targets outside `dom(Std_{<τ})` | independent re-audit | §12.2: G6 requires domain membership before `delta` reads `pred` and `payload` | `test_freshness.TestEffectPreconditions` (2 cases) | No |
| `cited(ρ)` ranged over all of `N_t`, where `Digest` is defined only on events | independent re-audit | §6: `cited(rho) ⊆ ids(NormEvents_t)` | enforced by `History.append`; exercised throughout `test_demand_interface` | No |
| EP stated for all `x`, where `status_t(x)` is undefined off `dom(Std_t)` | independent re-audit | §20: quantified over `x ∈ dom(Std_t)` | `test_seed_and_episodes.TestEpisodeUniqueness` | No |

The last three are recorded as **reconstructed local audit repairs; exact
original R-numbers unavailable**. They are the only additional defects the
independent pass found, they are all local, and none of them touches a store, a
constructor or a conservation law.

## Exact reconstructed conditions

**D1 (monotonicity).** For every `d`, `q`, multiset inclusion
`ρ⃗ ⊆ ρ⃗′`, and cited-digest maps `δ ⊆ δ′` as graphs — `dom δ ⊆ dom δ′` and
agreement on `dom δ`:

```text
[[d]]_D (q, ρ⃗, δ)  ⇒  [[d]]_D (q, ρ⃗′, δ′)
```

The graph-inclusion hypothesis is the compatibility the cited-digest map
requires, and Digest Stability is what supplies it: `CitedDigest` is monotone
in `ρ⃗` because each digest is a function of its own frozen prefix.

**D2 (disposition gating).**

```text
[[d]]_D (q, ρ⃗, δ) ⇒ ∃ρ ∈ ρ⃗. ∃aid ∈ cited(ρ) ∩ dom(δ).
    id q ∈ roots(ρ) ∧ id q ∈ δ(aid).disposed ∧ δ(aid).τ < τ(ρ)
```

**Z3′.** `∀q ∈ Roots_0. subject(q) ∈ dom(Std_0)`. With Z3 this makes
`subject : Roots_0 → dom(Std_0)` a bijection.

**Z6.** `L_0 = R_0 = N_0 = ∅`.

**Base result.** For `x ∈ dom(Std_0)`:
`status_0(x) ≠ Terminated ⟺ ∃! q ∈ Roots_0. CurrentEpisode_0(q) ∧ subject(q) = x`.
Z6 gives `Responses_0(q) = ∅` and no disposers; D2 then gives `¬Closed_0(q)`,
so every seed root is `Live ∧ ¬Due`; Z1 gives the left side; Z3 and Z3′ give
existence and uniqueness.

**F1–F3.** `tag` and `rootTag` are injective on `(τ, index)`;
`range(tag) ∩ dom(Std_0) = ∅`; `range(rootTag) ∩ ids(Roots_0) = ∅`.

## The four broken theorems, closed

The recap attributes the failure of Fate Monotonicity, Episode Uniqueness,
Custody Locality and the preservation form of No-Invisible-Discontinuity to a
seed root carrying a non-gated or non-monotone demand.

- **Episode Uniqueness.** An ungated seed demand is satisfied by the empty
  response multiset, so the seed root is `Closed` at `t = 0`, no episode is
  current, and EP's base case fails against `status_0(x) = Active`. D2 refuses
  the demand; Z6 supplies `N_0 = ∅`. Executed in
  `test_ungated_seed_demand_breaks_episode_uniqueness`, which asserts the
  failure and then the refusal.
- **Fate Monotonicity.** A non-monotone demand lets `Closed` revert when a
  further response arrives. D1 refuses it. `test_non_monotone_demand_is_rejected`.
- **Custody Locality.** Its proof runs through EP; and separately, a current
  episode closing without a disposition would move custody with no `Transfer`.
  D2 blocks both. `test_custody.TestCustodyLocality`.
- **No Invisible Discontinuity.** The preservation form needs a `Due` witness
  that cannot be closed except through the frozen interface; D2 is what makes
  "closed" imply "was disposed", so the witness cannot evaporate.
  `test_reaudit.TestConservation`.

## Minimality decisions

| item | decision | reason |
|---|---|---|
| `Creditor.Prin` | deleted; `Creditor = Stage (PrincipalId × Time)` | no consumer. Minting stamps `Stage(author a, τ a)` and the seed stamps `Stage(P_0, 0)`; Source Closure reads the time component, which `Prin` does not have |
| `Grounded(q)` | deleted | `GC` is `∀a. WF(a)`; the predicate was constant `⊤` and nothing consumed it. The seed's role is stated in §4 and §26 as prose about where grounding bottoms out |
| `G4₂` (`schemaRef a ∉ fresh(effect a)`) | deleted | redundant once F1–F2 hold: `schemaRef a ∈ dom(Std_{<τ(a)})` by G4, and §13 makes `fresh(effect a)` disjoint from that domain. `test_reaudit.test_self_licensing_is_impossible_without_g4_2` checks the consequence directly |
| cohort partition, clause (8) | demoted out of the main theorem | with `I_s^{A_s}` and `New_t^{A_s}` defined exactly, the partition `I_s = D_t ⊔ R_t` is excluded middle over a set that AC(i) keeps fixed. It adds nothing to successor-root continuity and Due-Witness. Source Closure is retained, because §17's uniform creditor rule cites it |

## What this does not establish

Nothing here is Lean-checked, and `src/ri_core.py` is a reference model rather
than a proof: it decides the finite histories it is given, and D1/D2 are
decided over supplied finite samples, not over all response multisets. The
proofs in the specification are paper derivations. The independent adversarial
pass found three further local defects; it is not a completeness claim, and a
fourth may exist. The reconstruction of R2–R4 is inference from the rerun's
dependencies, and where the original repairs differed in form, only their
consequences are preserved here.
