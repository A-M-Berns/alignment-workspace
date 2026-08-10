# Theory 10: joint composition, and the repaired tightening

This part joins the two lines of the previous consolidation at the level of one
public process, and then repairs and tightens the movement accounting that the
joint result depends on. Every symbol used here is defined here.

## 1. Setting

Fix a finite **mechanism** with a challenger class, an authorized start,
consuming potential with initial value `Psi_0`, a latency gate, adequate
preassigned funding, and the closure conditions of the previous consolidation's
uniform finite-mechanism construction. The mechanism's **active book** is a
finite set of endorsements; a **book change** activates, deactivates, or
suspends endorsements. Each active book compiles to a **region** `S`, an
intersection of finitely many rational half-spaces inside the credal simplex
`P`, and the compiler selects a **reference** `q` in `S`.

The compiler carries a **core coefficient** `theta` in `(0,1]` with the
**fixed-core condition** `q + theta(P - q) subset S`. Quote selection has
errors summing to `E` over the run; the worldwise aggregate risk guard is `-R`;
ordinary adverse reference movement is limited by `M`.

Write `kappa = (1 - theta)/theta`.

## 2. The movement recursion

**Reference-jump movement.** {#NL-J1} **Status: PROVED (single derivation).**
One reference move from `q` to `q'` against holdings `H` charges adverse
movement equal to the nonnegative part of `-<H, q' - q>`.

**Proof.** Movement is charged only when it is adverse, so the charge is the
nonnegative part of the signed change in the value of the holdings under the
reference. Favourable movement charges nothing, which is the convention the
recursion below is stated against. `square`

**The uniform movement recursion.** {#NL-J2} **Status: PROVED (single
derivation).** Over at most `m` reference jumps, total adverse movement is
limited by `U_m`, where `U_0 = M` and

    U_{k+1} = (1 + kappa) U_k + E/theta + (kappa + 1) R .

**Proof.** At each jump the previous cap on worldwise gain is `E/theta +
kappa(R + U_k)` by the operative-force cap of the previous consolidation applied
to the prefix. A jump can convert that cap plus the risk guard into movement, so
the new total is at most `U_k` plus that quantity plus `R`, which rearranges to
the displayed recursion. Iterating from `U_0 = M` gives the bound at `m`.
`square`

**The wealth cap.** {#NL-J3-CAP} **Status: PROVED (single derivation).** With
the movement cap `U`, worldwise gain over every horizon is at most
`E/theta + kappa(R + U)`.

**Proof.** Substitution of the movement cap into the operative-force cap.
`square`

**Displayed constants.** {#NL-J2-N} **Status: MACHINE-CHECKED (stated finite
scope).** At `theta = 1/10`, `E = 1/100`, `R = 1/10`, `M = 1/5`: `kappa = 9`,
the additive term is `11/10`, and the caps are `U_0 = 1/5`, `U_1 = 31/10`,
`U_2 = 321/10`.

## 3. The tightening, and the fault it repairs

The recursion charges one jump per book change. Most book changes move nothing.
The tightening restates the cap over only the changes that can move the
reference — but *which* changes those are was got wrong once, and the error was
not conservative.

**Bare admission is not the certificate.** {#NL-N-J2A} **Status: NECESSITY
WITNESS.** A change admitting the incumbent reference can still cut its core,
forcing a nonzero jump. A retention test on bare admission is therefore
unsound: it certifies a zero charge where the real charge is nonzero, and it
undercounts the jumps, so the cap becomes breachable by chaining such changes.

**Witness.** One coordinate. Core coefficient `theta = 1/10`, incumbent
reference `q = 3/5`, base region `x >= 1/2`, and a change adding `x >= 3/5`. The
bare reference is admitted, since `3/5 >= 3/5`. But the core's lower end is
`q(1 - theta) = (3/5)(9/10) = 27/50`, and `27/50 < 3/5`, so the core is cut. A
compiler honouring the fixed-core condition must move to `q'` with
`q'(1 - theta) >= 3/5`, that is `q' >= (3/5)/(9/10) = 2/3`. At holdings `2` the
charged movement is `2(2/3 - 3/5) = 2/15`, which is not zero. `square`

**The correct retention test.** {#NL-J2P} **Status: PROVED (single
derivation).** A change under which the **whole core** of the pre-change
incumbent survives contributes exactly zero jump, and the core survives exactly
when every vertex of the shrunk simplex `q + theta(P - q)` satisfies the
post-change region. Hence the cap may be taken at `m*`, the number of
**core-invalidating** changes, with `m* <= Psi_0`.

**Proof.** The core is the convex hull of the shrunk vertices and the region is
an intersection of half-spaces, hence convex, so the region contains the core
exactly when it contains each shrunk vertex — a finite exact test. If the core
survives, the incumbent still satisfies the fixed-core condition after the
change, so a certificate-retaining compiler keeps the reference; then `q' = q`
and by `NL-J1` the charge is the nonnegative part of zero, which is zero.
Changes contributing zero may be dropped from the count in `NL-J2`, leaving
`m*`. Since every change is a book change and there are at most `Psi_0` of
those, `m* <= Psi_0`. `square`

**The separation is coefficient-relative.** {#NL-J2P-B} **Status:
MACHINE-CHECKED (stated finite scope).** Retention is a property of the change
*and the coefficient*, not a shape property of the change. On the fixture above,
the change retains at `theta = 1/10`, since the core `[27/50, 32/50]` lies inside
`x >= 1/2`, and invalidates at `theta = 1/2`, since the core's lower end is
`3/10 < 1/2`. The crossover is exact at `theta = 1/6`, where
`(3/5)(5/6) = 1/2` and the weak inequality still admits.

The correct separation is therefore **core-invalidating versus
constraint-adding**, replacing an earlier and unsound framing in terms of
point-exclusion.

**Expansion-stability.** {#NL-X6} **Status: PROVED (single derivation).** A
change that only removes constraints retains every core.

**Proof.** Removing constraints enlarges the region. A point in the smaller
region is in the larger one, so every shrunk vertex admitted before is admitted
after. `square`

**The count is against the incumbent in force.** {#NL-J2P-C}
**Status: PROVED (single derivation).** Each change must be judged against the
reference in force at that change, not against the initial reference.

**Proof.** Retention is a property of a change together with a reference, by
`NL-J2P-B`. Once the reference has moved, judging a later change against the
initial reference tests a condition about a reference that is no longer in
force, and the error runs in both directions: a change invalidating the initial
core may retain the current one, and conversely. So the trajectory must supply,
for each change, the reference in force before it. `square`

**The extensionality cost, made explicit.** The trajectory of
(change, reference-in-force) pairs is **read from public history**; this layer
invents no compiler policy and synthesizes no successor reference. That
dependence on public history is a cost the previous consolidation's provenance
result already concedes, and making it an input type is honesty about the cost
rather than payment of it.

## 4. The joint theorem

**Joint finite reason-governed process.** {#NL-J3} **Status: PROVED-CONDITIONAL
(conditions listed).** Assume: the mechanism and challenger hypotheses of §1;
the jointly serviceable terminal certificate; the market and mechanism
noninterference and account-assignment contracts; a computable rational compiler
with uniform core `theta > 0` on every activated endpoint; quote errors summing
to `E`; the worldwise risk guard `-R`; ordinary adverse movement at most `M`;
and the event order and refusal contract. Then a uniform finite-code transform
computes a joint public-history policy such that:

1. every operative endorsement occurrence has a reconstructible authorization
   and dependency lineage;
2. proposals and ontology outputs have no force before activation;
3. every persistent admissible expressible challenge receives a checked
   response, an authorized consuming repair, an authorized suspension or
   terminal failure, or the declared mechanism trigger;
4. every active-book change is recompiled, and its reference move has exactly
   one movement ledger entry;
5. the answerability projection satisfies the flow criterion and, under the
   stated terminal coverage, the terminal biconditional;
6. for every represented world and horizon, gain is at most
   `E/theta + kappa(R + U_{Psi_0})`;
7. the active book changes at most `Psi_0` times; and
8. no balance, market fact, quote, permitted geometry, or movement scalar
   creates normative authorization.

**Proof.** Construct the policy from the previous consolidation's finite
transition, inserting the compiler, reference and quote steps. Every new check
is a finite rational program or finite certificate check, so computability is
preserved. For answerability, erase market-only events: noninterference makes
them stutters and the filtered route certificate is authorized coverage for the
remainder, with flow guards, payments, queues, route consumption and
dispositions unchanged, so the inherited flow and terminal results apply. For
force, erase flow-only fields: proposal/activation separation gives identity
before activation, each activated state has the certified core, the quote
satisfies the required variational inequality, and the risk guard supplies `R`,
so the operative-force cap applies to every prefix; with at most `Psi_0`
reference jumps, `NL-J2` caps total movement by `U_{Psi_0}` and substitution
gives (6). Append-only constructors preserve every provenance path, and the
typed guards give (8) by inspection. `square`

**Uniformity.** The transform from finite encoded mechanism, compiler and
certificates to policy is uniform finite code. The cap is horizon-uniform and
uniform across runs sharing `theta, E, R, M, Psi_0`; it is **not** uniform
across a family in which those constants vary.

**With the tightening.** {#NL-J3-T} **Status: PROVED-CONDITIONAL (conditions
listed).** Under the hypotheses of `NL-J3` together with a recorded trajectory,
conclusion (6) holds with `U_{m*}` in place of `U_{Psi_0}`, where `m*` counts
core-invalidating changes.

**Proof.** By `NL-J2P` the retained changes contribute zero movement, so the
recursion may be iterated `m*` times rather than `Psi_0` times; substitution
into the cap gives the result. The improvement is strict exactly on a trajectory
containing at least one core-retaining change, and vanishes otherwise. `square`

## 5. Boundary

`NL-J3` alone does not justify a corollary about any particular engine. Such a
corollary needs every condition of the previous consolidation's bundle
separately supplied — and Theory 12 shows what that amounts to once the bundle
is compared with the interface: four of its conditions have no interface
counterpart and must be carried as the compiler contract.


## Transcribed rows: the source ledger's remaining claims

The rows below complete the consolidation's discard test for this layer. They
are **transcriptions**, carried folder-locally from the source tree's own claim
ledger during the completing pass: no new mathematics, no reinterpretation, and
no status change to any claim already stated above. Each carries its hypotheses,
its conclusion, and — for a drop-contract or necessity row — the witness the
source displayed, so the instance is readable here rather than only named.

Two conventions apply throughout this section. Where the source recorded a
status of a compound form, the status here is the plain mandated one and the
qualifier is carried in the ledger's verification column as provenance: the
mandated vocabulary of this package has no compound forms, and the qualifier
describes how the source established the claim rather than what its status is.
And where the source's verification pointer names a file of the source tree,
that pointer is recorded as historical provenance only — it is **not** evidence
a reader of this package can follow, and the folder-local evidence for a
transcribed row is the displayed witness itself.

**joint-certificate decidability.** {#NL-J0} **Status: PROVED (single derivation).** joint eventual route coverage is decidable and certified paths execute

*Hypotheses.* finite exact route graph; decidable authorization, address, account, consumption, and compiler checks

*Necessity / sharpness.* infinite/open route languages excluded; eventual route coverage load-bearing by NL-X9 Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**typed liability decomposition.** {#NL-J4} **Status: PROVED (single derivation).** no coordinate is debited twice; total equality iff componentwise equality

*Hypotheses.* typed direct-product ledger; unique `(event,kind,obligation)` key; one account per literal entry

*Necessity / sharpness.* NL-X10 shows identical-channel duplication; different obligations or risk types are not duplication

**exact two-date joint trace.** {#NL-E1} **Status: PROVED (single derivation).** every displayed rational equality and balance holds

*Hypotheses.* displayed binary book, accounts, challenge, service, suspension, references, and trades

*Witness.* smallest retained trace with all required event types; uniqueness minimality not claimed Source status was `PROVED+MACHINE-CHECKED`; the qualifier is provenance and is carried in the verification column.

**proposal-bypass witness.** {#NL-X1} **Status: NECESSITY WITNESS.** letting the proposal compile early changes quote `1/2` to `0`

*Hypotheses.* active `[1/2,1]`; unactivated removal proposal; sell demand

*Witness.* activation gate is load-bearing

**unrecorded-movement witness.** {#NL-X2} **Status: NECESSITY WITNESS.** omitted movement can hide liability `M`

*Hypotheses.* one move with `H=M,q^-=0,q^+=1`

*Witness.* recording is necessary; literal payment is not

**shared-reward-scalar obstruction.** {#NL-X3} **Status: PROVED (single derivation).** nonzero nonnegative challenge reward cannot be ordinary self-financing wealth

*Hypotheses.* faithful positive price or world-independent mint

*Witness.* typed external settlement escapes by being a different quantity Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**funding-to-authorization obstruction.** {#NL-X4} **Status: PROVED (single derivation).** solvency may gate release but cannot create authorization

*Hypotheses.* typed activation interface; equal authority records, unequal balances

*Witness.* an explicit balance-dependent governance rule is a different normative predicate Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**compiled-suspension witness.** {#NL-X5} **Status: NECESSITY WITNESS.** disposition and operative force disagree

*Hypotheses.* suspended endorsement remains in compiled set

*Witness.* recompile-on-activation is load-bearing

**pooled protected-trace witness.** {#NL-X7} **Status: NECESSITY WITNESS.** pooling changes procedure outcome exactly on `[1,5/4)`

*Hypotheses.* ordered world debit `1`; procedure debit `1/4`; adequate fenced comparison

*Witness.* pooling remains solvency-monotone; protected trace is the issue

**geometry-only repair obstruction.** {#NL-X8} **Status: PROVED (single derivation).** legitimate repair cannot factor through current geometry

*Hypotheses.* equal affine endorsements with different dependency IDs; one challenged

*Witness.* injective provenance geometry would escape Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**no-disposition obstruction.** {#NL-X9} **Status: NECESSITY WITNESS.** no authorization-respecting answerable-learner policy exists

*Hypotheses.* false persistent bound; no authorized respond, repair, suspend, or failure edge

*Witness.* adding one checked route removes this obstruction

**duplicate-channel witness.** {#NL-X10} **Status: NECESSITY WITNESS.** literal debit doubles from `r` to `2r`

*Hypotheses.* one charge semantic key entered twice

*Witness.* different typed risks are not duplicates

**market-priority interference witness.** {#NL-X11} **Status: NECESSITY WITNESS.** market-equivalent mechanism traces admit different challenges; repeated favoritism can defeat finite overtaking

*Hypotheses.* admission policy reads market sign; one service slot

*Witness.* a publicly modeled channel requires C-GP5 analysis

**reusable-crossing witness.** {#NL-X12} **Status: NECESSITY WITNESS.** bounded-inventory unbounded gain

*Hypotheses.* reusable two-state routes; alternating fixed-gap permitted regions

*Witness.* consuming potential or summable crossings escapes

**finite-change-only movement cap.** {#NL-X13} **Status: NECESSITY WITNESS.** one change has arbitrarily large adverse scalar

*Hypotheses.* one reference change; no common prefix payoff budgets

*Witness.* NL-J1 explains why the full joint hypotheses escape

**quote-before-activation witness.** {#NL-X14} **Status: NECESSITY WITNESS.** public book and operative region disagree for one date

*Hypotheses.* one book change and a quote made on the wrong side of it

*Witness.* atomic activation/compile before quote escapes

**late-account-assignment witness.** {#NL-X15} **Status: NECESSITY WITNESS.** identical admitted obligation can pay or trigger by retrospective assignment

*Hypotheses.* due charge `1/4`; candidate accounts with balances `0` and `1`; assignment after observation

*Witness.* stamping at admission escapes

**suspension-jump boundary.** {#NL-X16} **Status: PROVED (single derivation).** suspension can be zero-jump but is not automatically so

*Hypotheses.* authorized suspension; compiler either preserves or reselects reference

*Witness.* expansion-stable compiler is sufficient; NL-J2 handles reselection Source status was `PROVED+INDEPENDENTLY-REDERIVED`; the qualifier is provenance and is carried in the verification column.

**service-inadequacy witness.** {#NL-X17} **Status: NECESSITY WITNESS.** resource failure suspends a correct target before response

*Hypotheses.* true bound; response latency exceeds available service window

*Witness.* operational adequacy is load-bearing for the terminal bridge

**uncertified-compiler activation witness.** {#NL-X18} **Status: NECESSITY WITNESS.** activation leaves empty region and no quote/core

*Hypotheses.* exact contradictory endorsements `p>=3/4,p<=1/4` on `[0,1]`

*Witness.* preflight certificate or explicitly authorized relaxation escapes

## 6. What this part does not establish

The tightening tightens a cap and a count. It makes no behavioural,
convergence, or learning claim and changes what no policy does. Everything
verified numerically here is the one-coordinate fixture; the vertex formulation
is stated for general finite `P` but only the scalar case is exercised, so
higher-dimensional sharpness is open. No claim is made that the corrected
retention test is the weakest sound one: it is sufficient, and its necessity is
witnessed for the core condition itself by `NL-N-J2A`, not against alternative
formulations. The joint theorem does not discover correct warrants, validate an
initial book, define moral truth, solve open-ended language growth, or prove any
behavioural equilibrium.
