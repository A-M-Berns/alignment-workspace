# Joint finite reason-governed process

## 0. Authority and verdict

The frozen authority is the August 8 consolidation in `../consolidation_aug8/`.
Canonical identifiers below refer to that source.  In particular, this project
uses `C-OF1`, `C-OFSB`, `C-COMPILER`, `C-ACTIVATION`, `C-CONSUME`, `C-GP1`,
`C-GP2`, `C-GP3`, `C-GP5`, `C-PROV-IRR`, and `C-SCALAR-NOGO`.  No claim of the
consolidation is strengthened silently.

**Lead verdict.** A positive joint theorem is proved for a finite flow mechanism with
a jointly serviceable terminal repair certificate and a separated market
interface.  The theorem is uniform over runs sharing explicit numerical caps
and horizon-uniform within each such run.  It is not a complete Logical Induction
construction.

The central issue has a better resolution than a literal activation reserve.
Finitely many book changes do not, by themselves, cap

\[
[-\langle H_t,q_t-q_{t+1}\rangle]_+.
\]

But immediately before a reference jump, `C-OF1` caps every prefix payoff from
above and the risk contract bounds it from below.  The jump scalar is the
difference of the prefix payoff at the new and old references.  This yields a
recursive ex ante cap even when the norm of `H_t` is not bounded.  The cap is
proof accounting, not money.

## 1. Typed primitives

Let \(\Omega_t=\{w_1,\ldots,w_m\}\) be a nonempty finite represented-world set in
\(\mathbb R^d\), and let \(\Delta(\Omega_t)=\operatorname{conv}(\Omega_t)\).  A finite flow mechanism \(K\) has exactly the fields and named
challenger-class hypotheses of Part VI.  Its active warranted book is \(\mathcal E_t\); each
endorsement retains an occurrence identifier, dependency identifiers, source, scope,
authorization, status, and repair lineage.

The joint state immediately before date `t`'s mechanism cycle is

\[
Z_t=(h_t,\mathcal E_t,\mathcal C_t,q_t,p_{t-1},H_{t-1},\mathcal Q_t,F_t,\Gamma_t,\Lambda_t).
\]

The fields have the following types.

- `h_t` is an append-only sequence of typed public events.
- `\mathcal E_t` is the active book, not the proposal set.
- `\mathcal C_t\subseteq\Delta(\Omega_t)` is the compiled permitted region of `\mathcal E_t`.
- `q_t\in\Delta(\Omega_t)` is the public reference certified for `\mathcal C_t`.
- `p_{t-1}` is the last constrained quote; it is not an authorization field.
- `H_{t-1}=\sum_{s<t}x_s` is post-trade holdings through date `t-1`.
- `\mathcal Q_t` is the finite flow-mechanism challenge, queue, service, and repair state.
- `F_t` is a product of literal accounts.
- `\Gamma_t` stores active targets, route tokens, immutable burdens, account
  assignments, movement classification, and compiler certificates.
- `\Lambda_t` is a typed liability ledger.

### 1.1 Quantities that are not interchangeable

The account product contains at least:

\[
F_t=F_t^{wrld}\times F_t^{charge}\times F_t^{svc}\times
\prod_c F_t^{stake,c}.
\]

`F^wrld`, `F^charge`, and `F^svc` are literal currencies.  A stake account is
literal escrow: principal returned to a successful repair challenger is not
revenue.  A mechanism may combine `F^charge` and `F^svc` into the Part VI procedure
account, but this project keeps them typed and funds each assigned subaccount by
its `C-GP2` peak.

Ordinary self-financing settlement wealth is the world-indexed contingent
quantity

\[
G_N(w)=\sum_{t<N}\langle x_t,w-p_t\rangle.
\]

It is neither a flow balance nor challenge stake.  Locked capacity does not occur
in the primary flow model.  It appears only in comparisons with stock semantics.

Reference movement is the analytic quantity

\[
\ell_t=[-\langle H_t,q_t-q_{t+1}\rangle]_+.
\]

It is not a debit, receipt, collateral asset, or transfer.  An institution may add
literal revision collateral, but that is a new account with a declared recipient
and disposition; it does not replace `ell_t` in the wealth proof.

**No-conversion contract.** Guards that authorize an endorsement read authorization and
provenance fields, not any scalar balance.  Flow payment guards read only their
stamped literal account.  The quote solver reads \(\mathcal E,\mathcal C,q\) and market demand, not
flow balances.  The movement proof reads \(H,q\) and never credits a literal
account.  There is no constructor converting among these types.

## 2. Compiler and joint route certificate

A rational core-certified compiler is a total computable function on its declared
serviceable domain.  For a book \(\mathcal E\) it returns

\[
\operatorname{Comp}(\mathcal E)=(\mathcal C(\mathcal E),q(\mathcal E),\theta(\mathcal E),\chi_{\mathcal E})
\]

with rational-polytope \(\mathcal C(\mathcal E)\subseteq\Delta(\Omega_t)\), \(q(\mathcal E)\in\Delta(\Omega_t)\),
\(\theta(\mathcal E)\ge\theta>0\), and a checkable witness

\[
q(\mathcal E)+\theta(\mathcal E)(\Delta(\Omega_t)-q(\mathcal E))\subseteq \mathcal C(\mathcal E).
\]

The compiler does not relax an endorsement on its own.  `C-COMPILER` may be used to
construct a proposed explicit relaxation, but that relaxation becomes operative
only after the proposal, authorization, admission, and activation records exist.

A **jointly serviceable eventual-route certificate** augments the `C-GP3` eventual
route coverage certificate.  For every covered unresolved terminal key it supplies one
of:

1. a checked response that changes no active endorsement;
2. an authorized consuming repair path whose every active-book endpoint has a
   compiler certificate; or
3. an authorized consuming suspension/terminal-failure path that deactivates the
   target endorsement and has a compiler certificate.

Every edge names its charge, world, stake, and service accounts before the relevant
obligation arises.  An endpoint with no compiler certificate is not silently
activated.  Refusal leaves the previous certified book unchanged, but refusal may
not count as disposition of the challenged active endorsement. If no serviceable
route to respond, repair, or suspend exists, the missing-route obstruction `C-NO-ROUTE`
applies and the joint theorem does not claim success.

**Joint-certificate decidability.** {#NL-J0}
**Status: PROVED+INDEPENDENTLY-REDERIVED.** The certificate is finite and decidable
by the same graph enumeration as `C-REPAIR-CERT`, with one additional finite
compiler-witness check per endpoint.  A certified path is semantically executable
by induction over its finitely many checked edges.

## 3. Exact within-date transition

For `t>=0`, with initialization treated as a certified activation, the joint
policy performs this order.

1. Settle due ordinary market contracts into ordinary settlement wealth and due
   world-challenge contracts from their stamped world accounts.  A frozen-mechanism
   combined charge-plus-match obligation is one atomic debit, with component tags
   but no second debit.
2. Pay every remaining standing flow charge atomically, ordered by immutable
   challenge ID.  A charge component already included in step 1 is marked consumed
   and cannot reappear here.  Shortfall triggers before debit exactly as in Part
   VI.
3. Continue the already admitted serialized service or repair.  Charge literal
   service cost only to the preassigned service account.
4. Publish checked responses, proposals, address witnesses, or completed repair
   certificates.  Publication alone has no operative projection.
5. Apply the normative authorization predicate.  It reads routes, addresses,
   provenance, and burdens, not solvency or market outcomes.  Separately check
   feasibility: route tokens, assigned funding, and the preflight compiler
   certificate.
6. Atomically activate only a feasible authorized endpoint.  Otherwise append a
   refusal and continue the already authorized fallback route; an unresolved
   invalid endorsement is not relabeled complete.
7. Verify the activated book's compiler certificate and set `\mathcal C_{t+1}`.  Because
   verification preceded the atomic update, post-update compiler failure cannot
   leave a half-activated book.
8. Select `q_{t+1}`.  If the active book changed, classify the entire reference
   move as a reference jump and perform no ordinary reference evolution on that
   boundary.  If it did not change, classify the move as ordinary.  The basic
   constructed policy freezes `q` on unchanged books, so its ordinary movement is
   zero.
9. Append exactly one analytic movement entry for the classified move, using
   post-trade holdings `H_t`.  No literal account is debited.
10. Read the next rational market demand and solve the finite rational linear
    problem

    \[
    p_{t+1}\in\arg\max_{y\in \mathcal C_{t+1}}\langle x_{t+1},y\rangle.
    \]

    This is the exact variational inequality with `epsilon_{t+1}=0`.  Approximate
    solvers are allowed when their nonnegative errors have a declared summable
    cap.
11. Execute the demand only if its post-trade payoff remains at least `-R` in
    every represented world.  Otherwise execute the zero position and append the
    market refusal.  This finite guard establishes the aggregate risk
    invariant rather than assuming it.
12. Append all dispositions, compiler witnesses, solver witnesses, account
    changes, movement classifications, refusals, dependencies, and liabilities.

The reference move after trade `t` is therefore exactly the timing of `C-OFSB`:
`N` trades contain `N-1` internal moves.  Quote selection cannot precede
activation/compilation, and proposal publication cannot mutate `mathcal E,mathcal C,q,p`, or `H`.

The theorem uses a fixed finite coordinate language.  It does not perform fresh
coordinate discovery.  A predeclared finite coordinate extension may enter only
through the exact-preimage, onto-projection, zero-new-holdings, fixed-old-scope
interface of `C-CONS-EXT`; new-coordinate force still requires its own admission
and activation record.  Thus fresh coordinates cannot acquire force merely by
appearing in a proposal.

## 4. Projection contracts

### 4.1 Operative-force projection

Delete mechanism-only and literal-account fields and retain

\[
(\mathcal E_t,\mathcal C_t,q_t,p_t,H_t).
\]

For every executed date the projection has:

- a common core coefficient `theta>0` (shrink any larger certified core to
  `theta`);
- an exact or approximate variational inequality;
- accumulated error at most `bar_epsilon`;
- worldwise prefix payoff at least `-R`, established by the risk guard;
- post-trade holdings and the `q_t -> q_{t+1}` timing of `C-OFSB`;
- an exact partition of moves into ordinary dates and active-book-change dates.

Thus `C-OF1` applies.  `C-OF2` is unnecessary, though it remains available for a
nondecreasing variable-core refinement.  The stronger `C-MOVING-INTERFACE` does
not follow automatically; section 12 states its additional conditions.

### 4.2 Answerability projection

Delete market positions, quotes, solver events, and analytic movement entries.
Market refusal becomes a stutter.  The remaining trace is the `C-GP1` uniform
finite-flow policy on the route graph filtered by the joint compiler checker.
The jointly serviceable certificate is route coverage for that
filtered mechanism.

Market activity cannot alter admission, authorization, address predicates, route
availability, route tokens, account balances, paid/trigger comparisons, service
priority, or eventual route coverage.  This is syntactic noninterference: none of those
transition functions has a market argument.  If an implementation adds such an
argument, it is a different mechanism and must be analyzed with `C-GP5`; it is not
covered by the theorem.

Consequently the projection satisfies `C-GP1`.  Under eventual route coverage
hypothesis it also satisfies the `C-GP3` biconditional.  Fencing is
used for protected-trace conservativity, not because pooling is necessary for
solvency; `C-GP6A` still says pooling weakly helps aggregate solvency.

### 4.3 Provenance projection

Every noninitial operative endorsement occurrence has the stored path

\[
\text{evidence/challenge}\to\text{proposal}\to\text{authorization}
\to\text{admission}\to\text{activation}\to\text{compiled endorsement occurrence}.
\]

Suspension appends an inactive status without deleting that path.  Compiler input
is the multiset of active endorsement occurrences, not a geometry quotient.  Equal endorsements
retain distinct dependency identifiers, as required by `C-PROV-IRR`.

## 5. Reference-jump movement lemma

For a prefix ending immediately after trade `t`, define its affine payoff at any
\(z\in\Delta(\Omega_t)\) by

\[
\Phi_t(z)=\sum_{s\le t}\langle x_s,z-p_s\rangle.
\]

Then

\[
\Phi_t(q^+)-\Phi_t(q^-)=\langle H_t,q^+-q^-\rangle
=-\langle H_t,q^--q^+\rangle. \tag{5.1}
\]

**Reference-jump payoff-range lemma.** {#NL-J1}
**Status: PROVED+MACHINE-CHECKED.** Suppose every represented-world prefix payoff
is at least \(-R\), and before the current reference move `C-OF1` gives
\(\Phi_t(w)\le L_t\) for every \(w\in\Delta(\Omega_t)\).  For any old and new references
\(q^-,q^+\in\Delta(\Omega_t)\),

\[
[-\langle H_t,q^--q^+\rangle]_+\le L_t+R,
\qquad
|\langle H_t,q^--q^+\rangle|\le L_t+R. \tag{5.2}
\]

**Proof.** Convex averaging extends the worldwise lower bound to every point of
\(\Delta(\Omega_t)\), so both \(\Phi_t(q^-)\) and \(\Phi_t(q^+)\) are at least \(-R\). Both are at most
\(L_t\) by `C-OF1`. Equation (5.1) is their difference. Its positive part and
absolute value are at most the width \(L_t-(-R)=L_t+R\). The scalar range argument
is machine-checked in `lean/Joint.lean`. `square`

This lemma explains why raw holdings norm is the wrong quantity.  `H_t` can be
large in coordinates to which the two references are nearly insensitive; only
the realized payoff difference matters.

## 6. Finite-jump recursion

Let

\[
\kappa=\frac{1-\theta}{\theta},\qquad
A=\frac{\overline\varepsilon}{\theta}+(\kappa+1)R=\frac{\overline\varepsilon+R}{\theta}.
\]

Assume ordinary (non-book-change) adverse movement has total at most `M_ord`.
Define

\[
U_0=M_{ord},\qquad U_{j+1}=(1+\kappa)U_j+A
=\theta^{-1}U_j+\frac{\overline\varepsilon+R}{\theta}. \tag{6.1}
\]

Equivalently,

\[
U_m=\theta^{-m}M_{ord}+
\frac{\overline\varepsilon+R}{\theta}\sum_{i=0}^{m-1}\theta^{-i}. \tag{6.2}
\]

**Finite reference jump cap.** {#NL-J2}
**Status: PROVED+MACHINE-CHECKED.** If at most `m` active-book changes occur,
the total adverse movement is at most `U_m`.

**Proof.** Before jump `j`, let `D` be all accounted movement so far.  `C-OF1`
gives

\[
L_t\le \overline\varepsilon/\theta+\kappa(R+D).
\]

By `NL-J1`, the new jump is at most

\[
L_t+R\le A+\kappa D.
\]

Let `V_j` be all reference jumps through `j` plus the entire ordinary budget
`M_ord`, including ordinary movement not yet realized.  Then `D<=V_j` and

\[
V_{j+1}\le V_j+A+\kappa V_j=(1+\kappa)V_j+A.
\]

Induction gives (6.1), and finite geometric summation gives (6.2).  The recurrence
induction is machine-checked in `lean/Joint.lean`. `square`

If ordinary **absolute** movement has the same cap, the absolute version of
`NL-J1` gives the same recursion for total absolute movement.

Finiteness of book changes alone is not enough: with one formal move,
`H=M,q^-=0,q^+=1`, the liability is `M`.  The uniform result uses the inherited
risk, core, error, and prior-movement caps to rule out an unbounded payoff
difference at the moment of the jump.

## 7. Joint finite reason-governed process theorem

**Joint theorem.** {#NL-J3} **Status: PROVED (single derivation).** Fix a finite
flow mechanism `K` and challenger class satisfying the hypotheses of `C-GP1`: an
authorized start, consuming potential `Psi` with `\Psi_0=Psi(K_0)`, latency gate,
adequate preassigned funding, and pure-run, persistent-filer, settlement-test,
and coalition closure; add the ecology hypotheses exactly where `C-GP1` adds
them.  Assume:

1. the jointly serviceable terminal certificate of section 2;
2. the market/mechanism noninterference and account-assignment contracts of sections
   1 and 4;
3. a computable rational compiler with uniform core `theta>0` on every activated
   endpoint;
4. constrained quote errors summing to `\overline\varepsilon<infinity` (the constructed exact LP
   has `\overline\varepsilon=0`);
5. the worldwise aggregate risk guard `G_n(w_i)>=-R`;
6. ordinary adverse reference movement at most `M_{ord}<infinity` (the constructed
   frozen-on-book policy has `M_{ord}=0`); and
7. the event order and refusal contract of section 3.

Then a uniform finite-code transform computes a joint public-history policy such
that:

1. every operative endorsement occurrence has a reconstructible authorization and
   dependency lineage;
2. proposals and ontology outputs have no force before activation;
3. every persistent admissible expressible challenge receives a checked response,
   authorized consuming repair, authorized suspension/terminal failure, or the
   declared mechanism trigger;
4. every active-book change is recompiled, and its reference move has exactly one
   reference jump ledger entry;
5. the answerability projection satisfies `C-GP1` and, under the stated terminal
   coverage, `C-GP3`;
6. for every represented world and every horizon,

   \[
   G_N(w)\le \frac{\overline\varepsilon}{\theta}
   +\kappa\bigl(R+U_{\Psi_0}\bigr); \tag{7.1}
   \]

7. the active book changes at most `Psi0` times; and
8. no balance, market fact, quote, permitted geometry, or movement scalar creates
   normative authorization.

**Proof.** Construct the policy by taking the `C-GP1` finite transition and
inserting the compiler/reference/quote steps in section 3.  All new checks are
finite rational LP or finite certificate checks, so computability is preserved.

For answerability, erase market-only events.  Noninterference makes them stutters,
and the filtered joint route certificate is authorized coverage for the remaining
mechanism.  All flow guards, payments, queues, route consumption, and dispositions
are unchanged.  `C-GP1` therefore gives terminal flow learning and at most `Psi0`
book changes; `C-GP3` gives the terminal-coverage biconditional.

For force, erase flow-only fields.  Proposal/activation separation (`C-ACTIVATION`)
gives identity before activation.  Each activated state has the certified core,
the quote has the required variational inequality, the risk guard supplies
`R`, and step 9 has the timing of `C-OFSB`.  Thus `C-OF1` applies to every prefix.
There are at most `Psi0` reference jumps, so `NL-J2` caps total movement by
`U_{\Psi_0}`.  Substitution in `C-OF1` proves (7.1).

The append-only event constructors preserve every provenance path.  Typed guards
prove the no-conversion clause by inspection.  These arguments establish all
eight conclusions. `square`

### Uniformity statement

The transform from finite encoded `K`, compiler, and certificates to policy is
uniform finite code.  `C-GP1`/`C-GP3` remain challenger-class-relative and their
terminal claims are run-relative in the exact sense inherited from Part VI.  The
wealth cap (7.1) is horizon-uniform and uniform across all runs sharing
\(\theta,\overline\varepsilon,R,M_{\rm ord},\Psi_0\); it is not uniform across a family in which those constants
vary.

## 8. Smallest exact joint trace

Take binary represented worlds \(\Omega_t=\{0,1\}\), so \(\Delta(\Omega_t)=[0,1]\).

At date 0 the active book contains one sourced endorsement `rho: p>=1/2` with dependency
identifier `dep:rho`. Its region is \(\mathcal C_0=[1/2,1]\), reference \(q_0=1\), and common
core \(\theta=1/2\).  Sell demand \(x_0=-1\) gives the exact constrained quote
`p_0=1/2`.  Holdings are `H_0=-1`; prefix payoffs are

\[
G_1(0)=1/2,\qquad G_1(1)=-1/2.
\]

The date-0 history admits repair-only challenge `c` with stake `1/2`, assigns its
charge account holding `1/4`, and assigns its service account holding `1/8`.  The
stake margin holds because `1/2>1/4`.

At date 1 the charge account atomically pays `1/4`; the service account pays the
separate checking cost `1/8`.  A checked certificate proposes suspension of
`rho`; the authorized consuming route activates it.  The stake principal `1/2`
is returned. The book becomes empty and compiles to \(\mathcal C_1=[0,1]\) with canonical
reference \(q_1=1/2\).  The reference movement is

\[
[-H_0(q_0-q_1)]_+=[-(-1)(1/2)]_+=1/2.
\]

Buy demand `x_1=1` gives `p_1=1`, leaving `H_1=0`.  Total ordinary market payoff
is `-1/2` in both worlds.  The literal charge balance and service balance both end
at zero; stake return has zero profit component; analytic movement is `1/2` and
debits no account.

**Exact joint trace claim.** {#NL-E1}
**Status: PROVED+MACHINE-CHECKED.** The displayed trace satisfies every stated
region, core, quote, holdings, payoff, flow, stake, service, and movement equality.

For `theta=1/2,\overline\varepsilon=0,R=1/2,M_{ord}=0,\Psi_0=1`, recursion (6.1) gives `U_1=1` and
the uniform wealth cap is `3/2`.  The actual `C-OF1` cap using `D=1/2` is `1`,
and the realized payoff is `-1/2`.  All numbers are recomputed in
`tests/test_joint.py`.

## 9. Formal no-double-charging rule

Let liability kinds be

\[
\mathsf K=\{\mathsf{market},\mathsf{charge},\mathsf{stake},
\mathsf{service},\mathsf{movement}\}.
\]

The ledger is a partial function from `(event ID, kind, obligation ID)` to one
typed entry.  Literal entries additionally name exactly one account.  The key
uniqueness invariant forbids two entries with the same event, kind, and obligation
ID.  Movement entries have no literal account.

**Typed liability decomposition.** {#NL-J4}
**Status: PROVED (single derivation).** Under key uniqueness, the accounting of a
finite event set is the direct-product sum of five projections.  No component is
debited twice, and equality of the total typed record is equivalent to equality
in every component.

**Proof.** The ledger codomain is the direct product of the five free rational
modules generated by their typed obligation IDs.  Key uniqueness gives each
basis coefficient at most one originating entry.  Addition in a direct product
is coordinatewise, and equality is coordinatewise. `square`

This does not prohibit one physical episode from creating different risks.  An
unresolved challenge may create charge; checking it may consume service; changing
the compiler reference may create analytic movement; and a false world bound may
create a world-contract loss.  Those are four different coordinates.  Calling
them “double charging” would be incorrect.  Duplication occurs only when the same
semantic obligation ID is debited twice in the same coordinate.

Ordinary market payoff is charged once through its settlement contract.  If a
world challenge is a distinct contract, its loss is distinct.  If an
implementation reuses the market contract ID as the challenge contract ID, the
uniqueness checker rejects the second debit.

## 10. Drop-contract and unsafe-order witnesses

Each item either supplies a finite witness, cites a decisive frozen witness, or
records that the proposed necessity is false.

1. **Proposal-bypass witness.** {#NL-X1} **Status: REFUTED (witness displayed).**
   With active `S=[1/2,1]` and sell
   demand `x=-1`, the exact quote is `1/2`.  Illicitly compiling the unactivated
   removal proposal gives `[0,1]` and quote `0`.  This violates
   `C-ACTIVATION` and changes market payoff before authorization.

2. **Unrecorded-movement witness.** {#NL-X2} **Status: REFUTED (witness displayed).**
   A single state with
   `H=M,q^-=0,q^+=1` has adverse scalar `M`.  Omitting the entry deletes an
   arbitrarily large term from `C-OFSB`/`C-OF1`.  Literal payment is not required;
   analytic recording is.

3. **Shared-reward-scalar obstruction.** {#NL-X3}
   **Status: PROVED+INDEPENDENTLY-REDERIVED.** `C-SCALAR-NOGO`
   proves that a nonzero all-world reward cannot be both ordinary self-financing
   wealth and nonnegative in every world under a faithful positive price.

4. **Funding-to-authorization obstruction.** {#NL-X4}
   **Status: PROVED+INDEPENDENTLY-REDERIVED.** Two records with identical route
   authority but balances `0` and `1` have the same normative authorization.
   Solvency can gate service release, not create the authorization constructor;
   this is `C-SOLV-AUTH`.

5. **Compiled-suspension witness.** {#NL-X5}
   **Status: REFUTED (witness displayed).** Suspending `p>=1/2` while retaining
   `S=[1/2,1]` makes sell demand quote `1/2`; the correct empty book compiles to
   `[0,1]` and quote `0`.  The disposition and operative projection disagree.

6. **Expansion-stable suspension.** {#NL-X6}
   **Status: PROVED+MACHINE-CHECKED.** The
   proposed universal danger is false.  Removing `p>=1/2` expands
   `[1/2,1]` to `[0,1]`; keeping `q=1` preserves the old `1/2`-core and creates
   zero movement at every holdings vector.  Therefore “reference must change” is not a
   theorem.  The actual contract is: recompile the region and record movement
   exactly once if the reference changes.

7. **Pooled protected-trace witness.** {#NL-X7}
   **Status: REFUTED (witness displayed).** With world debit `1`, procedure
   debit `1/4`, and pooled balance in `[1,5/4)`, the first debit succeeds and the
   protected procedure debit triggers, while the fenced comparison pays it.
   This is `C-CROSS-EFFECT`/`C-GN3`.

8. **Geometry-only repair obstruction.** {#NL-X8}
   **Status: PROVED+INDEPENDENTLY-REDERIVED.** Duplicate one
   affine endorsement under dependency IDs `d_1,d_2` and challenge only one.  Geometry is
   equal but the required removal differs.  This is exactly `C-PROV-IRR`.

9. **No-disposition obstruction.** {#NL-X9}
   **Status: REFUTED (witness displayed).** A false persistent
   active endorsement with no authorized response or deactivation edge cannot both remain
   authorized and meet terminal answerability.  This is `C-NO-ROUTE`.

10. **Duplicate-channel witness.** {#NL-X10}
    **Status: REFUTED (witness displayed).** A charge obligation
    `r=1/4` recorded twice under the same semantic key debits `1/2` instead of
    `1/4`.  The key-uniqueness invariant rejects the second entry.

11. **Market-priority interference witness.** {#NL-X11}
    **Status: REFUTED (witness displayed).** Let one service slot
    choose challenge `a` when the last market demand is nonnegative and `b`
    otherwise.  Histories equal on every mechanism field but with demands `1` and
    `-1` admit different targets.  Repeated favored later filings can also destroy
    finite overtaking.  Thus market/mechanism noninterference is load-bearing.

12. **Reusable-crossing witness.** {#NL-X12}
    **Status: REFUTED (witness displayed).** Drop route
    consumption and use the reusable two-state repair cycle of `C-REVISION-CYCLE`,
    compiling alternately to `[0,1/3]` and `[2/3,1]`.  Persistent challenges force
    fixed-gap crossings, and `C-MOVE-OBS` supplies bounded-inventory unbounded
    gain.  Consuming potential, or another summable-crossing condition, is
    necessary.

13. **Finite-change-only movement cap.** {#NL-X13}
    **Status: REFUTED (witness displayed).** The raw one-change family in
    item 2 has no uniform movement cap.  It does not refute `NL-J3`, because it
    omits the common prefix risk/upper-payoff caps. Under those conditions,
    `NL-J1` caps the scalar even if `||H||` is large. Hence an
    holdings-dependent activation certificate is sufficient but not necessary.

14. **Quote-before-activation witness.** {#NL-X14}
    **Status: REFUTED (witness displayed).** In item 1 the old quote is used for
    a trade after the endorsement is officially removed, or the proposed quote is used
    before removal.  Either ordering gives one date on which public book and
    operative region disagree.

15. **Late-account-assignment witness.** {#NL-X15}
    **Status: REFUTED (witness displayed).** If a due `1/4` charge can
    be assigned after balances `0` and `1` are observed, the same admitted
    challenge has either a trigger or a payment.  Stamping the account at
    admission removes this retrospective choice, as required by Part VI.

16. **Suspension-jump boundary.** {#NL-X16}
    **Status: PROVED+INDEPENDENTLY-REDERIVED.** It is safe with an
    expansion-stable compiler that retains the old reference.  A compiler that
    gratuitously changes the reference can create a jump, as the exact trace in
    section 8 does.  Suspension is therefore a serviceable fallback, not a
    zero-movement theorem; its jump is handled by `NL-J2`.

17. **Service-inadequacy witness.** {#NL-X17}
    **Status: REFUTED (witness displayed).** Drop the latency/capacity adequacy
    gate in the `C-BRIDGE-FAIL` true-bound instance.  Required lock/resource use
    reaches its trigger at effective age two before the correct response at age
    five, so a true endorsement is suspended for resource failure.  The joint process
    must record that suspension explicitly and cannot call it evidential repair.

18. **Uncertified-compiler activation witness.** {#NL-X18}
    **Status: REFUTED (witness displayed).** Activate exact endorsements \(p\ge3/4\) and
    \(p\le1/4\) on \(\Delta(\Omega_t)=[0,1]\).  Their exact permitted region is empty, so no quote or
    positive core exists.  Preflight certification blocks activation.  A
    `C-COMPILER` relaxation can restore serviceability only as a public proposed
    repair followed by authorization; silent compiler weakening is not an escape.

## 11. Hypothesis audit

- Joint eventual route coverage is load-bearing by `C-NO-ROUTE`; coverage of unused or
  transient states is not required by `C-GN4`.
- Consuming potential or another finite/summable crossing condition is
  load-bearing by item 12.
- The uniform positive core, risk, summable solver error, and movement
  timing are the inherited load-bearing conditions of `C-OF1` and its moving
  obstruction.
- \(q^-,q^+\in\Delta(\Omega_t)\) is load-bearing for `NL-J1`; outside \(\Delta(\Omega_t)\), convex worldwise payoff
  caps do not apply.
- A cap on ordinary reference movement is load-bearing unless the construction
  freezes references between book changes.  The retained construction does so.
- Market/mechanism noninterference is load-bearing by item 11.  Restricted transfers
  may instead be admitted only under the exact `C-GP5` protected-trace condition.
- Account fencing is not necessary for total solvency (`C-GP6A`), but zero
  cross-component influence is necessary for the all-balance, record-seam-rich
  protected-trace theorem (`C-GP5`).
- A literal movement reserve is not necessary.  If adopted as policy, its funding,
  beneficiary, and failure branch are additional primitives and its balance may
  not authorize an endorsement.
- Exact LP quote selection is sufficient, not necessary; any solver satisfying
  the inherited variational inequality and summable-error contract works.
- Whether the recursive cap can be improved uniformly using favorable movement
  netting is open.  `C-MOVE-MIN` establishes only local no-netting minimality.
- The exact jointly serviceable coverage formulation is sufficient.  Some form of
  terminal disposition coverage is necessary by NL-X9, but necessity of this
  particular edge-by-edge compiler-certificate presentation is open.

## 12. Logical Induction boundary

`NL-J3` alone does not justify a Logical Induction corollary.  Such a corollary is
available only if every condition of `C-MOVING-INTERFACE` is separately supplied:
a computable deductive process, rational compact cylinders, effective
finite-algebra witness extension to fresh sentences, a fixed positive core,
rational prefix-causal clock integration, aggregate risk limit `-2`, a constrained
solver, and the declared aggregate-trader dominance property.

In addition, use the **absolute** form of the present recursion: assume ordinary
absolute movement has a computable summable schedule, and assign each of the at
most `Psi0` reference jumps its computable `NL-J1` majorant.  Then their combined
sum supplies the `D_*` required by `C-MOVING-INTERFACE`.  Under all those inherited
conditions its stated nonexploitation conclusion follows.  This project does not
construct the recursive constrained history, witness-extension compiler, or clock
proof that the consolidation leaves conditional.

## 13. Interpretation boundary

The theorem joins the two mathematical lines at the level of one public process:
represented active reasons constrain quotes, and persistent admissible challenges
can respond, repair, or suspend those reasons without losing the worldwise
wealth cap.  It does not discover correct warrants, validate the initial book,
define moral truth, solve open-ended language growth, establish unrestricted
reflective integrity, or prove a behavioral incentive equilibrium.
