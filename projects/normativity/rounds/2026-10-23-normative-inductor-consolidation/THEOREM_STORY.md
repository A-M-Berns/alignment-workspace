# The warrant Normative Inductor

A mathematical account of one construction, written to be read without the repository.
Every named object is a Lean declaration under `lean/Workspace/Normativity/Contrib/`. This
supersedes the integration round's account
(`../2026-10-22-normative-inductor-integration/THEOREM_STORY.md`) in §B (entitlement), §C (the
compile outcome), §E (two scenarios) and §G (one interface, two realizations).

## A. The problem

A logical inductor is a market: a sequence of price vectors over sentences, produced by a
market maker who clears the trades of a fixed firm of traders, with the guarantee that no
efficiently computable trader makes unbounded money against it. Its prices converge to
something probability-like on every sentence a deductive process eventually settles. It has
no normative content: nothing in it answers to an obligation.

The question is whether such a reasoner can be made to **answer to revisable normative
commitments** — commitments entered as warrants, challenged, undercut, rebutted, retired — at
a quantitative rate, without losing the guarantee that made it a logical inductor, and whether
the resulting prices can be made to bear on what the reasoner **does**.

Three things could go wrong. The commitments could be ignored (no force). Their enforcement
could bankrupt the market maker's guarantee (unbounded liability destroys the exploitation
criterion). Or the prices could conform while the actions do not (credal conformance is not
practical adequacy). The construction addresses all three, and the theorem says exactly which
parts are proved and which are inputs.

## B. The normative state

**Warrants.** A warrant occurrence is a typed leverage form with an identity, a citation, a
source and a defeat set (`Occurrence`): a *premise* `P(X) ≥ c`, an *applicability*
`P(X∧A) ≥ c·P(X)` citing the premise it conditions on, or a *strength* `P(X∧A∧Y) ≥ c·P(X∧A)`
citing the applicability. Each compiles to one linear row on the fragment's coordinates
(`Form.row`).

**Revision.** The docket records *defeat* of ports; the settlement records which coordinates
are *pinned* true or false. Settlement acts on a form by its shape (`settleOutcome`): a premise
on a pinned-false sentence is **retired**, a conditional form whose antecedent is pinned false
is **vacuous**, one whose consequent is pinned false is **rebutted** — a defeasible warrant does
not contrapose, so its row leaves rather than pinning its antecedent.

**The survivors** (`Grounds.survivors`). An occurrence is active when the docket does not
undercut it (neither its own port nor a port of its defeat set is defeated), the settlement
keeps its form, and the occurrence it cites is itself active. The active identities are the
least fixed point of this step from the empty set (`activeIds_fixed`, `mem_survivors`).
Undercut, retirement, vacuity and rebuttal propagate along citation chains of every length;
a citation that resolves to nothing, or a cycle, is inactive. Survivors only leave under more
settlement (`survivors_anti`) and under more defeat (`survivors_anti_docket`).

**The state and its bundle** (`NormState`, `.bundle`). The normative state is the record state
— grounds, docket, settlement, the events the record authorizes — with the structural rows
(coherence relations such as `X∧A ≤ X`). Its bundle is the survivors' rows, specialized by the
settlement, together with the live structural rows and the settlement's pins, each row cited
by what produced it. Four views read this one bundle: the **joint region** `K_t` of price
vectors satisfying every row (`region`); the **licence**, which checks a verdict's certificate
against the cited rows (`SupportedOn`); the **elimination**, which computes each coordinate's
forced interval by Fourier–Motzkin (`interval`); and the **enforcer's rows**.

**Four authorities, kept apart.** *Provenance* (`Origin`) says which exposed obligation
occurrence of the accounted state a warrant occurrence realizes. *Entitlement*
(`Entitlement`) says what admits its constraint to the market: the originating obligation is
admitted by the protocol at the boundary's history, its account still carries a live leaf — an
obligation already answered or closed entitles no standing constraint — and the form expresses
the obligation's anchored requirement under a declared relation `Expresses`. *Verdict
licensing* (`Licensed`) says what authorizes a certificate-backed selection of a verdict: a
certificate supported on the bundle and an event the record authorizes. *Operative
enforcement* says what makes an entitled constraint act: survival under the docket and the
settlement, and a compiled bundle. The enforcer consumes no licence and a licence introduces
no constraint; the theorem joining entitlement to enforcement is that every enforced
substantive row is an entitled survivor's. Entitlement is a typed input with its semantics
stated — the protocol's `Admitted` and the application's `Expresses` are not derived — and
what it does take from the account is checkable: the fates of the origin's leaves.

**Licence.** A verdict is a value for a coordinate. A verdict certificate is a pair of bound
certificates — nonnegative multipliers on rows summing to `±e_φ` — each row cited by
occurrence, with the two attained endpoints. *Supported*: every positively weighted row is a
survivor's row under that occurrence's citation, a pin, or a cube face; the endpoints bracket
the verdict and are attained in the region. *Licensed*: supported, and the issuing event
authorized. Licensed implies supported implies admissible (`licence_chain`), and neither
converse holds (`Countermodel`).

## C. Enforcement

**The compile and its outcome.** A date's compile result is the compiler's (`CompileResult`:
a witness, a Farkas conflict certificate, or nothing). The outcome (`outcome`) is *idle* when
the state has no rows, *enforced* when the witness checks into the region, *withheld*
otherwise, carrying the result. The obligations present are the state's bundle in every case
(`outcome_obligations`): withholding force extinguishes nothing, and the survivors and the
accounted state are untouched. A valid conflict certificate refutes the region
(`conflict_region_empty`), which separates an infeasible system from an unchecked witness and
from no result. A withheld date trades nothing (`day_value_eq_zero_of_bundle_nil`), so the
liability bound and Logical Induction are unaffected by withholding; a service whose date is
not enforced, or whose certificates are not supplied, is dropped from the protocol's services
and its transport mass moves into the residual (`residual_restrict`), where the Progress bound
charges it at the worst loss.

**The trader.** The force layer's trader holds, on each row `⟨a, P⟩ ≥ b`, a position
proportional to the row's violation at the day's displayed price, at a declared intensity
(`enforcementStrategy`). Its value against a world is the units-weighted signed gaps plus the
intensity-weighted squared violations (`Account.day_value_eq`).

**The schedule and the market** (`WarrantSchedule`, `.enforcer`, `.market`). A fragment map
`ι` prices coordinate `j` as the sentence `ι j`; each date carries the rows its outcome holds
(`compileAt`) and a tolerance `tol_n`. The enforcer is effective data: on date `n`, against
the ordinary aggregate's trade list `ord`, it holds the held rows at the **calibrated
intensity** `κ_n = (ε_n + A(ord))/tol_n²`, where `ε_n` is the market maker's own slack and
`A(ord)` the ordinary aggregate's syntactic bound. The augmented market is the deductive
process's source firm priced together with this enforcer.

**Affordability** (`OddsBankroll`). An *account* is a trader of this shape on a history with
rational quotes, assessed at a family of live worlds, whose cumulative value at a live world
is below a cap. The augmented market is an account with cap `3` — the market maker's constant
`1` plus the source firm's floor `2`. **The odds bankroll**: if at date `n` a live world `v'`
clears every enforced row of every date `t ≤ n` with a surplus dominating, by the factor `ρ`,
the deficit of the assessed world on that row, the enforcer's net worth there is at least
`−3ρ`. **Across one reopening** — a slack world `v₀` before date `m`, a slack world `v'` from
`m` on — it is at least `−3ρ(2+ρ)`. Intensity, tolerance and the number of rows and dates do
not appear. For a warrant of strengths `c`, the natural `ρ` is the largest odds `c/(1−c)`.

**Preservation.** With a liability bound and the enforcer effective, the augmented market is
a logical inductor over the deductive process in the source's original sense
(`WarrantSchedule.isLogicalInductor`): the computability of the market is supplied by the
compiled bounded evaluator (`EnforcedCompiler`), given that the trade map is primitive
recursive — which it is whenever the bundle schedule runs through finitely many phases
(`WarrantSchedule.computation`).

**Conformance** (`rowViolation_le_tol`, `excess_le_tol`). At every enforced date, every held
row has violation at most `tol_n` at the displayed price. The proof is the force layer's
inequality `Σ_i κ_n g_i² ≤ ε_n + A_n`, whose two right-hand terms are discharged at the real
market: the slack by the market maker's contract at every cube point
(`marketMaker_day_value_le_cube`), the volume by the ordinary aggregate's syntactic bound
(`Strategy.abs_value_le`); the calibrated intensity is exactly what turns this into
`g_i ≤ tol_n`. This is rowwise conformance, not distance to the region.

**Transport** (`FunctionalCert.le_of_excess`, `BoundCert.transport`, `bracket_at_market`).
A certificate — nonnegative multipliers `m_i` on rows whose normals sum to a functional `ℓ` —
carries rowwise conformance to the functional: at any price where every positively weighted
row's excess is at most `δ`, `ℓ·p ≤ Σ m_i b_i + (Σ m_i)·δ`. The multiplier sum is the
certificate's **mass**, the Lipschitz constant of the certified bound in the rows' excesses.
Hence a supported verdict's bracket holds at the displayed price, widened by `mass · tol_n` on
each side, and an adapter's certified score bounds hold there too.

## D. The main theorem

`WarrantInductor.warrant_inductor`; the statement in paper form, with the assumption ledger,
is `THEOREM.md`. In short: for an externally supplied state process, a fragment map, the
compiler's results and tolerances — given an entitlement of every date's grounds, well-formed
grounds, a computable deductive process and an effective enforcer, a liability bound, and an
adapter protocol whose service dates are enforced and carry certified exclusion and margins
with declared adequacy semantics and constants — the augmented market is a logical inductor;
at every enforced date every row of the state's bundle has excess at most the tolerance at the
displayed price, and every held substantive row is an entitled survivor's; the adapter's
inadequate mass is at most `κ` times the displayed inadequate excess, itself at most the
certificates' mass times the tolerance; and the Progress bound holds with its uptake package
derived.

The theorem is pointwise in the date. Nothing in it says how one normative state follows
another; that is the revision process's, and the two scenarios below are two such processes.

## E. Two scenarios

Both run on five sentences `X, X∧A, X∧A∧Y, Y, Z`, a principal warrant `P(X) ≥ 4/5`,
`P(X∧A) ≥ 3/4·P(X)`, `P(X∧A∧Y) ≥ 2/3·P(X∧A)` (each form citing the one before), an
independent warrant `P(Z) ≥ 3/4`, three coherence rows, tolerance `1/400`, `X` settled true
at date 3 and `Y` (with `X∧A∧Y`) refuted at date 8. Both discharge computability and
liability: the deductive stage is a step function, the bundle runs through finitely many
phases, and the bankroll across the reopening is `−72 = −3·4·(2+4)` with the all-true world
slack before the refutation and the world `X, A, Z` true, `Y` false after it. Both are entitled
in an accounted state with two live obligations; in the state where the first obligation is
already answered, no entitlement may trace a warrant to it (`answered_not_entitled`).

**Scenario A — the undercut** (`WarrantInductorWitness`). The applicability's port is defeated
at date 5. The strength leaves with the applicability it cites — at the undercut, not at the
later refutation (`survivors_eq`). The region loses the lower bounds `P(X∧A) ≥ 3/4` and
`P(X∧A∧Y) ≥ 1/2` it carried at date 4 and keeps `P(Z) ≥ 3/4` (`undercut_summary`). At date 4
the adapter's question is *act on the warrant's conclusion or refrain*, scored by `P(X∧A∧Y)` and
`P(X∧A) − P(X∧A∧Y)`; the strength row and a cube face certify the refraining score at most
`1/3`, the strength and applicability rows certify the acting score at least `1/2 − (5/3)/400`;
the gate puts mass at most `1/25` on refraining. At date 9 the question is *act on `Z` or
refrain*; mass at most `1/100` on refraining. After the revision the region no longer excludes
refraining on the principal matter (`exclusion_lapses`): the certified guidance there is lost
and nothing replaces it, while the independent warrant's guidance is untouched. The Progress
bound is `≤ 37/100` against the trivial `1` (`progress_le`), the unserved quarter of the
evaluation mass its largest term.

**Scenario B — the strength rebutted while active** (`WarrantInductorRebuttal`). The docket is
quiet. The strength is operative — a survivor, its row held — at every date before 8
(`operative_before`). At date 8 the settlement pins `Y` and `X∧A∧Y` false and leaves `X∧A`
open: the date-9 region contains `(1, 1, 0, 0, 1)` and forces `P(X∧A) ≥ 3/4`
(`antecedent_open`). The strength's outcome is `rebutted` and it is not a survivor
(`withdrawn`). Had its specialized row stayed — at date 9 it reads `2/3·P(X∧A) ≤ 0` — the
system would have been infeasible against the applicability row's `P(X∧A) ≥ 3/4`
(`contraposition_blocked`): withdrawal is what leaves the antecedent's credence where the
applicability puts it rather than suppressing it. Every date is enforced and conforms
(`inductor`); the liability is `−72` with the applicability row now among the rows the second
slack world dominates (`liability`).

*The same question, before and after.* The date-4 problem is posed again at date 9, with its
adequate set *act* unchanged. The constraints change (`withdrawn`). The region changes: at
date 4 every admissible price vector prices refraining at most `1/3`, at date 9 at least `3/4`
(`region_flips`). The guarantees change: no `Excludes` and no `Margins` certificate for this
problem exists on the date-9 bundle (`no_certificate_after`), so the adapter theorem cannot be
applied to it there — the former recommendation is no longer warranted by anything the
construction can certify. The adapter's behavior changes: at the realized market the gate acts
with mass at least `24/25` at date 4 and refrains with certainty at date 9 (`same_question`),
because the enforced pin holds `P(X∧A∧Y) ≤ 1/400 < τ` and the enforced applicability row holds
`P(X∧A) ≥ 3/4 − 1/400`. This reversal follows the pinned price of the refuted conclusion, not a
revised adequacy judgment; whether refraining is *adequate* after the refutation is not a
question the mathematics answers. The declared protocol's date-9 service is dropped and its
transport mass `1/4` reappears in the residual, charged at `D` (`residual_restricted`).

## F. What is learned, and what is not

Three things could be meant by learning here. (1) Learning future normative evaluations or
verdicts: the market's prices on settling sentences are logical-inductor prices and nothing
more is claimed. (2) Learning the strengths or applicability of warrants: not addressed; the
strengths are declared and revised only by the docket and the settlement. (3) **Learning to
respond adequately under changing warranted constraints**: this is what the construction
supports, conditionally. The response at each service is a function of displayed prices; the
prices respect the held constraints within a declared tolerance at every enforced date; the
declared adequacy semantics and the certificates turn that conformance into a bound on the
inadequate response mass and hence on the anchored loss. Revision changes the held
constraints, and the same theorem reads them off the revised state; Scenario B shows one
question's guidance withdrawn by revision and the adapter following the market.

**A conditional asymptotic corollary.** Fix services `s = 1, 2, …` with intensities `lamS_s`
and tolerances `tol_s`. If the tolerances are summable in square against the intensities, the
error terms `εad_s` vanish, and the transport plan covers the exposure (residual `→ 0`), the
Progress bound tends to zero. The conditions this needs are exactly the inputs: coverage,
stability (the margin `τ + δ` survives the tolerance at every service), and the adequacy
semantics at each service. Nothing is proved about the convergence of the warrants.

**What is not established.** That any warrant is sound or that any adequate set is adequate;
that the admission is legitimate — entitlement reads admission from the protocol and liveness
from the account, and neither the protocol's admission predicate nor the `Expresses` relation
is derived; that the settlement is sound for the deductive process (it enters through the
slack-world hypotheses); market computability beyond finite-phase bundle schedules and
computable deductive processes; the bankroll for more than one reopening; a distance-to-region
reading of conformance (§G); and that conformance to a credal constraint is more than that — a
price near an admissible region proves nothing about an action without the declared adequacy
semantics and the margin, which are inputs.

## G. One interface, two realizations

The Normative Inductor is an interface, not an enforcer. **The interface**: a compiled region
`K_s` per service, a trader added to the market under bounded liability, a public
**defect** `d_s ≥ 0` the realization displays, and for each response-relevant functional a
**certified bound** at the displayed price in terms of that defect. The Progress bound
(`Evaluation.progress_bound`) consumes exactly this through `PracticalUptake`: `d_s ≥ 0`,
`PracticalCert` on each served edge — anchored loss `≤ M·d_s + ε` — the work relation
`λ_s d_s² ≤ ρ_s`, and amplification. The adequate-set route reduces `PracticalCert` to a
coupling of the adapter's inadequate mass to `d_s`, which any adapter sound at a region point
and Lipschitz in its scores supplies (`GatedChoice`).

**The projection realization** (`NormativeInductorComposition`, `ProjectionForce`). The
enforcer is Euclidean projection of the displayed prices onto `K_s` at a prospective
multiplier; its defect is the sup-distance `d_s = dist_∞(b_s, K_s)`; the work relation is
derived from the projection's kernel-checked Euclidean work bound; conformance is a distance
(`dist2 (market n) (target n) ≤ tol`). It needs a vertex representation of `K_s`, and the
coupling an adapter needs is in terms of the distance of the displayed scores from the region.

**The rowwise realization** (`WarrantForce`, `WarrantInductor`). The enforcer holds each row at
the calibrated intensity; its guarantee is per row, `excess ≤ tol_s`, at the realized market;
certificate transport carries it to any functional with a certificate; the defect is the
displayed inadequate excess `Σ_{q∉A} (score_q − τ)⁺`, bounded by `massCap_s · tol_s`. It needs
only the rows and a feasibility witness, and its coupling is through the certificates' mass.

Neither implies the other without a constant. From rowwise excesses the distance to the region
is bounded by a Hoffman constant of the row system, which depends on the bundle and is not
computed here (item 125); from a distance bound, a row's excess is bounded by the row's norm
times the distance. Both realizations deliver the interface's defect and certified bounds, both
are retained on the same deductive market, and the Progress theorem is indifferent to which
produced its inputs.

**Two claims, kept apart.** *Normative warrants constrain the prices of the market*: this is
conformance, and it follows from enforcement under feasibility (an enforced outcome) and
affordability (the liability bound), with Logical Induction preserved. *Normative warrants
produce warranted guidance about the adapter's behavior*: this additionally requires the
adequacy semantics — a declared adequate set, anchored losses — and the certificates that tie
the declared set to the bundle; it is the adapter conclusion and the Progress bound, and it is
conditional on those declarations. Neither claim says the admitted warrants are correct, and
Scenario B shows the second can be withdrawn by revision while the first continues to hold on
what remains.
