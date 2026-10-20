# The warrant Normative Inductor

A mathematical account of one construction, written to be read without the repository.
Every named object is a Lean declaration under `lean/Workspace/Normativity/Contrib/`.

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
practical adequacy). The construction below addresses all three, and the theorem says exactly
which parts are proved and which are inputs.

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

**Licence.** A verdict is a value for a coordinate. A verdict certificate is a pair of bound
certificates — nonnegative multipliers on rows summing to `±e_φ` — each row cited by
occurrence, with the two attained endpoints. *Supported*: every positively weighted row is a
survivor's row under that occurrence's citation, a pin, or a cube face; the endpoints bracket
the verdict and are attained in the region. *Licensed*: supported, and the issuing event
authorized. Licensed implies supported implies admissible (`licence_chain`), and neither
converse holds (`Countermodel`). A certificate citing a rebutted or undercut occurrence is not
supported — the licence is settlement-sensitive because the bundle is.

**Admission.** How an accounted obligation becomes a warrant occurrence is a typed input
(`Admission`): a map from occurrences to exposed obligation occurrences. The legitimacy of
admitting a constraint to the market is thereby separated from the authorization of a
verdict-selection event (the record's `authorized`), and neither is derived here.

## C. Enforcement

**The trader.** The force layer's trader holds, on each row `⟨a, P⟩ ≥ b`, a position
proportional to the row's violation at the day's displayed price, at a declared intensity
(`enforcementStrategy`). Its value against a world is the units-weighted signed gaps plus the
intensity-weighted squared violations (`Account.day_value_eq`).

**The schedule and the market** (`WarrantSchedule`, `.enforcer`, `.market`). A fragment map
`ι` prices coordinate `j` as the sentence `ι j`; each date carries a compiled bundle — the
state's bundle if the supplied rational witness checks into its region, nothing otherwise
(`compileAt`) — and a tolerance `tol_n`. The enforcer is effective data: on date `n`, against
the ordinary aggregate's trade list `ord`, it holds the bundle's rows at the **calibrated
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
`m` on — it is at least `−3ρ(2+ρ)`: the pre-reopening bankroll plus `ρ` times the
post-reopening slack mass, which the capital bounds by `3 + 3ρ`. Intensity, tolerance and the
number of rows and dates do not appear. For a warrant of strengths `c`, the natural `ρ` is the
largest odds `c/(1−c)`.

**Preservation.** With a liability bound and the enforcer effective, the augmented market is
a logical inductor over the deductive process in the source's original sense
(`WarrantSchedule.isLogicalInductor`): the computability of the market is supplied by the
compiled bounded evaluator (`EnforcedCompiler`), given that the trade map is primitive
recursive — which it is whenever the bundle schedule runs through finitely many phases
(`WarrantSchedule.computation`).

**Conformance** (`rowViolation_le_tol`, `excess_le_tol`). At every date with a checked
witness, every enforced row has violation at most `tol_n` at the displayed price. The proof is
the force layer's inequality `Σ_i κ_n g_i² ≤ ε_n + A_n`, whose two right-hand terms are
discharged at the real market: the slack by the market maker's contract at every cube point
(`marketMaker_day_value_le_cube`), the volume by the ordinary aggregate's syntactic bound
(`Strategy.abs_value_le`); the calibrated intensity is exactly what turns this into
`g_i ≤ tol_n`. This is rowwise conformance, not distance to the region.

**Transport** (`FunctionalCert.le_of_excess`, `BoundCert.transport`, `bracket_at_market`).
A certificate — nonnegative multipliers `m_i` on rows whose normals sum to a functional `ℓ` —
carries rowwise conformance to the functional: at any price where every positively weighted
row's excess is at most `δ`, `ℓ·p ≤ Σ m_i b_i + (Σ m_i)·δ`. The multiplier sum is the
certificate's **mass**, the Lipschitz constant of the certified bound in the rows' excesses.
Hence a supported verdict's bracket holds at the displayed price, widened by `mass · tol_n` on
each side. Semantic entitlement (the licence) and operative force (the enforcer) meet in this
inequality; it is the quantitative conversion from the force layer's rowwise guarantee to the
bounds a licence certifies and an adapter reads.

## D. The main theorem

`WarrantInductor.warrant_inductor`. Fix a fragment `d`, a state process `N : ℕ → NormState d`,
a fragment map, witnesses `wit`, tolerances `tol > 0`, and a deductive process `DP`. Assume:

1. *Admission and well-formedness.* An `Admission O (N n).grounds` for every date, and
   `(N n).grounds.WellFormed` (unique identities, resolving citations).
2. *Computability.* `DeductiveProcessComputation DP`, and the enforcer's effectiveness
   `EffectiveEnforcerComputation (schedule …).enforcer` (discharged by `computation` for
   finite-phase schedules).
3. *Affordability.* A bound `B` with `−B ≤ netWorth` at every plausible world at every date
   (discharged by `liability` from one slack world, or `liability_reopened` across one
   reopening).
4. *The adapter protocol* `A`: services (dates), an evaluation measure and transport plan,
   one finite-menu problem per service — responses scored by affine functionals of the
   displayed prices, a declared adequate set `A`, margin witnesses `A₁ ⊆ A`, a positive task
   preference, a threshold `τ`, ramp width `δ`, witness mass `W`, and certificates on the
   bundle: an upper certificate on each inadequate response's score with `offset + value ≤ τ`
   (`Excludes`), a lower certificate on each witness's score with
   `τ + δ ≤ offset − value − mass·tol` (`Margins`) — at the service dates, together with
   checked witnesses there.
5. *Adequacy semantics.* Anchored losses `lam r s q` with `lam ≤ εad_s` on `A_s` and `lam ≤ D`
   everywhere.
6. *The declared constants.* Nonnegative intensities `lamS` with positive sum, budgets
   `lamS_s · (massCap_s · tol_s)² ≤ ρ_s` where `massCap_s` is the inadequate responses'
   certificate mass, and the amplification bound `Σ_e T(e,s)·D·κ_s ≤ Γ·lamS_s/Σ lamS` with
   `κ_s = (Σ_{q∉A} pref q)/(W δ)`.

Then, on the augmented deductive market of the compiled schedule:

1. **Logical Induction**: `IsLogicalInductor (W.market DP) DP`.
2. **Conformance**: at every checked date every row of the state's bundle has excess at most
   `tol_n` at the displayed price; and every enforced row is a survivor's row — whose
   occurrence realizes an exposed obligation and whose citation names exactly one survivor —
   a structural row, or a pin.
3. **The adapter**: at every service date the gate's mass on inadequate responses is at most
   `κ_s` times the public defect, which is at most `massCap_s · tol_s`.
4. **Progress**: `progress ≤ Γ √(Σρ/Σλ) + Σ T ε + D·residual`, with `PracticalUptake`
   derived, not assumed.

What the hypotheses are. Admission, the adequacy losses and the declared constants are
semantic and protocol inputs: nothing in the market derives that `A_s` is adequate or that
`lam` scores it. The certificates are checkable facts about the normative state, not about the
market. The liability bound and the enforcer's effectiveness have theorems that discharge them.
The deductive process's computability is the deductive process's.

The theorem is not a conjunction of its predecessors. Before it, `ComputableMarket`,
`PracticalUptake`, the maker's contract at the realized market, and the licence's relation to
the enforced rows were all hypotheses; each is now either derived or replaced by a checkable
condition on the normative state.

## E. The example

`WarrantInductorWitness`. Five sentences `X, X∧A, X∧A∧Y, Y, Z`. A principal warrant
`P(X) ≥ 4/5`, `P(X∧A) ≥ 3/4·P(X)`, `P(X∧A∧Y) ≥ 2/3·P(X∧A)`, each form citing the one before;
an independent warrant `P(Z) ≥ 3/4`; three coherence rows. `X` settles true at date 3; the
applicability is undercut at date 5; `Y` is refuted at date 8. Tolerance `1/400`.

*What happens to the warrants.* Through date 4 all four occurrences survive; from date 5 the
strength occurrence leaves with the applicability it cites — not at date 8, when its consequent
is refuted. From date 8 the premise and the `Z` warrant remain, with the pins. The compiled
bundle runs through four phases, so the enforcer is effective data (`computation`); the
deductive stage is a step function, so the process is computable (`process`).

*What the market guarantees.* It is a logical inductor over the process. The enforcer's net
worth is at least `−72 = −3·4·(2+4)` at every plausible world at every date: the all-true
world is the slack world before the refutation, the world `X, A, Z` true and `Y` false after it
(`liability`). Every enforced row conforms within `1/400` at every date.

*What the adapter does.* At date 4 the menu is *act on the warrant's conclusion* or *refrain*,
scored by `P(X∧A∧Y)` and `P(X∧A) − P(X∧A∧Y)`; the strength row and a cube face certify the
refraining score at most `1/3` (`excludes₁`), the strength and applicability rows certify the
acting score at least `1/2 − (5/3)/400` (`margins₁`); with `τ = 1/3`, `δ = 1/12` the gate puts
mass at most `1/25` on refraining (`gate_bounds`). At date 9 the menu is *act on `Z`* or
*refrain*, scored by `P(Z)` and `1 − P(Z)`, certified by the `Z` row with `τ = 1/4`,
`δ = 1/4`; mass at most `1/100` on refraining. The gate is not constant: at a price vector in
the date-4 region it acts with certainty, at `(1, 1, 0, 0, 3/4)` it refrains with certainty
(`gate_nonconstant`). After the revision the region no longer excludes refraining — it contains
a point pricing it at `1` (`exclusion_lapses`): the undercut and the refutation together leave
no certified guidance on the principal matter, while the `Z` warrant continues to function.

*The licence at the market.* The verdict `P(X∧A∧Y) = 1/2` is supported on the date-4 bundle
and its bracket holds at the displayed price: `1/2 − (5/3)/400 ≤ P₄(X∧A∧Y) ≤ 1 + 1/400`
(`bracket`).

*The theorem at the fixture* (`inductor`) has no computability and no liability hypothesis.

## F. What is learned, and what is not

Three things could be meant by learning here. (1) Learning future normative evaluations or
verdicts: the market's prices on settling sentences are logical-inductor prices and nothing
more is claimed. (2) Learning the strengths or applicability of warrants: not addressed; the
strengths are declared and revised only by the docket and the settlement. (3) **Learning to
respond adequately under changing warranted constraints**: this is what the construction
supports, conditionally. The response at each service is a function of displayed prices; the
prices respect the operative constraints within a declared tolerance at every date; the
declared adequacy semantics and the certificates turn that conformance into a bound on the
inadequate response mass and hence on the anchored loss. Revision changes the operative
constraints, and the same theorem reads them off the revised state.

**A conditional asymptotic corollary.** Fix services `s = 1, 2, …` with intensities `lamS_s`
and tolerances `tol_s`. The modulus `Γ √(Σ ρ_s / Σ lamS_s)` is `Γ · √(average of
(massCap_s·tol_s)² weighted by lamS_s)` when the budgets are tight. If the tolerances are
summable in square against the intensities, the error terms `εad_s` vanish, and the transport
plan covers the exposure (residual `→ 0`), the Progress bound tends to zero. The conditions
this needs are exactly the inputs above: coverage (the transport plan serves the exposed mass),
stability (the margin `τ + δ` survives the tolerance at every service, which bounds how fast
`tol_s` may fall relative to the certified margins), and the adequacy semantics at each
service. Nothing is proved about the convergence of the warrants themselves.

**What is not established.** That any warrant is sound or that any adequate set is adequate;
that the admission is legitimate (it is typed, not derived); that the settlement is sound for
the deductive process (it enters through the slack-world hypotheses); market computability
beyond finite-phase bundle schedules and computable deductive processes; the bankroll for more
than one reopening; a distance-to-region reading of conformance (the rowwise reading is what is
proved); and that conformance to a credal constraint is more than that — a price near an
admissible region proves nothing about an action without the declared adequacy semantics and
the margin, which are inputs.
