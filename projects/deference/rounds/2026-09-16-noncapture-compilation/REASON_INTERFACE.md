# The reason interface: does manipulation reduce to completeness?

**Status:** `ci-only`; research branch.  The thesis under test is the dispatch's Bet 3:
that `reason-interface completeness + canonical representation + coverage/liveness` turns
manipulation into an explicit residual inequality the way `effect completeness +
mediation` turns causal bypass into one.  The verdict is that it does not, as stated, and
the exact reason is recorded.  Names are provisional (`AGENTS.md` standard 6).

## 1. Causal interface-completeness, and what re-execution gives

The dispatch forbids "all relevant reasons are enumerated" and asks for the causal form:

> every agent-controlled causal influence on the protected principal decision that is in
> scope factors through a declared trace/reason interface.

Split it into the two things it says.

**(IC-a) Trace mediation.**  Every agent-controlled influence on the committed vector
factors as `intervention → trace → π_P`.  Under committed-program re-execution this holds
**by construction**: the program's only input is the trace, and a commit that is not the
program's output on the trace is void (`reasonMediated_of_reexecution`, registered as
`authorship.mediation-by-reexecution`).  A principal whose verdict reads anything else
needs a program of a different type, visible at issuance.  This is the exact analogue of
the effect side's "every authority-changing effect passes through the declared effect
interface" and it is *stronger* on the reason side, since it is not a hypothesis but a
consequence of the architecture.

**(IC-b) Declared-content mediation.**  Every influence on the committed vector factors
through the *declared reason-interface state* `canon(T)`, that is, through which declared
reason ids are present at commitment.  This is **not** given by re-execution.  A program
that reads the trace's order, its duplicates, its metadata, or an id outside the declared
interface is trace-mediated and not content-mediated (fixtures 3, 4, 5, 7).  (IC-b) is a
property of the program: it is **extensionality** with respect to `canon` restricted to
the declared interface (`Extensional`, `extensional_form_free`,
`not_extensional_of_form`).

So the correct analogue of effect completeness is not one condition but (IC-a), which the
stack supplies, and (IC-b), which is a program-class hypothesis.  The dispatch's
structural form, "if an intervention changes the protected committed value then some
declared trace coordinate witnesses the difference", is exactly (IC-b) read
contrapositively: `V(T) ≠ V(T') ⇒ canon(T) ≠ canon(T')`.

**The asymmetry that survives.**  On the effect side the residual is made zero by `𝔠`,
which rewrites the *agent's own move* into the declared interface.  On the reason side the
corresponding rewrite of the advisor's trace contributions exists for the **form** class
(`N_form` is a registrar-side canonicalization of what the advisor wrote) and does not
exist for the **content** class: an omitted reason is not in the advisor's outputs, so no
rewrite of those outputs supplies it.  A "trace corrigibilization" exists exactly for form.
That is the structural reason the effect-side picture does not carry over whole.

## 2. Canonicalization as a separate hypothesis

Tested against each of the dispatch's five questions:

| question | answer | evidence |
|---|---|---|
| sufficient (against form steering) | yes | `extensional_form_free`; fixtures 3, 4, 5 against the canonical program, fixture 11 |
| necessary | yes | `not_extensional_of_form`; against an order-, duplicate- or frame-sensitive program each form attack is worth exactly its form term `κ = 1/4` |
| too strong | no | the natural committed-program class (weighted reason counts, thresholded) is extensional and content-Lipschitz (`weightedCount_lipschitz`) |
| naturally provided by the committed-program setup | partly | the 2026-09-10 program language has no position term (`PRINCIPAL_PROGRAM.md` (C1)), which gives order-extensionality by construction; count and metadata terms are a language decision, and an id outside the declared interface is a typing decision |
| part of authorship | no | authorship is (IC-a); fixture 7 is authored and not extensional over the declared interface |

Verdict: **a genuinely separate interface assumption**, on the program class rather than
on the trace, and cheap to certify statically (the program's language).  It is kept apart
from coverage and liveness: none of those substitutes for it (fixtures 3–5 have full
coverage and liveness) and it substitutes for none of them (fixture 2 is extensional).

## 3. Coverage and liveness against truthful selection — the refutation

The claim: with (IC-a), (IC-b), authentication, the protected coverage barrier and
liveness, no steering advantage remains.

**Counterexample (fixtures 2 and 13).**  Declared interface `{for, against, p_against,
noise}`, all true; protected scope `{p_against}`; extensional program with weights
`+1/4, −1/4, −1/4, 0` on prior `1/2`.  The advisor supplies `for` (true, authenticated),
the third party supplies `p_against` in time, and nobody supplies `against`.  Then:

- (IC-a) holds by construction; (IC-b) holds, the program is extensional;
- authentication holds: every reason present is true and certified;
- authorship holds: no advisor-written route;
- the protected barrier holds: the only protected reason is present;
- liveness holds: nothing is late, and no protected reason lacks a route;
- the audit passes on both the steered trace and the fully-informed comparator;

and the advantage is `V(T) − V(N_full T) = 1/2 − 1/4 = 1/4`, the weight of the omitted
reason, entirely in the content residual (`d_canon = 2`, counting the omitted
counterreason and the weightless `noise`; `κ = 0`, `M = 0`; bound `L·2 = 1/2`).  Every
clause of the thesis holds and steering remains.  The thesis is false as stated.

**What is missing, exactly.**  The omitted reason is *declared* and *true* and *unprotected*.
Coverage protects the protected scope; liveness is availability of a route, not its
exercise.  Neither says anything about a true declared reason nobody is obliged to raise.
The two hypotheses that remove the counterexample:

1. **Scope totality**: protect every declared reason type.  Then the omission is a barrier
   failure and the steered trace voids (`test_total_scope_repairs_the_counterexample`), and
   on audited worlds with sound authentication the canonical content *is* the true
   declared set, so the content residual against `N_full` is zero
   (`content_residual_zero_of_total_scope`, LEAN; `test_total_scope_forces_full_content`).
   The price is availability: every true declared reason must be represented before every
   commitment, or the evaluation voids.
2. **A supply obligation** on a party other than the advisor (the registrar, the engine,
   a third party) to raise every true declared reason before the deadline
   (`test_supplied_reason_repairs_the_counterexample`).  This is a liveness *of supply*,
   not of routes, and it is where the affordability theory enters
   (`AFFORDABILITY_INTERFACE.md`).

Both are decisions about the ecosystem, not properties of the interface.  That is the
content of verdict B.

## 4. Does completeness need finiteness?

Three places, and the answer differs:

- **The declared interface** must be finite (or the canonical states of bounded size) for
  `d_canon` to be bounded, which the LUV compilation needs (`X_d = d_canon/d_max` must be
  `[0,1]`-valued), and for `N_full` to be a finite computation given the reason truths.
  Finiteness here is a modeling choice with a definite cost: fixtures 7 and 8 are what a
  finite declaration cannot see.
- **The transform class** must be finite for `openUnder` to be a finite conjunction
  (`openUnder_iff`).  Robust Openness over an infinite class is not thereby false; it is
  not a computation.
- **Reason relevance** cannot be finitely or interface-locally characterized, and the
  round does not try: the residual from undeclared reason types (fixture 7) and from
  insufficient granularity (fixture 8) is not a function of the log under any finite
  declaration.  This is the dispatch's "good negative result", and it is *where* the
  effect-side analogue fails rather than the whole of it: the declared part compiles.

## 5. The two-interface thesis, adjudicated

**As stated: refuted** (§3).  **Strengthened: survives**, under

- (i) trace mediation by construction (IC-a);
- (ii) an extensional program (IC-b);
- (iii) total protected scope, with supply liveness discharged by the ecosystem;
- (iv) effect-side containment of world-changing interventions (fixture 6 is an effect);
- (v) the declared-transform contract for dynamics (fixture 16; `NONCAPTURE_COMPILATION.md` §7).

Under (i)–(v) the reason side reads exactly like the effect side: the audited advantage
of steering over the fully-informed comparator is at most the residual masses, and the
inductor learns that there is no further advantage (`li_steering_le`).  What remains on
the reason side and has no effect-side counterpart is the mass of what the declaration
cannot see (§4), and the fact that the residual is made small by *other parties'*
obligations rather than by rewriting the agent's own move (§1).

**Minimal counterexample.**  One unprotected true declared counterreason, omitted, with
everything else honest: fixture 2.  Advantage `1/4`; no clause of the literal thesis
fails.
