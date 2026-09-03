# Research round: Unified Grounds and Answerable Defeat

Prompt-author model: Claude Fable 5.1 (Anthropic), via chat. Executor: unrecorded
in the dispatch; the executor was Claude Opus 5 (Anthropic), recorded in the round's
`PROVENANCE.md`.

Work against the live alignment-workspace at current main (PR77 landed; the Sep 1
checkpoint #76 is on main). Inspect the actual head before naming anything. This
round answers `PRIORITIES.md` item 77 (what licenses authorized disposition). It
touches items 58, 61, 75 and 76 only to file precise non-goals against them; it
does not attempt them.

Preserve unless refuted: settled Normative Continuity (`NORMATIVE_CONTINUITY.tex`
rev 2 and `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`), the
carriers/anchored-slices/faithful-preservation stack as landed by PR77, the
fixed-era theorem (`FIXED_ERA_THEOREM.md`, frozen), and every registered claim.
Continuity surgery is permitted in this round only where §1 says so, and every
change must re-elaborate every existing theorem in the file.

## 0. The working hypothesis

The round works under the **Defeat Principle**: no participant extinguishes a
debt; a participant may pay it or move it onto the grounds for saying it is not
owed; only settlement extinguishes. If a dated `DECISIONS.md` entry adopting or
rejecting this has landed by the time you read this, cite it and work under it.
Otherwise treat the principle as the round's hypothesis, record it as
agent-decided and reversible (R2), and make every theorem below explicitly
conditional on it.

Terminology, provisional (R4): a resolution has a **kind** — `answer`
(rebuttal of the challenge-warrant; discharges content), `dispose G` (undercut
of the challenge-warrant, grounded in `G`), `settle s` (the world lowered the
level of demand). "Defeat" of a debt means `dispose`. Do not introduce a fourth
kind. If you find a resolution the three kinds cannot classify, that is a
finding; report it, do not add a kind.

## 1. One ground type

Diagnose first. The Lean spine keeps two traces — `IssueTrace` over `Q` and
`StandingTrace` over `N`, bridged by `Licensing.standsFor` — and `Grounded` is
defined only on the standing side. State exactly which occurrences a disposal
may cite as grounds (prior issues, standing facts, rule revisions, settlement
facts) and show that no single existing type holds them.

Then unify: `Ground := Q ⊕ S`, where `S` is a type of settlement facts with a
monotone `Settled : ℕ → S → Prop` that belongs to no participant's write set.
`Grounded n (inl q)` iff `q` is in the record strictly before `n` (outstanding
or resolved); `Grounded n (inr s)` iff `Settled n s`. Make standing occurrences
and rule revisions issues of a licence/revision kind so that `Ladd` is birth,
dropping is disposal, `Fresh` is `born_unique`, and `standsFor` is *derived*
from live licence-issues in the prefix. Delete `StandingTrace`, `Licensing` and
`Grounded` as primitives and re-derive `grounded_replay`, `anchor_grounded` and
freshness as corollaries of `anc` on the unified trace. If any of them does not
re-derive, say precisely which requirement was doing work the unified trace
lacks.

Change `Met` from a primitive judgment to a definition: a prerequisite is met
iff every root is resolved before `n` **by answer or settlement**. Prove
`met_persistent` still holds. Test the claim that, because `Routes` is
ancestry-closed, a wait on a disposed root reroutes to the successor with no
new axiom — and state the resulting strengthening of `persistent_wait` ("a
prerequisite cannot be disposed away") as a theorem or refute it.

Keep settlement a summand, not an issue kind. If you find a reason it must be
an issue kind, report it as a finding and stop; do not implement both.

Add to `TraceData`: `A` (participants), `kind : ℕ → Q → Kind Q S`,
`by : ℕ → Q → A` (resolver), `opener : Q → A`. Add exactly one requirement to
`IssueTrace`: a `dispose` resolution in batch `n` is accompanied by a fresh
`q' ∈ Born n` with `q ∈ par q'`. Check that this is `fresh_successors` read in
reverse and that `resolution_continuity` and `no_rewire` need no change.

## 2. Answerable disposal and separation

Define **answerable disposal** for `q ∈ Res n`, `kind n q = dispose G`:

- D1 grounded: every `g ∈ G` satisfies `Grounded n g`;
- D2 routed: the successor `q'` from §1 has content "G suffices to dispose q"
  and inherits `q`'s load;
- D3 separated: some `b ≠ by n q` has standing on `q'`, and some `g ∈ G` has
  `opener g ≠ by n q`.

Define a **defeat-disciplined** trace: every resolution is `answer`, an
answerable `dispose`, or a `settle s` with `Settled n s`.

Label each disposal edge by its resolver. Characterize **laundering** as a
walk in the disposal graph whose edges, grounds and standings all belong to one
participant, and prove separation forbids such walks. Then attack: exhibit the
two-participant alternating walk that satisfies D3 and launders. Do not repair
it in this round; file it (§6) with the coalition-indexed statement the general
non-capture predicate would need.

Show that the transition-certificates round's no-self-grounding (a theorem of
its checker, not an axiom — see its `MEMO.md` row 5) re-derives on the unified
trace and covers disposals: a disposal cannot be grounded in itself, its
successor, or anything born in its batch.

## 3. Loads and mass — two layers, one rule

The carriers stack tracks **loads** in a join-semilattice with satisfaction,
disposition and transfer components. The service layer tracks numeric
obligation **mass** with two fates. Reconcile them under the principle:

- Carrier layer: a `dispose` sets the disposition component to bottom and
  transfers the disposed component to the successor with an identity
  certificate (the identity frame). Restate Slice-wise Conservation with the
  `disp` receipt identically bottom in a defeat-disciplined trace. Handle
  mixed resolutions componentwise — part answered, part disposed — and check
  the identity-frame condition per component.
- Service layer: define the terminal claim measure `μ̃^r_N` as the pushforward
  of `μ^r_N` along disposal chains. Prove disposal is a claim-to-claim
  transport step with `L = 1, ε = 0`, and that the transport plan of F3
  factors through it. Define the contest residual `κ^r_N` (claim mass in open
  successors over `C^r_N`) and derive the F3 bound with the added term
  `D κ^r_N`. This is a corollary; if it needs more than F3 plus conservation,
  report why.

Do not touch the transport constants on answer edges (item 76).

## 4. Theorems

State and, where marked, prove:

- **T1 Conservation** (prove, carrier layer; state, service layer): in a
  defeat-disciplined trace, open load/mass at `N` equals initial minus
  answered minus settled. Disposal contributes zero.
- **T2 Liveness** (Lean): `persistent_wait`, `persistent_opportunity`,
  `no_structural_abandonment` re-elaborate unchanged on the unified trace, and
  the corollary that a matter resolved only by disposals from `n₀` on has
  `Live n m ≠ ∅` for all `n ≥ n₀`.
- **T3 Reach** (prove on the trace; state the composition gap): for principal
  `P`, advisor `V`, and matters `Corr(P)`, if every disposal by `V` over a
  corrective matter is separated with `P` among the standing-holders on the
  successor, then at every `n` each `m ∈ Corr(P) ∩ M n` has a live issue on
  which `P` stands. State explicitly that this preserves reach, not the ability
  to open a challenge (a scorekeeping move, item 58) nor its service
  (non-starvation); do not prove the composition.
- **T4 Persistence with defeat** (prove under exogenous contest durations;
  state the endogeneity gap): with contest charge `c` per open successor per
  date entering the liability account as a budget drain, a norm has a
  persistent affordable schedule iff `liminf_t L_t(1) = 0` and
  `Σ_disposals τ(q') < ∞`. Give the bounded-delay refinement: successors
  inherit deadlines, D4 applies to terminal claims, and uniform bounded delay
  requires `τ(q') ≤ H`. State that `τ` is policy-dependent and that the
  closed-loop version is item 75; do not attempt it.
- **T5 Necessity of separation** (finite fixture): drop D3 and exhibit the
  self-grounded disposal chain that conserves mass, is contested by nobody and
  serviced by nobody. Relate it to the two-books countermodel of reasonwise
  accounting.

Register Lean headlines at merge (R5). Everything else is test-supported and
unregistered; say so.

## 5. Hostile fixtures

Exact finite cases, in the settlement round's runner style: disposal grounded
in its own successor (refused by ancestry); disposal grounded in a fact the
disposer settled (refused unless `Settled` is outside the write set — make the
independence of settlement from the disposer's writes an explicit hypothesis
and test its necessity); a wait on a disposed root that reroutes; a wait on an
answered root that is met; a mixed resolution with mismatched component
receipts; the single-author laundering walk (refused); the two-author
alternating walk (accepted — the finding); a disposal chain with infinite total
contest duration under `liminf L_t(1) = 0` (not persistent); the same chain
with bounded contest (persistent); a settlement that lowers demand with no
successor and no charge.

## 6. Out of scope and reservations

Out: item 58 composition, item 75 closed loop, item 76 transport constants,
item 61's weld (the reading that the enforcer's risk capital and the contest
cost of its exclusions are one account is noted as a reading, filed under item
61 as a candidate route, and not argued), market realization of the contest
charge, and any change to the affordability round's frozen files.

Reserve to the author, each with a one-line *turns on*: whether disposal
transfers load in full or at a discount (turns on taste about second-order
liability; changes T4's constants, not structure); whether settlement's
independence from the disposer's writes is a standing hypothesis of the program
or a per-realization assumption (turns on where `L_t` comes from in the
assessment-process generalization); and the coalition finding from §2 (turns on
whether legitimacy may presuppose a designated protected participant). Append
each to `DECISIONS.md` *Awaiting the author* per `AGENTS.md` §10.

## 7. Deliverables

Round directory under `projects/normativity/legitimacy/rounds/`: `REPORT.md`
first, then `GROUNDS.md`, `DEFEAT.md`, `LOADS_AND_MASS.md`, `THEOREMS.md`,
`COUNTERMODELS.md`, `PROVENANCE.md`, `src/`, `tests/`. The Lean lives in the
spine file; if the unification forces a split, name the new file and cite the
prompt. Provisional names listed in the report. Depends-on and rests-on filled
(R9). Report every deviation. If the unification breaks a Continuity theorem
you cannot repair, stop, report the theorem and the requirement it needed, and
leave the spine unchanged.
