# Certified interactive service prosecution

Round question: is there a minimal, non-vacuous interactive-service
interface that exactly embeds the set-cover/submodular/adaptive inquiry
models, expresses the non-submodular and multiplicity-bearing cases a
bounded normative learner needs, supports serviceability and
certification, and composes with the record-above / assessment-below
boundary?

**Verdict: REQUIRES-REVISION — the object survives as an arena plus
finite-witness certification, its laws typing disciplines, its content
in the capability lattice.** The conjectured object survives after five
revisions, as `I = (A, Y, Gamma : H x A -> P+(Y), Sigma)` with
liabilities external and costs demoted to objective annotations:

1. per-action response sequences `Y*` collapse to one response event,
   with embeddings required to preserve the source model's
   observation/action order (the tick convention — see
   `CERTIFICATION_CLEANUP.md`, which adds a finite counterexample
   showing the order matters online);
2. hidden world state leaves the public interface (it is only needed
   to define semantic success, which is excluded from the core);
   `Gamma` denotes the epistemically possible responses given the
   public history, not true hidden dynamics;
3. `cost` is structure on optimization problems over the core;
4. certification splits into historical validity and present
   discharge: the existential predicate `Certifiable` is
   extension-closed as a THEOREM of citation locality plus
   append-only receipts, and freshness/lapse conditions are
   record-side discharge policy (`MayClose`), not spec structure —
   CIS produces certificates and closes nothing
   (`CERTIFICATION_CLEANUP.md`, `CLOSEOUT.md`);
5. external, identity-bearing obligations are confirmed against
   internalization by the multiplicity microcase; the service-facing
   request type carries only the obligation reference and pinned
   spec.

The core laws (finite witness; citation persistence; observation
locality; pinned specification; interpretation separation) are typing
and boundary disciplines: they exclude category errors and make service
auditable, and they prove no theorems. The mathematical content lives
in the capability lattice; each prior model is a capability
conjunction, and each imported guarantee names its capabilities. The
bare object is deliberately weak: it is a waist, not a theory.

## Map

- `CLOSEOUT.md` — the final surviving interface and full-stack
  contract, stated without narrative, with the closeout verdict.
- `INTERACTIVE_SERVICE_INTERFACE.md` — types, subtraction analysis,
  laws, capability taxonomy with layer typing.
- `CERTIFICATION_CLEANUP.md` — the follow-up prosecution: the
  validity/closure split, the monotonicity theorem, online timing,
  the serviceability notion lattice, and the reason-waist
  compatibility audit, with the four closeout verdicts.
- `PRIOR_ART_EMBEDDINGS.md` — exact translations and preservation
  claims for Set Cover with Delay, Submodular Ranking / MLSC, Adaptive
  Submodularity, Interactive Submodular Set Cover; the two-way
  Request-Response analysis.
- `SERVICEABILITY.md` — `Servable` as forced reachability; the
  interference counterexample separating individual from joint
  serviceability; the overload results separating eventual service
  from bounded latency, and their spec-relativity.
- `HANDOFF.md` — the upstream/downstream contract.
- `src/`, `tests/` — executable reference model: 63 exact finite
  tests covering all ten mandatory microcases, the five embeddings
  (including the RR paper's Example 2 value `56/10` reproduced
  exactly), the RR compilation correspondence, the
  validity/discharge split with record-side stubs, the online-timing
  counterexample and repair, and the canonical three-provenance
  boundary fixture. Run `python3 tests/run.py`.
- `OPEN_QUESTIONS.md`, `PROVENANCE.md`.

## The ten dispatch questions

1. Generalizes Set Cover with Delay: yes, exactly, under the stated
   discrete-event and tick (arrival-first) conventions; guarantees do
   not transfer outside the subclass.
2. Generalizes Submodular Ranking / MLSC: yes, exactly, for fixed
   dockets with set-factorizing normalized submodular specs.
3. Generalizes adaptive submodular coverage: yes; GK coverage
   (Definition 7) is the generic certificate; the prior and the
   adaptivity conditions are capabilities.
4. Generalizes Interactive Submodular Set Cover: yes; the
   consistency-relational `Gamma` expresses it with no hidden state,
   and fixed-target vs consistency-adversary coincide for certified
   objectives.
5. Request-Response games: overlapping abstractions, not a nested
   subclass — RR embeds as instances, a coalescing finite-state
   fragment compiles to RR, and identity-bearing same-type
   multiplicity is a genuine two-way mismatch.
6. Certification is load-bearing: yes — it is what a record can close
   on (microcase 6), it is where ISSC's stated semantic termination
   must be repaired to be learner-usable, and GK's own coverage
   definition already is it.
7. Hidden environment state is not part of the public interface.
8. Weakest useful law set: L1-L5 plus the validity/discharge split
   L2'' as typing/boundary disciplines, with extension-closure of
   `Certifiable` a theorem rather than a law or capability.
9. Guarantee-to-capability attribution: the taxonomy table in
   `INTERACTIVE_SERVICE_INTERFACE.md`.
10. Composition with the learner boundary: yes, demonstrated and
    vocabulary-enforced in `tests/test_composition.py`.

All names are provisional. Nothing in this round is registered or in
Lean.
