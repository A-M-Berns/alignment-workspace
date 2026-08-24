# Open questions

Genuine remainders only.

1. **Sharp schedulability condition.** Under overload, deadline-free
   specs keep eventual certifiability, Check-windowed specs lose
   forceable certifiability, Admit-windowed specs lose timely
   closability. The load bound relative to spec windows under which
   `Schedulable(A_class, Gamma, capacity)` holds for each notion — a
   real-time scheduling question in this vocabulary — is open, as is
   a solver for timely closability (admissibility-aware monitors are
   specified but not built).

2. **Between coalescing RR and unbounded multiplicity.** Same-type
   open-occurrence counts are unbounded counters. Whether a decidable
   liveness fragment exists with bounded multiplicity k > 1 (compiling
   to RR over k tracked occurrences per type, or to the counting
   extension the RR paper cites as [18]) was not determined.

3. **Strategy-level RR transfer.** The compilation correspondence was
   checked at play level. That winning strategies of the compiled RR
   game induce service policies with the same guarantee (and the
   converse) is the expected but unproved strategy-level statement.

4. **Stochastic and fairness refinements of `Servable`.** The base
   notion is deterministic-adversarial with finite branching. Whether
   the record wants an almost-sure variant (for `KnownPrior`
   instances) as a first-class predicate, and what fairness
   assumptions on `Gamma` are ever normatively warranted, are open —
   and partly upstream questions.

5. **Certificate reuse discipline.** Microcase 5 shows evidence
   sharing is spec-governed. Whether the record layer wants a standard
   vocabulary of account rules (shared, exclusive, k-use evidence)
   rather than free-form spec content is an upstream design question
   surfaced, not answered, here.
