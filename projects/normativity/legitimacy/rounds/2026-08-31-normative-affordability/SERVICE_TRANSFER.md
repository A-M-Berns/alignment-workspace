# Service Transfer

## 0. The objects

For each horizon `N` fix the index set `[N] = {0, ..., N-1}` and two nonnegative
weight arrays: the **claim** weights `c_t` with `C_N = sum_{t<N} c_t > 0`, and the
**service** weights `w_t` with `W_N = sum_{t<N} w_t > 0`. Normalize:

    mu_N(t) = c_t / C_N        the normatively owed exposure measure
    nu_N(t) = w_t / W_N        the actual service measure

A **defect array** is `d^{(N)} : [N] -> [0, D]`. A **fixed defect sequence** is a
single `d : N -> [0, D]` restricted to each prefix. The distinction is the whole
content of §2 and is not a technicality.

The prompt's `c_t^r >= 0` representation is adequate and no weaker object is
needed: every statement below uses only the two normalized measures, so a claim
process is exactly as expressive as the measure it induces. What is *not*
adequate is same-index matching, which §4 replaces.

## 1. The array theorem, and contiguity as the exact condition

**Definition (contiguity).** `mu ◁ nu` when for every sequence of sets
`A_N subseteq [N]`, `nu_N(A_N) -> 0` implies `mu_N(A_N) -> 0`.

**Lemma T1.0.** `mu ◁ nu` if and only if for every `eps > 0` there are `delta > 0`
and `N_0` such that for all `N >= N_0` and all `A subseteq [N]`,
`nu_N(A) <= delta` implies `mu_N(A) <= eps`.

*Proof.* The stated form gives contiguity immediately. Conversely, suppose it
fails for some `eps`. Then for each `k` there is `N_k >= k` and `A_k subseteq
[N_k]` with `nu_{N_k}(A_k) <= 1/k` and `mu_{N_k}(A_k) > eps`; passing to a
strictly increasing subsequence and setting `A_N = A_k` at `N = N_k` and `A_N =
empty` elsewhere gives `nu_N(A_N) -> 0` with `mu_N(A_N) > eps` infinitely often.
`square`

So "uniform absolute continuity" is not a stronger alternative to contiguity in
the list the dispatch asked to compare; it is the same condition stated
non-asymptotically, and the asymptotic form is the one that survives a finite
prefix of bad behaviour.

**Theorem T1 (Service Transfer).** Let `0 <= d^{(N)} <= D` and suppose
`E_{nu_N}[d^{(N)}] -> 0` and `mu ◁ nu`. Then `E_{mu_N}[d^{(N)}] -> 0`.

*Proof.* Fix `eps > 0` and put `A_N = { t : d^{(N)}_t > eps }`. Markov's
inequality on `nu_N` gives `nu_N(A_N) <= E_{nu_N}[d^{(N)}]/eps -> 0`, so
`mu_N(A_N) -> 0` by contiguity. Then

    E_{mu_N}[d^{(N)}] <= eps + D mu_N(A_N) ,

so `limsup_N E_{mu_N}[d^{(N)}] <= eps` for every `eps > 0`. `square`

**Theorem T2 (contiguity is necessary, for arrays).** If `mu ◁/ nu` there is a
`{0, D}`-valued defect array with `E_{nu_N}[d^{(N)}] -> 0` and
`E_{mu_N}[d^{(N)}] ↛ 0`.

*Proof.* Take `A_N` with `nu_N(A_N) -> 0` and `mu_N(A_N) > delta` along an
infinite set `S`. Put `d^{(N)} = D 1_{A_N}` for `N in S` and `d^{(N)} = 0`
otherwise. Then `E_{nu_N}[d^{(N)}] <= D nu_N(A_N) -> 0` while
`E_{mu_N}[d^{(N)}] > D delta` on `S`. `square`

Two consequences worth recording. Contiguity is *exactly* the weakest condition
for the array version — T1 and T2 together — and the extremal defect arrays are
indicators, so nothing is gained by quantifying over graded defects.

**Corollary T1.1 (the quantitative form).** If `mu_N <= M nu_N` pointwise for all
`N`, then `E_{mu_N}[d] <= M E_{nu_N}[d]` for every nonnegative `d`, with no
asymptotics and no boundedness hypothesis. `density_bound` and `transfer_bound`
in `src/transfer.py` compute both sides exactly.

## 2. Fixed defect sequences need strictly less

**Theorem T2' .** For `N`-independent defect sequences the transfer property —
`E_{nu_N}[d] -> 0` implies `E_{mu_N}[d] -> 0` for every bounded nonnegative `d` —
holds if and only if **fixed-set contiguity** holds: for every fixed
`A subseteq N`, `nu_N(A) -> 0` implies `mu_N(A) -> 0`.

*Proof.* For bounded `d`, `E_{nu_N}[d] -> 0` is equivalent to
`nu_N({d > eps}) -> 0` for every `eps > 0`, and `{d > eps}` is a fixed set; the
argument of T1 then applies verbatim with fixed level sets. Necessity is
`d = 1_A`. `square`

**Fixed-set contiguity is strictly weaker.** Take `mu_N = delta_{N-1}` and
`nu_N = delta_{N-2}`: service happens one date before the claim is scored.
Sequence contiguity fails at `A_N = {N-1}`, where `nu_N(A_N) = 0` and
`mu_N(A_N) = 1`. Fixed-set contiguity holds: `nu_N(A) = 1[N-2 in A] -> 0` forces
`A` finite, and then `mu_N(A) = 1[N-1 in A] -> 0`. Checked exactly in
`tests/test_transfer.py::ArrayVersusFixedDefect`, both directions.

**Which version this theory needs.** The array version, and the reason is
settlement. A defect assessed against the still-live continuations — `PC(D_N)` in
the deductive case, the live assessment set generally — is re-evaluated at every
horizon, because the assessment set shrinks as settlement arrives. That is a
genuine triangular array, and T2 then says contiguity is not merely sufficient
but forced. Only a defect pinned by the record at its own date and never re-read
lives in the weaker regime of T2'. **Recommendation: the schematic states the
array version.** The weaker one is worth keeping named, because a realization
whose defect is settled at its date may discharge the cheaper obligation.

## 3. Two attacks, and what each one refutes

### C1 — Surface Fairness is a mass condition, not a fidelity condition

The merged Progress schematic assumes bounded-deficit Surface Fairness

    sum_{N_0 <= n < N} a_n e_n(r) >= eta sum_{N_0 <= n < N} a_n - C

and concludes `D_N / W_N -> 0` with `w_n = a_n c_n`. Take `a_n = 1` on every
date, `e_n = c_n = 1` on even dates and `0` on odd ones, and put the defect
entirely on the odd dates. `(SF)` holds with `eta = 1/2, C = 0`. Then

    E_{nu_N}[d] = 0   exactly, at every horizon,
    E_{mu_N}[d] = floor(N/2)/N -> 1/2 .

The conclusion the theorem delivers is true and empty: the service measure never
looks at a date where anything is wrong. `mu_N` has no bounded density against
`nu_N`, so contiguity fails, and the level set `{d > 1/2}` is the witness the T1
proof would have used. Exact at every even horizon in
`tests/test_transfer.py::SurfaceFairnessIsNotServiceFidelity`.

This discriminates among the four interfaces the consolidation offers for
Persistent Relevance. **Interface 1** — a registered surface exposed on every
service date with `c_n >= c_* > 0` — gives `mu_N <= nu_N / c_*` pointwise and
therefore T1.1 outright. **Interfaces 2 and 4** — finite fair rotation, and
service-mass windows — give `(SF)` and nothing more; the countermodel above *is*
a two-surface fair rotation. **Interface 3** inherits whichever of the two its
intra-matter scheduler implements. The recommended interface in that document is
2-plus-3, so as stated it does not deliver claim-weighted Progress.

### C2 — Dilution

A scheduler can also drive `E_{nu_N}[d]` to zero by padding service onto dates
where nothing is owed. Claims and defect on even dates, one unit of service each;
`N` units of service on each odd date, where the defect is zero. Then
`E_{nu_N}[d] -> 0` while `E_{mu_N}[d] = 1` at every horizon. Contiguity fails
here too, and the diagnostic quantity is the **service-to-claim ratio**
`W_N / C_N`, which diverges. A fixed ratio is harmless: at ratio `1 + M` with `M`
constant, `mu_N = (1+M) nu_N` on the claim dates and transfer holds with constant
`1 + M`.

## 4. Deferral: the transport theorem

Same-index matching is too strong, and C1 shows why: bounded-delay service is
normatively unimpeachable and fails contiguity. A rotation that services each odd
claim at the neighbouring even date has delay `1` and bounded backlog, and still
defeats T1. The repair is to stop comparing `mu_N` with `nu_N` and start
transporting.

**Definition.** A **transport plan** at horizon `N` is `T(t, s) >= 0` on
`[N] x [N]` with

    (T1)  sum_s T(t, s) <= c_t ,  and  R_N := C_N - sum_{t,s} T(t,s)  the residual;
    (T2)  sum_t T(t, s) <= w_s ;
    (T3)  d_t <= L d_s + eps  whenever  T(t, s) > 0 .

`(T1)` says the plan is drawn from what is owed and reports what it leaves
unmatched; `(T2)` says no date is asked for more service than it delivered;
`(T3)` is the transport stability inequality, and it is what carries a conclusion
about the defect at the service date back to the defect at the claim date.

**Theorem T3 (Deferred Service Transfer).** Suppose a plan satisfies (T1)–(T3),
that `W_N <= K C_N` (**service parsimony**), and that `R_N / C_N -> 0`. Then for
every `0 <= d <= D`,

    E_{mu_N}[d]  <=  L K E_{nu_N}[d]  +  eps  +  D R_N / C_N .

*Proof.* Write the transported claim measure `mu~_N(s) = (sum_t T(t,s)) / C_N`.
Then

    E_{mu_N}[d] = (1/C_N) sum_t c_t d_t
                <= (1/C_N) sum_{t,s} T(t,s) d_t  +  D R_N / C_N
                <= (1/C_N) sum_{t,s} T(t,s) (L d_s + eps)  +  D R_N / C_N
                <= L sum_s mu~_N(s) d_s  +  eps  +  D R_N / C_N .

By (T2), `mu~_N(s) <= w_s / C_N = nu_N(s) W_N / C_N <= K nu_N(s)`, so the first
term is at most `L K E_{nu_N}[d]`. `square`

Three things follow, and they are the reason to prefer this statement.

**Contiguity is derived, not assumed.** The step `mu~_N <= K nu_N` is a pointwise
density bound obtained from the plan's feasibility and the parsimony cap; T1.1
then applies. Nothing asymptotic is used and no separate fidelity hypothesis is
carried.

**The theorem is quantitative.** There is no `-> 0` in the hypothesis and none in
the conclusion; the asymptotic statement is the corollary.

**The scheduling literature enters in the right place.** Bounded backlog, bounded
delay, queue stability and fair scheduling are exactly conditions under which a
feasible plan with small residual *exists* — a bounded-delay schedule gives one
supported within `delay` of the diagonal. They are not conditions under which
contiguity holds, and C1 is the proof: rotation has delay 1, backlog 1, and no
contiguity. Their role is to supply `(T1)`–`(T2)`; `(T3)` is a separate,
semantic obligation on the reason, and no scheduler supplies it.

Exactly checked in `tests/test_transfer.py::DeferredTransfer`: the rotation plan
is feasible with zero residual, its stability defect against the C1 array is
exactly `1` (so the theorem correctly refuses to conclude), and against a defect
constant on rotation blocks the stability defect is `0` and the bound holds.

## 5. The recommended interface

The Answerability-to-Progress interface is a **declared transport plan with
constants `(L, eps, K)` and a residual schedule**, not a contiguity assertion.
Contiguity is the right *characterization* — T1 and T2 make it exactly the class
of measure pairs for which blind transfer works — and the wrong *primitive*,
because it is not checkable at a finite horizon, not quantitative, and not
satisfied by service patterns the theory has no reason to forbid.

## 6. What this section does not establish

Contiguity here is the finite-index analogue of a standard notion for sequences
of measures; no result from that literature is used, cited or needed, and the two
proofs above are self-contained. T3 assumes the plan is *given*; whether one
exists is the affordability existence problem and is not answered here. `(T3)`'s
constants are a semantic claim about the reason, and this round supplies no
method for certifying them.
