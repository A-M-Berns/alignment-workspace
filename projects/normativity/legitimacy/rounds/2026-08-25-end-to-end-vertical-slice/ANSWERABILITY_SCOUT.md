# Theorem scout: answerable succession and cumulative liability

Status: **scout; unregistered.** Names provisional. One tightly scoped pass, not
a research round.

**Verdict: `ACCOUNTING-THEOREM-PROVED-LOCALLY`**, at Level I and
presentation-level, with the honest qualification in §7.

The question was whether the existing answerability structure already supports a
conservation theorem bounding `sum_t c_t`, rather than one obtained by showing
the per-date deficit falls — a route this round already closed, since a frozen
injunction's compilation moves with the mesh and `D_t` can rise under increasing
settlement.

It does. The proof is short once the carrier and the lemma are right, and the
content is in those two choices rather than in the algebra.

---

## 1. The carrier

**The live answerability episode of a force-bearing standing** — an `AnsRoot`,
not a `StandingId`.

Episode Uniqueness gives at most one current episode per standing, so while a
standing lives the two are interchangeable. They come apart exactly where it
matters. Supersession *terminates* one standing and *creates* another, so a
balance held on the standing has nothing to cross on; the root has
`succ_t(q) = { q' in MINT(a) | Disposes(a, q) }`, which is precisely the
relation "who is now answerable for what this episode was answerable for".

That is also why the answer is not a new object. RI already mints successor
roots at every disposition and already proves that every episode the record ends
is answered or visibly outstanding. The scout adds a number to an existing
carrier; it does not add a carrier.

## 2. The allocation lemma

The charge is computed from all active rows at once, so it is not additively
separable *a priori*. It is subadditive, which is enough:

```text
D(union_i G_i) = max_w sum_i sum_{j in G_i} d_j(w)
              <= sum_i max_w sum_{j in G_i} d_j(w)  =  sum_i D(G_i)
```

— a maximum of a sum is at most the sum of the maxima. With `eps_t`, `M_t` and
`delta_t` common to the date, `c_t <= sum_i alloc_t(i)` where `alloc_t(i)` is
the canonical charge of standing `i`'s **own** rows over the **joint** support
and the **joint** live worlds.

Each `alloc_t(i)` is therefore the charge of a real `ForceRequest` — same date,
same support, same assessment, a sub-presentation of the rows — and not a share
invented by an accounting convention. `test_answerability.py` checks the
covering inequality on every non-blocking case in the suite.

## 3. The local laws

Each is checkable at one normative event.

**L1 — charge coverage.** Force exercised at `t` is debited from the episodes
currently answerable for it. No row contributes to `c_t` while owned by no
episode.

**L2 — no laundering through succession.**

```text
sum_{q' in succ(q)} B_{t+1}(q')  <=  B_t(q) - (charge allocated to q) + grant
```

Splitting, merging and plain replacement are this one law; a successor of two
predecessors accumulates from both, and each application only releases what its
own predecessor held.

**L3 — no silent creation.** New capacity enters through the typed grant
channel `eta_t` and nowhere else. In the reference ledger there is no method
that raises a balance without recording a grant, so this is a property of the
type rather than a discipline.

**L4 — conservation under relabelling.** `applyEffect` is the identity on a
`Transfer`, and the successor episode differs only in its debtor, so transfer is
L2 with one successor and no grant. Conservation is inherited rather than
assumed.

**L5 — explicit discharge.** An episode ending with no successor releases its
allowance out of the system, and the transition is named in the log. The
accounting layer needs only that discharge happened through an allowed
transition; what may legitimately discharge liability is inquiry's question and
is not answered here.

## 4. The theorem

```text
Phi_t = sum over live episodes of B_t(e)

one step:      c_t + Phi_{t+1}  <=  Phi_t + eta_t
telescoping:   sum_{t<T} c_t + Phi_T  <=  Phi_0 + sum_{t<T} eta_t
hence:         Phi_0 < inf  and  sum_t eta_t < inf   ==>   sum_t c_t < inf
```

with the cleanest case `eta == 0`, under which `sum_t c_t <= Phi_0`
unconditionally.

Exercised rather than asserted. A driven run of the slice's own pipeline, three
dates, `Phi_0 = 40` and no grants during the run:

| `t` | `c_t` | `Phi_t` → `Phi_{t+1}` | holds |
|---|---|---|---|
| 0 | `101/20` | `40` → `699/20` | ✓ |
| 1 | `101/20` | `699/20` → `299/10` | ✓ |
| 2 | `101/20` | `299/10` → `497/20` | ✓ |

`sum c_t = 303/20` against the bound `40`. At `Phi_0 = 6` the first date is paid
and the rest are **withheld**: `sum c_t = 101/20`, still under the bound, the
demand still standing, no force emitted and no price produced.

## 5. Necessity

**Drop L2** and the theorem is false, with a witness that is semantically
inert: one force superseded by an *equivalent* successor at every date — the
same demand in force throughout — driving the cumulative charge to
`per-date × dates` while every individual date looks unremarkable. Under L2 the
same trajectory is capped by the initial allowance. Any accounting under which
this is free lets a source launder liability by renaming itself.

**Drop L3** and a fresh episode funds itself: eight dates of charge with
`granted == 0`, capacity having appeared with nothing recording it.

**L4** needs no separate witness because it is L2 at one successor.

## 6. Where the qualitative becomes quantitative

The reason multihypergraph carries **no weights**, and should not. The seam is
`MINT`:

```text
reasons  ->  Derivation  ->  NormEvent  ->  creates/supersedes force-bearing standing
                                        ->  MINT mints the answerability episode
                                                    |
                                            allowance lives here
                                                    |
                          kappa_t -> rows -> ForceRequest -> c_t is debited
```

Provenance and answerability stay qualitative up to the point where an event
mints an episode; the episode is where a number attaches; and traderization
supplies the number. Nothing above `MINT` acquires a weight, which is what keeps
the reason layer from becoming an accounting system.

## 7. What this is not, and the seam that limits it

**It is presentation-level.** `c_t` is a function of the compiled row
presentation, not of the semantic region, so allowance is spent against the
actual request. This round takes that as the honest first theorem rather than
canonicalising by fiat. One consequence is mildly reassuring: padding a
presentation with redundant rows raises `sum_i alloc_i` and drains the padder's
own allowance faster, so redundancy is self-punishing rather than a laundering
route. A **semantic-level** theorem would need a presentation-invariant
liability — plausibly a minimum over equivalent row systems — together with
attainment, computability, and an argument that a source may be held to the
minimum rather than to what it emitted. None of that is done here.

**`sum_t eta_t < inf` is a hypothesis, and a reader should see exactly what it
costs.** The theorem does not prove summability from nothing; it *reduces*
summability of an unbounded future charge stream to summability of an explicit
grant channel, plus local invariants checkable one event at a time. That
reduction is the content. It is not the rejected formulation "every source is
assigned enough budget to cover its future charges": nothing here inspects the
future, `Phi_0` is a fact about the seed, and the interesting case `eta == 0`
has no summability hypothesis at all.

**It says nothing about what happens next.** A system that exhausts its
allowance withholds force forever, which is safe and probably not what anyone
wants. Whether an answerable practice can *earn* new allowance — and what would
license a grant — is Level II and needs the inquiry loop.

## 8. The three levels, and the gap

```text
Level I    quantitative answerability invariants  ==>  sum_t c_t < inf
Level II   answerability + inquiry/revision       ==>  those invariants
Level III  legitimate normative learning          ==>  perpetual safe enforceability
```

Level I is this scout, at presentation level. The gap to Level II is now sharp
and is a question about **the grant channel**: `eta` is currently an
unexplained input, and Level II is exactly the claim that a practice which
answers for its outstanding liability generates grants whose total converges.
That is a statement about inquiry dynamics, and it has a typed target to aim at
rather than a vague one — which is the point of doing the scout first.

## 9. What the future inquiry layer may read

Computed, typed, and none of it a reason:

```text
B_t(e)                     remaining allowance on a live episode
Phi_t                      total outstanding allowance
alloc_t(i)                 what each force-bearing standing cost this date
the grant log              every unit of capacity, with the reason given for it
successors' inheritance    a successor arriving with substantial outstanding liability
withheld-force events      a date on which standing stood and nothing moved
```

Preserved:

```text
liability pressure != inquiry != reason != NormEvent
```

`Std_t` moves only through `applyEffect` on a well-formed `Norm` step, so a low
balance cannot become a normative change without an event.

## 10. What this scout does not establish

- No Lean, no registered claim. The one-step inequality and the telescoping are
  checked on driven finite runs; the covering lemma is one line of algebra and
  is checked on every non-blocking case in the suite, not proved in general.
- The laws are shown **sufficient** for the bound and **necessary** in the sense
  that dropping either L2 or L3 admits a divergent witness. No claim is made
  that they are the weakest sufficient laws.
- The allocation charges each standing its solo deficit, which over-covers.
  Whether a tighter allocation — a Shapley-style split of the joint deficit, say
  — is both well defined and answerable is untouched.
- Nothing here connects a grant to any normative act. `grant` takes a reason
  string that nothing checks.
- The reference ledger is not wired into `pipeline.run_day`; it is driven
  alongside it by `run_accounted`. Making it part of the pipeline would mean
  deciding what mints an allowance, which is Level II.
