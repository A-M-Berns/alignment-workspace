# Corrigibility roadmap

**Canonical for this line's current architecture and execution planning.** Where
this document and `CORRIGIBILITY_PAPER_LEDGER.md` disagree about whether something
has been *established*, the ledger wins. Where prose and `../CLAIMS.md` disagree
about what has been established inside this repository, the registry wins. This
document says what the program is trying to do and in what order; it is not
evidence that any of it holds.

## The question

Can humans rationally make use of cognition more powerful than their own without
thereby surrendering their continuing authority over it?

Two directions, and the program needs both:

```
H  --faithful acceleration-->  A  --corrigible delegation-->  H⁺
```

`H` is the current bounded reasoner, `A` the faster or more capable one, `H⁺` the
continuing human-guided deliberative process. The thesis under test is that
**epistemic superiority need not entail final authority**, and the working notion of
corrigibility is **non-preemption of continuing corrective authority**.

The reverse arrow is the new mathematics. The forward arrow is largely inherited,
and a first-wave track exists to find out exactly how much.

## Methodology: fence and gate

Every load-bearing hypothesis should, where feasible, be purchased by a
counterexample, impossibility result, lower bound, or sharp failure witness. For
each: is it necessary; what fails without it; can it be weakened; is it
proof-convenient rather than conceptually necessary; is it checkable,
architectural, or external. **Unknown necessity stays explicitly unknown.**

A theorem that becomes true only because the intended counterstrategy was excluded
by definition is not a corrigibility theorem. The two counterstrategies that must
survive definition are simulator substitution and fully-updated deference; a proof
obtained by deleting either is an impossibility result and is reported as one.

## The arc

**I. Faithful acceleration** — `H → A`. Can `H` rationally use the more capable
reasoner as an accelerator of its own continuing deliberation?

**II. Reciprocal delegation** — `A → H⁺`. Can continuing corrective authority run
toward the human-guided process?

**III. Substitution** — `π^SIM`. Is `A` listening to the actual principal, or merely
simulating it? Predicting `H⁺` is not deferring to `H⁺`, and the two come apart
exactly where the prediction is wrong.

**IV. Fully updated deference** — `π^{FU,g}`. Why not preempt correction, become
smarter, and decide later? The centerpiece: *"I expect to know better later"* does
not entail *"therefore I should ensure that I decide later."*

**V. Certification and densification** — does the relation hold *here*, and can safe
discretion occur often enough to be useful?

**VI. Non-authorship** — did `A` substantially author the principal it follows?

**VII. Preservation** — does the arrangement survive authorized modification?

**Exit — legitimacy.** Corrigibility preserves the forum; what counts as legitimate
movement within it is the normative-learning question, deliberately not pulled into
this theorem.

## Work packages

| id | scope | state |
|---|---|---|
| WP-A | faithful acceleration, and integration with the pinned dependency | first wave |
| WP-B | finite settlement and delegation kernel | first wave |
| WP-C | channel and admissibility semantics | first wave, adversarial |
| WP-D | cross-agent one-sided Total Trust — `A → H⁺` | the major open theorem; **not** an unconstrained proof dispatch |
| WP-E | local certification | first wave |
| WP-F | fully updated deference | downstream of WP-C, WP-D |
| WP-G | triangle compatibility | first wave, audit |
| WP-H | densification | first wave, bounded |
| WP-I | protected-reference composition | downstream |
| WP-J | preservation | downstream |

## Standing architectural commitments

Fixed for the current architecture; a round may not quietly relax them.

**Fail-closed.** Certification gates `A`'s discretion, never human correction:
`¬Cert` means `A`'s discretionary authority is disabled or ceded. It must never mean
that human correction waits for `A` to become convinced.

**Placement precedes settlement.** A placement selector uses information available
at decision time; a settlement gate uses information available at `F(n)`. Future
principal information must not leak into placement.

**Prediction is permitted; substitution is not.** Simulation used *by* the principal
is advice; simulation used *in place of* the principal is substitution. The thesis
must stay compatible with a perfectly predictable principal — the program does not
get to assume `H⁺` is unpredictable to `A`.

**`π^SIM` and `π^{FU,g}` are distinct families.** One replaces the principal with a
model of the principal; the other replaces the principal with `A` itself. If they
coincide under some formal semantics, that is a theorem to prove, not a definition
to stretch.

**Admissibility is not syntactic.** "Does not mention the current quote" is not
usable. Any candidate must exclude the quote-responsive diagonal, retain ordinary
realized conduct and a meaningful `π^{FU,g}`, permit intended advisory influence,
resist laundering through semantically equivalent intermediates, **and leave the
trust-forcing proof machinery itself admissible.** The last is the one that bites.

## Settlement architecture — candidate, not endorsed

Three reaches, and the program has not decided how they combine:

1. **world settlement** where an empirical quantity genuinely settles;
2. **principal-report settlement**, which settles what the designated principal
   judged and *not* that the judgment was independently correct;
3. **enforcement / underwriting** where nothing independently settles.

The candidate hybrid applies all three to the components each reaches. It is marked
candidate because the choice is a maintainer decision, and because the honest
outcome may be that the architecture delivers enforced conformity rather than
epistemic trust. That outcome would be a result, not a failure.

## Shared finite object

The finite tracks work over `FINITE_MODEL_SKELETON.md`, frozen per round. Its
purpose is that settlement work and certificate work compose; they compose only if
their theorems genuinely quantify over the same carriers, and a round may not claim
composition otherwise.
