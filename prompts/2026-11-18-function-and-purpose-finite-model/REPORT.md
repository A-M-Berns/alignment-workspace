# Report — function and purpose in a finite model

**Attribution.** Prompt author: the maintainer (no model). Executor: Claude Fable 5.2
(Anthropic). Dispatched 2026-11-18; this report 2026-11-19. Write scope: granted by
message 22 of the dispatch.

**Verdict.** MODEL-BUILT-NOTHING-REGISTERED. The round's results are in
`projects/naturalized-agency/rounds/2026-11-18-function-and-purpose-finite-model/README.md`
and are not restated here. Every component is **open**.

## What was done

- Read the sources listed at the end of the round's README. The Condensation paper,
  the Cartesian Frames paper through Claim 52 with three sequence posts, the
  Mindermann–Armstrong paper's main text, both Dennett papers, the organisational
  account's core sections and the two chemistry formalisms' definitions and main
  theorems were read directly. Flint's "The ground of optimization" and Richens and
  Everitt, arXiv:2402.10877, were read through a fetching subagent's report, the former
  without its last section, the latter without its Section 4 and proofs; neither is
  relied on by a statement in the README.
- Built the model of README §§1–6 and its 47 tests.

## Corrections to the dispatch

Message 1 relays a reading of the Condensation paper marked there as unverified. Read
against the paper:

- Corollary 5.10 does not conclude that one model's top latent is nearly determined by
  the other's. It bounds `H(Y_{⊇A} | Z_G)` where `G` is the sets containing all but
  `k − 1` elements of `A`; the paper prints "`n − 1`", which the polar of the
  `k`-subsets of `A` shows should be `k − 1`.
- By Corollary 4.6 and Theorem 4.9, in a perfect condensation every latent `Y_A` is a
  function of each single `X_i` with `i ∈ A`.
- The comparison theorems compare two latent variable models of one joint
  distribution.
- The guess that the lattice of latents matches the subagent relation: under the
  embedding of a frame with a distribution on its agent as a random variable model
  indexed by its environment, restricting the index set is `Assume`, a sub-environment
  operation.

## Deviations

- Message 1 proposes a first step with a controller observed across situations and two
  condensation models of it. That was not done. Messages 7 and 8 redirected the round
  to function and purpose by role and self-maintenance, and the model built is of that.
- Message 9 says a thermostat's function is bestowed from elsewhere; message 14 drops
  that as a separate category. The model follows message 14: a thermostat maintained by
  a whole it serves is ascribed a function on the same terms as an organ.
- The verdicts of message 14 on aims (a bacterium and a trained model within a task
  have one, a thermostat perhaps not) are not tested: §4 has one regulator, and
  no system in §3 carries a policy.

## Names introduced, all provisional

The line `naturalized-agency`; *self-maintaining set*, *necessity*, *relevance*,
*influence*, *kind*, *ascribed a function*, *splitting theorem*, *regulator*, *gain*,
*aim*, *strength*, *admissible target*, *independence* (`ρ`), *serve*, *defect*.

## What this does not establish

The README's *What is not shown* governs. In addition: the dispatch asks for an
objectivity theorem for the intentional stance. Statement 4.2 compares two priors for
one policy over one outcome space and one target class, and the splitting theorem
relates one description to a refinement constructed from it. Neither compares two
descriptions arrived at separately, and nothing here attributes information or belief.

## Not yet done in this pull request

1. No node, source or want is filed in `graph/`. The dispatch states wants in the
   maintainer's words (messages 1, 2, 3, 19); filing them needs his one-word priority
   for each.
2. No `ATTENTION.md` item is filed for the residual questions the README's *What is not
   shown* lists.
3. `state/concepts.json` and `state/vocabulary.json` are unchanged.

## Outstanding maintainer actions

1. Give a one-word priority for each want to be filed from messages 1, 2, 3 and 19, so
   that item 1 above can be completed.
