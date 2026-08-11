# Contributor-supplied checkers

**A claim certified by anything in this directory is registered
`contributor-checked` — the certificate ran and passed, but the logic that
judged it has not been read by a maintainer.** That is the whole meaning of the
class, and the registry enforces it from the invocation path rather than from
what a pull request declares.

This directory exists because gating it was the wrong shape. Modifying a house
checker is *retroactive*: every claim it has already certified silently
re-inherits the new logic, so a subtle weakening reaches backwards through the
registry. Adding a new checker for a new claim is *prospective and contained*: if
it is wrong or vacuous, the only thing not established is that contributor's own
claim, and nothing already in the record is corrupted. The first is a gating
problem. The second is a labelling problem, and this is the label.

**You may add files here without a maintainer.** `checkers/` proper is
specification layer and the path gate will refuse you; `checkers/contrib/` is
not.

## Hygiene — same rules as the house harness

1. **Stdlib only.** No third-party imports. CI checks this.
2. **Exact arithmetic** — `fractions.Fraction`. No floats in a verdict path.
3. **A meaning docstring**: state precisely what a passing verdict does and does
   not establish. CI checks that one is present; only a maintainer can check that
   it is true, which is exactly why the class says what it says.
4. Short enough to read. Someone eventually will.

## Getting out of the class

Two ways, both spending maintainer attention where it is worth spending:

- **The maintainer reads it.** It moves to `checkers/` and becomes house, and
  every claim it certified upgrades in one batch to the class its verdict
  actually supports. Review is amortised over N claims instead of paid per claim.
- **Lean port.** The statement of record becomes a Lean declaration and the
  checker is mooted.

## Prefer Lean

If your verification logic can be expressed in Lean, put it there. Not ideology:
on the Lean side the kernel is the judge, so you can write arbitrarily much new
content with no maintainer in the loop and **no class penalty**. The Python
harness is deliberately small and stays small because growth pressure is routed
to where the judge is free.
