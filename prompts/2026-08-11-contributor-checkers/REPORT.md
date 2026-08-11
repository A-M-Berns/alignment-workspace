# Round report — contributor-supplied checkers

**Attribution.** Prompt author: Claude Fable 5 (Anthropic), 2026-08-11.
Executor: Claude Opus 5 (Anthropic), 2026-08-11.

## The AGENTS.md change

The class ordering gains one term:

```
lean-proved > enumeration-verified > witness-checked >
contributor-checked > test-supported > conjectured
```

with the definition stated at the ordering, and the cap described as derived from
the invocation path rather than declared.

The rule that contributors never ship verifiers was replaced by the asymmetry it
was standing in for. Modifying a house checker is **retroactive** — every claim it
already certified silently re-inherits the change — so it stays gated. Adding a
checker for a new claim is **prospective and contained** — if it is wrong, the
only thing not established is that contributor's own claim — so it is labelled
instead. The section says why one is gated and the other is not, because the
distinction is the whole point and a reader who does not see it will read the
relaxation as a loosening.

Also added: the two promotion paths, and the standing guidance that new
verification logic should go to Lean, with its reason — on the Lean side the
kernel is the judge, so a contributor writes as much as they like with no
maintainer in the loop and no class penalty. The Python harness stays small
because growth pressure is routed to where the judge is free.

## The enforcement mechanism, and how it was tested

`checkers/registry.py` derives the ceiling from the statement of record. A
`checker` field beginning `contrib/` requires class exactly
`contributor-checked`, and the named module must exist under `checkers/contrib/`.
The reverse is also caught: a house checker declared `contributor-checked` fails,
so the class cannot be used to duck scrutiny in either direction.

**Negative test, run and now permanent.** Three cases against a temporary
repository with a contrib checker:

```
ok  declared witness-checked        -> FAIL  (expected FAIL)
      demo.claim: statement of record invokes the contributor-supplied checker
      'contrib/my_checker', so its class cannot be 'witness-checked' — the
      ceiling is 'contributor-checked'. The label is derived from the invocation
      path, not from what the pull request declares.
ok  declared enumeration-verified   -> FAIL  (expected FAIL)
ok  declared contributor-checked    -> PASS  (expected PASS)
```

These three are now cases in `python3 -m checkers.run --self-test`, which runs in
CI — so the cap is regression-tested rather than demonstrated once and trusted.
The self-test went from six cases to nine.

## Path-gate confirmation

```
SPEC   checkers/witness.py
proof  checkers/contrib/mine.py
SPEC   checkers/README.md
SPEC   AGENTS.md
proof  lean/Workstudio/Deference/Contrib/X.lean
```

Adding a contrib checker passes the gate for a non-maintainer; editing a house
checker still fails it. This needed a real change rather than a pattern tweak:
`checkers/contrib/**` sits **inside** a specification directory, so the gate now
gives proof patterns precedence over spec patterns instead of testing spec first.
Without that, `checkers/**` would have swallowed the new directory and the
relaxation would have been inert — a governance change that looks applied and
is not.

`CODEOWNERS` carries a matching entry with the reason.

## Hygiene

`tests/contrib_hygiene.py`, wired into the `checkers` CI job and the repo runner:
no third-party imports, a module docstring present, a top-level `check` function.
It says in its own docstring what it cannot check — whether the docstring is
*true* — which is precisely why the class exists.

One portability fix: the check used `sys.stdlib_module_names`, which is 3.10+,
and the maintainer's local interpreter is 3.9. It now falls back, so the gate
runs everywhere rather than only on the runner.

## Existing registry entries affected

**None**, as expected. The three entries in `projects/leverage/CLAIMS.md` are two
`lean-proved` and one `enumeration-verified`, all invoking house checkers or Lean
declarations. No class changed.

## Reserved — with a proposed answer

**May a `contributor-checked` claim satisfy an `OPEN_PROBLEMS.md` acceptance
criterion?**

Proposed: **yes by default, with the item free to say otherwise.** The reasoning
is that the alternative reintroduces the bottleneck this round removed — if items
can only be closed by house-checked or Lean-proved answers, a contributor with a
correct result waits on maintainer attention to have answered anything, which is
the situation the relaxation exists to end. Against that: an item closed by an
unread checker is an item whose closure nobody has verified, and the ledger would
show a problem as solved on the strength of logic no maintainer read.

The proposal splits the difference by putting it in the item: an item whose
acceptance check names a house checker or a Lean declaration already requires
one, because the acceptance check is *stated as something CI runs*. So the
default costs nothing where it matters and helps where it does not. **Not
decided — the maintainer's call.**

## What this round does not establish

The cap is mechanical, but the hygiene is not the same as review: a contributor
checker can be stdlib-only, exactly arithmetic, documented, and still wrong.
`contributor-checked` says exactly that and no more.

And the harness that now enforces all of this remains `llm-unreviewed` — the same
standing caveat, load-bearing again here, since the code deciding what class a
claim may carry is code no maintainer has read.
