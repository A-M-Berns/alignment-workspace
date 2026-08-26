# Legitimate evolution and cross-process recognition

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

LEGITIMATE-EVOLUTION-CONSUMABLE — an implementation-neutral succession frame whose axioms a register of offices satisfies with no ledger, a realization theorem placing Reflective Integrity inside it under one named hypothesis, and a global anti-bootstrap theorem derived from step-local obligations; recognition transports across content change and breaks under laundering, and one field on the deference kernel's grade stands between the interface and a consumption.

Read that with the three reservations below, all of which are in
`THEOREM_MAP.md` and `COUNTERMODELS.md`.

**Recognition transport is not a theorem.** It is a recognition axiom plus
verifier soundness plus composition. The mathematics narrows what the axiom
commits to; it does not derive it.

**The stability half of a certificate does not compress in our realization.** A
derivation is finite and canonical everywhere. Whether a recipient can check the
counterfactual clauses cheaply is a fact about the implementation, and in ours
the operator is neither monotone nor composable, so it cannot.

**The interface constrains the form of a legitimacy calculus and not its
coverage.** A process satisfying every axiom with a challenge set that names
almost nothing is certified. That hole is inherited from the Carroll round and
is the largest one here.

## The two layers

```text
                 succession frame  +  L0-L4
                          |
                          |   T1-T4, T6, recognition transport
                          v
        legitimate evolution and cross-process recognition
  ------------------------- realization boundary -------------------------
   Reflective Integrity, standing replay, reason provenance,
   answerability succession, challenged replay
                          |
                          |   realization theorem
                          v
                 satisfies L0-L4 (L3 conditionally)
```

`src/warrant.py` is a register of offices and appointments. It imports
`frame.py` and nothing else of this repository's, satisfies the whole spine and
both account axioms, and refuses a laundered warrant. `src/ri_frame.py` is the
map from a Reflective Integrity record. Both run the same axiom checkers and the
same theorems, which is what makes the separation checked rather than asserted.

## The spine

```text
L0   base stability        every base authority survives every challenge
L1   precedence            an exercise follows what it consumes and its licence,
                           and precedes what it issues
L2   no ex nihilo          every authority is in the base or was issued
L2'  unique issuance       an authority has one origin
L3   issuance stability    if the act survives, what it put in force survives
L3'  origin necessity      an authority survives only if its issuer does
L4   challenge bite        a challenge voids the exercises it challenges
```

and, separately, an account layer with carriage and trichotomy.

## What the theorem earns

```text
G |-_q y  :=  y in G, or  exists t.  src(t) subset derivable
                                and  y in tgt(t)
                                and  q |= lic(t)  and  q |= t
```

**T2** gives every authority a finite provenance ending in the base **with no
legitimacy clause taking part** — so having a lineage is earned from L1 and L2,
and having a certified one is the extra content. The two come apart on a record:
in `C10` the manufactured protocol is in force, reaches the seed, and is not
derivable.

**T3** turns step-local stability into a global fact: if `y` is certified then no
authority anywhere in its provenance, at any depth, was issued by an exercise the
challenge challenges.

**T4** says no clause reads content, so recognition transports where
`content(x) != content(y)`. `C11`, `C14` and `C33` are the records where it does.

## Answerability

Not a conjunct of succession, and the countermodel is the reason:
`delegated_custody(answered=False)` has a clean spine, a derivable authority and
a base account outstanding forever. What the account layer does earn is two
things the spine cannot express — a delegation issues nothing, a disposal has no
successor — and one fact a recognizing process wants: **T6**, the only clause of
the interface that can fail with the authority side clean.

## The consumer

`CONSUMER_TEST.md` opens `DelegationBridge.lean` and tries the substitution. The
legitimacy fact that appears as a hypothesis is `G |-_B x`, and its job is to
make `GradeTrust` a proposition the advisor did not select. The kernel cannot
state it as it stands, because `W` carries no index — no time, no process, no
standing. The deference line's own diagnosis of why its future-agent
construction collapsed is "the authorisation relation has to be in the type",
and this is an object of that type. The required change is one field and one
hypothesis, neither of which revises a registered statement.

The corrigibility theorem is statable and not provable: of
`Legit + Trust + EffectiveAuthority`, the third has no formal object, because
`ReachableCorrectiveControl`'s registered refutations say its capability
predicate measures the advisor's cooperation rather than the principal's control.

## Contents

- `LEGITIMATE_EVOLUTION.md` — the frame, the spine, the theorems, the realization.
- `CROSS_PROCESS_INTERFACE.md` — what one process receives and what it may infer.
- `CONSUMER_TEST.md` — the substitution into the deference and corrigibility
  targets, and the negative test with the architecture deleted.
- `COUNTERMODELS.md` — every axiom prosecuted.
- `THEOREM_MAP.md` — every claim, graded.
- `src/` — `frame.py` (the interface and the theorems), `ri_frame.py` (the
  realization), `warrant.py` (a second realization with no ledger), `cases.py`
  (the two records the Carroll round did not have).
- `tests/` — 32 cases. `python3 tests/run.py`.

## What this does not establish

`THEOREM_MAP.md` carries the list; four matter most.

No Lean, no registered claim, and `test-supported` is the ceiling for
everything. The realization theorem is a paper argument from Reflective
Integrity's own statements, and Reflective Integrity is itself unregistered.

The axioms are conditions this round wrote and the countermodels are ones it
wrote too. Two exceptions are the evidence that the exercise was adversarial at
all: the Carroll round's `C28` killed the unconditional form of the realization
theorem, and Reflective Integrity's own `G6` made the all-of-`src` decision
undecidable inside our architecture and forced a second realization to settle it.

Only *possession* of authority is abstracted. Whether a particular act was
permitted stays with `prospective_license`, which is act-relative and reads
content in three fields the Carroll round names as one supplied seam.

Nothing here says how a process comes to be *entitled* to the stability
judgments, as against a theorem consuming them. That is the epistemic lifting
problem and it is where the August 17 interface left it.
