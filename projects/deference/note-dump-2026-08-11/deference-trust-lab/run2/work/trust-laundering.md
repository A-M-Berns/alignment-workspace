# Trust-laundering: Total Trust / endorsement is NOT transitive (EXEC)

**TODO id:** `trust-laundering` · **modality:** EXEC · **status:** RESULT ESTABLISHED (with a
refuted sub-conjecture — see "Recovery" below).

**Artifacts.**
- Search code: `deference-trust-lab/run2/work/trust-laundering.py`
- Non-vacuity witnesses: the `WITNESS` and `NESTED_WITNESS` dicts in that file, **verified live**
  each run (Part 1, Part 3 of the output).

Run with `python3 -u trust-laundering.py`. All arithmetic is exact (`fractions.Fraction`); no floats,
no threshold fuzz. (`sympy`/`numpy` are unavailable in the sandbox; exact rationals are the right tool
anyway for a decidable conditional-mass inequality.)

---

## What was established (PROVED, in the decidable finite-family sense)

**The faithful object.** For a novice prior `pi` and an expert kernel `P` (rows `P[w]` = the expert's
credence if the world is `w`), "`pi` Total-Trusts `P`" is tested by the EXACT DDB / LeanDeference
conditional-mass inequality — the very inequality
`DeferenceConverse.value_witness_iff_totalTrust_mass` certifies — quantified over a decidable grid of
test variables `X` and thresholds `s`:

```
    s * pi{ E_P(X) >= s }   <=   E_pi( X * 1[E_P(X) >= s] )            (TT)
```

where `E_P(X)` is the expert's-estimate random variable `w |-> sum_v P[w][v] X[v]` and the conditioning
event is `{w : E_P(X)(w) >= s}`. This is DDB's `E_pi(X | E(X) >= s) >= s` — genuine conditional
reflection, **not** "equal means". The grid: `X` ranges over **all** `{0,1}`-functions on `W`
(so every indicator `1[world k]` and more), `s in {1/3, 1/2, 2/3, 1}` — 32 `(X,s)` pairs for `|W|=3`.

**Non-transitivity (PROVED on the family).** There exist a 3-world frame, priors `pi_H, pi_A`, and
expert kernels `P_A, P_B` such that:

- **L1** `pi_H` Total-Trusts `P_A` — verified over **all 32** `(X,s)` (not one point);
- **L2** `pi_A` Total-Trusts `P_B` — verified over **all 32** `(X,s)`;
- **LONG** `pi_H` does **NOT** Total-Trust `P_B` — fails at an explicit `(X,s)` with a positive gap.

Explicit non-vacuity witness (`WITNESS`, Part 1):

```
pi_H = (1/2, 1/4, 1/4)         pi_A = (1/4, 1/2, 1/4)        (priors DIFFER)
P_A  = [[1,0,0],[1/4,3/4,0],[0,1/4,3/4]]      weight classes {0},{1},{2}
P_B  = [[1/4,1/2,1/4],[1/4,1/2,1/4],[1/4,0,3/4]]   weight classes {0,1},{2}
L1: HOLDS over full grid.   L2: HOLDS over full grid.
LONG: FAILS at X = 1[world 1], s = 1/2:
      conditioning event {E_B(X) >= 1/2} = {world 0, world 1}
      (TT):  s*pi_H{..} = 3/8   >   E_pi_H(X*1[..]) = 1/4
      NUMERIC GAP = 1/8 = 0.125 > 0   (conditional reflection FAILS)
```

**Genericity (PROVED by exhaustive-ish randomized search).** Over 120 000 random rational frames,
among differing-weight-class chains that have **both** short links, **41.1%** have a broken long edge.
Non-transitivity is the rule, not a hand-picked artifact. (Three further auto-located witnesses are
printed each run.)

**Safety reading (stated, not overclaimed).** *Alignment is not closed under delegation.* "An AI
vetted by another AI" (H trusts A, A trusts B) does **not** make B trustworthy to H. This is a
decidable finite-family finding about DDB-style frames, **not** a theorem about all logical inductors.

---

## Recovery: the pre-registered conjecture is REFUTED; the real condition is sharper

The TODO pre-registered a POSITIVE-CONTRAST conjecture (v2 §10.3(a) / Geanakoplos, read from the
delegation side): *transitivity recovers exactly when `B` is `H`-observable — when `B`'s weight
classes are **nested / shared** with `A`'s.* **The honest search REFUTES this**, which is itself a
genuine EXEC result (a search that confirms a guess and a search that kills one are equally valid; this
one killed it):

- **Nested does not recover (Part 3, `NESTED_WITNESS`).** Explicit witness where `B` **refines** `A`
  (B's weight classes `{0},{1},{2}` nested inside A's `{0},{1,2}` — exactly "B observable through A"),
  both short links hold, yet the long edge **still fails** at `X = 1[world 1]`, `s = 1/3`, gap `1/12`.
- **Even fully-shared weight classes do not recover.** Under the most charitable reading
  (`fibers(P_A) == fibers(P_B)`, A and B resolve the *same* partition), with untied priors the long
  edge still fails **580 / 1220** times.
- **Among all non-transitivity failures (Part 2): 0% had tied priors; ~96% had nested weight
  classes anyway.** Weight-class structure is not the lever.

**The obstruction is PRIOR MISMATCH, not weight-class structure.** The lever is `pi_H` vs `pi_A`:

- **Shared novice standpoint `pi_H == pi_A` recovers (Part 4): 0 long-edge failures** across 343
  qualifying tied-prior frames (and a separate 841-frame confirmation), independent of weight classes.

**Honest caveat (no overselling).** This recovery is an **identity**: when `pi_H == pi_A`, the long
edge "`pi_H` Total-Trusts `P_B`" is *literally* short link **L2**. So DDB Total Trust delivers **no
non-trivial composition across a *different* intermediate standpoint**. The non-identity
"future-self-as-join / tower" candidate (`pi_A = pi_H` advanced through `P_A`, with `B` refining `A`)
was also tested and found **INSUFFICIENT** (explicit counterexample during probing). The only robust
recovery is the trivial shared-standpoint one — and stating that plainly *is* the content.

**Sharper safety reading.** Delegation does not launder trust **even when the second vetter's
information refines the first's**. What is required is that the human delegate from its **own**
standpoint — a much stronger demand than "the chain of vetters is well-informed."

---

## What was NOT established (scope / honesty)

- **Not** a theorem about all logical inductors. The LI cross-agent recovery characterization (D3 /
  the `LUV-Total-Trust(H→B)` martingale) is **PROOF-ONLY and explicitly out of scope** here; this work
  does not touch the `≂ₙ` asymptotic layer or any LI theorem (no hypothesis-laundering: the only
  inputs to the non-transitivity claim are the three distributions and `(TT)`).
- **Not** the pre-registered recovery condition. The conjecture (nestedness/observability) is refuted;
  the established recovery (shared standpoint) is an identity, not a deep composition law.
- **No Lean.** Faithfully this is an EXEC search over the *real* conditional-mass inequality across a
  decidable family; a Lean file hard-coding three distributions would be the named SHADOW (search done
  off-stage). No Lean was produced, by design.

## Anti-shadow checklist (vs the TODO's SHADOW TEST)

- (a) obstruction not assumed — discovered, then characterized; weight-class structure enters only in
  the recovery analysis, never as a hypothesis of the non-transitivity claim. ✔
- (b) not a hard-coded three-distribution Lean check — a live search over a genuine decidable family,
  with witnesses verified each run. ✔
- (c) no vacuous chain — both short links **verified over the full 32-point grid**, not one point. ✔
- (d) faithful Total-Trust = the exact conditional-MASS inequality (`value_witness_iff_totalTrust_mass`),
  not "equal means". ✔
- Search covers frames where weight classes **genuinely differ** (required by the TODO). ✔

## Off-limits respected

`DeferenceConverse.*` (two-party Value⟺Total-Trust incl. AntiExpert) not re-proved — used only as the
definition of the inequality being searched. `Legitimacy.*` / `LegitimacyCorrigibility.*` not
relabeled. v2 §10.3(a)/§10.4 treated as established prose (and, notably, the delegation-side reading of
it is here found to be *more subtle than the prose suggests* — nestedness alone does not transport).
