# The discovery residual, stated precisely

**Status:** `ci-only`; third pass.  Lean: `lean/Workspace/Deference/Contrib/ReasonDiscovery.lean`
§1.  Fixtures: `src/inquiry.py`, `tests/test_discovery.py::Residual`.

## 1. The three failures that are not discovery

At occurrence `n` with declared interface `I_n`, a true reason can be missing from the
principal's trace because

1. it is in `I_n`, true, and **nobody put it on the docket in time** — the discovery
   residual;
2. its **type is not in `I_n`** — ontology incompleteness;
3. its type is in `I_n` but **at a granularity that cannot carry the distinction** —
   representation failure.

Only (1) is treated here.  (2) and (3) are outside the consumer theorem and stay outside:
the theorem is relative to a declared reason representation, and no
"interface-incompleteness mass" is introduced, because no object of the declared
representation measures it (`DISCOVERY_COUNTERMODELS.md` rows 18, 19).  The existing
name for the hypothesis this residual quantifies is the wiki's "Open coverage hypothesis
that relevant latent reasons become due" (`wiki/Glossary.md`, eventual route coverage);
the discovery residual is its quantitative form on the deference side.

## 2. The quantity

Let `Truth_n ⊆ I_n` be the true declared reasons, `Disc_n ⊆ Truth_n` the reasons on the
docket before the service problem runs, and `V` the committed program's verdict for the
advisor's candidate.  The advisor supplies its own pro reasons; discovery concerns the
**adverse** reasons, those whose presence can lower the candidate's verdict (the
program is antitone in them given the pro content; `Inquiry.is_antitone`).

```
DiscoveryLoss_n  :=  V(Disc_n) − V(Truth_n)             (the omission gain of the undiscovered)
                 ≤  Σ_{r ∈ Truth_n \ Disc_n} A_{r | Disc_n}    (adverseAbove_union, LEAN)
```

where the **conditional adverse sensitivity above the docket** is

```
A_{r|D}  :=  sup_{c ⊇ D, r ∉ c} ( V(c) − V(c ∪ {r}) )⁺ .
```

The direct omission gain is the type-correct residual: it is what enters the steering
inequality's content term when the comparator is the full trace.  The conditional mass
is its certificate.  Both are needed, for different reasons.

## 3. Why conditional, not additive

The second pass showed static per-reason weights misdescribe defeat-sensitive programs,
and that every static certificate is loose under redundancy.  The conditional form
repairs the part of this that matters for discovery:

- **Defeat.**  A counterreason `c` defeated by the advisor's defeater `e` has
  `A_{c|∅} = W` and `A_{c|{e}} = 0` (`test_conditional_mass_is_the_right_quantity_under_defeat`).
  Once `e` is on the docket, `c` is no longer an inquiry obligation.  Conversely a
  defeater `d` of the advisor's pro reason has positive conditional adverse mass the
  moment the pro reason is on the docket: discovering a reason creates a defeater
  obligation (`DISCOVERY_COUNTERMODELS.md` row 7).
- **Redundancy.**  Two reasons establishing one counter-conclusion have `A_{r₂|∅} = W`
  and `A_{r₂|{r₁}} = 0` (`test_redundancy_conditional_mass_vanishes_after_one`); the
  additive mass double-counts, the conditional mass does not once one is found.
- **What stays loose.**  Before either redundant reason is found, the conditional mass
  of the pair is `2W` for a gain of `W`.  The direct gain is sharp; the certificate is a
  bound.  This is the same boundary as in `CONTENT_RESIDUAL.md` §3, and it is why the
  obstruction theorem is stated for the direct gain (`cellGap`) and the frontier theorem
  for the certificate.

## 4. The frontier

The **frontier** of a docket `D` in a cell `K` of consistent worlds is the set of reasons
undetermined in `K` (true in some world of `K`, false in another) with `A_{r|D} > 0`
(`Inquiry.frontier`).  **Frontier theorem** (`residual_le_zero_of_frontier_empty`, LEAN):
if every undiscovered true reason has conditional adverse mass `0` above `D`, the
residual is `≤ 0`.  Contrapositively, whenever the residual on some consistent world is
positive, an undiscovered reason of positive conditional adverse mass is named: that is
the **explicit inquiry obligation** the dispatch asked for, in the form

> unresolved reason of positive conditional adverse mass ⇒ a named inquiry obligation.

Discovery is therefore **closed under live defeaters** in exactly this sense: the
obligations are the frontier, the frontier is recomputed from the docket and the
program, and it is empty iff no consistent world can still hold a gain.  Under a finite
declared interface the process terminates: each discovery strictly grows `D` and `D ⊆ I_n`.

## 5. Which discovery target is needed

| target | needed? | why |
|---|---|---|
| full discovery (every true declared reason) | no | reasons of zero conditional adverse mass are irrelevant to the advisor's candidate |
| adverse-mass discovery (`Σ A_r` small) | sufficient, coarse | double-counts redundancy; ignores the docket |
| **decision-sufficient** (`V(Disc) − V(Truth) ≤ β`) | **the theorem's object** | it is literally the content term against `N_full` |
| defeat-closed (frontier empty) | sufficient for `β = 0` | the frontier theorem |
| certificate-relative (`Σ A_{r|D} ≤ β`) | **the certifiable form** | what a program class certifies statically; what `li_noncapture` consumes |

The weakest useful notion is decision-sufficient discovery, certified through the
conditional adverse mass of the frontier.

## 6. Stages, and what is charged where

```
candidate generation → inquiry → truth determination → authentication → docket → service → trace
```

- **Discovery** covers candidate generation, inquiry and truth determination: a reason is
  *discovered* when its truth is determined by the evidence (it is in the certain docket
  of the current cell).
- **Authentication** is the engine certifying a determined reason; a served reason that
  fails it is the authentication residual (second pass), not a discovery failure.
- **Service** starts at the docket: a discovered reason released too late for the
  supplier to route it before commitment is a *service* failure (its release is on the
  docket), not a discovery failure.  Row 13 of the countermodels sits on this boundary:
  "discoverable but not before commitment" is discovery when the *inquiry* budget runs
  out, service when the reason is docketed and the *supplier's* capacity does.

No failure is charged twice: the decomposition `Miss = discovery + service +
authentication` of the second pass is by stage, and this pass only refines the first
term.
