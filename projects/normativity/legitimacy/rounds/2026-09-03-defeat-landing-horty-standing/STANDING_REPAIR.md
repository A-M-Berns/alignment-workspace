# The standing repair

## 1. The defect

PR79's Lean had

```lean
structure Licence (Q K Ty X : Type*) where
  lic : Q → K → Ty → X → Prop

def standsFor (Li : Licence Q K Ty X) (n : ℕ) (κ : K) (τ : Ty) (x : X) : Prop :=
  ∃ q ∈ T.O n, Li.lic q κ τ x
```

and D3's standing side read

```lean
contested : ∃ b, b ≠ T.resolver n q ∧ T.standsFor Li n (κ q') (τ q') (x q')
```

**`b` is bound and never used.** The body mentions `κ q'`, `τ q'`, `x q'` and no
participant, so the clause is equivalent to

```
(∃ b, b ≠ resolver n q)  ∧  standsFor Li n (κ q') (τ q') (x q')
```

and the first conjunct holds of any participant type with at least two elements. The
standing half of D3 was **vacuous**, and every laundering result in that round in fact
rested on `foreign_ground` alone.

`DEFEAT.md` §1 of that round says "some `b ≠ resolver` has standing on the successor",
which the Lean did not say. The prose and the formalization disagreed, and the round's
report did not flag it. That is the defect: not a false theorem — everything PR79
proved is true — but a definition weaker than its own documentation, with a laundering
claim resting on one clause while appearing to rest on two.

**Why the Python fixtures did not catch it.** They were not vacuous.
`DefeatModel.stands_for_other` reads the *opener* of each licence issue as its
standing-holder, so a participant was present in the executable model all along,
implicitly. The two models disagreed and only the Lean was wrong — which is a
reasonable argument for keeping both, and a caution about treating a passing fixture
suite as evidence about a Lean definition it does not mention.

## 2. The repair

```lean
structure Licence (Q A K Ty X : Type*) where
  lic : Q → A → K → Ty → X → Prop

def standsFor (Li : Licence Q A K Ty X) (n : ℕ) (b : A) (κ : K) (τ : Ty) (x : X) : Prop :=
  ∃ q ∈ T.O n, Li.lic q b κ τ x

contested : ∃ b, b ≠ T.resolver n q ∧ T.standsFor Li n b (κ q') (τ q') (x q')
```

The participant is carried through `AnchorStanding`, which now reads "a fresh issue's
protocol is licensed *for someone*":

```lean
AnchorStanding … : ∀ n q, q ∈ Born n → ∃ b, T.standsFor Li n b (κ q) (τ q) (x q)
```

and through `anchor_grounded`, whose conclusion gains the participant.

### What needed more than the type change

**Nothing did.** `Answerable`, `Disciplined`, `no_self_grounding`, and every §5.1–5.6
theorem re-elaborated under the type change alone. That is itself informative: it
confirms that no prior result was consuming `contested`, which is the same fact as the
defect. The declarations that changed type but not proof are `Licence`, `standsFor`,
`AnchorStanding`, `anchor_grounded`, `Answerable`, `Disciplined`, `no_self_grounding`.

## 3. Laundering, now on both sides

```lean
structure InOneHand … (a : A) (n : ℕ) (q : Q) (G) (q' : Q) : Prop where
  resolved     : T.resolver n q = a
  grounds_own  : ∀ p : Q, Sum.inl p ∈ G → T.opener p = a
  standing_own : ∀ b, T.standsFor Li n b (κ q') (τ q') (x q') → b = a
```

- **`not_in_one_hand_of_contested`** — an answerable disposal is in nobody's single
  hand, proved **from `contested` and nothing else**. This is the theorem the
  pre-repair definition could not state, let alone prove.
- **`no_laundering_walk`** — no nonempty chain of edges is in one hand, by the above at
  any edge.
- **`foreign_ground_dichotomy`** — what the grounds side actually gives, stated exactly
  rather than overstated: the foreign ground is either a **settlement fact** or an
  issue opened by somebody other than the resolver.

That last one is worth its own line, because it is why the standing clause is
load-bearing rather than belt-and-braces. `foreign_ground` reads

```lean
∃ g ∈ G, ∀ p : Q, g = Sum.inl p → T.opener p ≠ T.resolver n q
```

and a settlement ground `Sum.inr s` satisfies the inner implication **vacuously**. This
is the right semantics — a fact the world settled belongs to no participant, so it is
foreign to everyone, which is the settlement-independence hypothesis appearing in the
definition — but it means:

> **A disposal citing only settlement facts satisfies `foreign_ground` trivially.**
> Before the repair, such a disposal satisfied all of D3 with nobody contesting it.
> After the repair, `contested` is the only thing standing in its way.

So the repair does not merely tidy a binder. It closes a case: self-grounded-by-
settlement disposals, which the previous round's laundering theorem did not reach.

## 4. The principal-relative form — definition and one theorem

Stated because the coalition question is the author's and **stays in the queue**. This
is not the general non-capture predicate.

```lean
structure AnswerableFor … (P : A) … extends T.Answerable … where
  principal_stands : T.standsFor Li n P (κ q') (τ q') (x q')

theorem no_coalition_excluding_principal (hP : P ∉ C) (hA : AnswerableFor … P …) :
    ¬ (∀ b, T.standsFor Li n b (κ q') (τ q') (x q') → b ∈ C)
```

One line: `P` stands, so if every stander were in `C` then `P ∈ C`.

The two-participant alternating walk that defeats plain separation is defeated by
this — its coalition `{V, W}` does not contain `P`. What it costs is that the predicate
**names a party**, which is precisely the reservation in `DECISIONS.md`: a structural
condition quantifying over all coalitions is unsatisfiable at `C = A`, and the only
known repair is to exempt a designated principal.

## 5. Fixtures

Four, in `tests/test_standing.py`; PR79's 24 continue to pass unchanged.

| fixture | outcome |
| --- | --- |
| standing held only by the resolver, with a foreign ground | **refused**, `D3-uncontested` — the standing side doing work by itself |
| standing held by a second participant who opened every ground | **accepted** — the coalition case, unchanged, restated under the explicit licence type |
| `P` holds standing at every successor | **no coalition excluding `P`** — the P-relative theorem's positive case |
| `P`'s licence answered away before the second edge | **one edge excludes `P`**, while plain separation still accepts every edge |

The last pair is the point: `single_handed_edges()` is empty for **both**, and
`principal_holds_throughout("P")` separates them. The P-relative form is strictly
stronger, and the fixtures exhibit the gap rather than asserting it.

### A modelling bug found while writing them

The first version of `coalition_walks_excluding` read standing off the *live*
outstanding set, so a licence answered away later retroactively removed standing from
an edge that had it at the time — and the `principal_absent_from_one` fixture reported
two excluded edges instead of one. Standing is read **at the strict prefix of the
disposal's own batch**, matching the Lean's `standsFor Li n b`; the model now snapshots
it in `check_answerable`. Recorded because it is the same class of error as the defect
this document repairs: a quantity read at the wrong index, silently.
