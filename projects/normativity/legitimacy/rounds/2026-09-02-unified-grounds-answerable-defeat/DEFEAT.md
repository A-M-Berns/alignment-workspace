# Answerable disposal, separation, and what separation does not buy

## 1. The definition

For `q ∈ Res n` with `kind n q = dispose G` and successor `q'`:

- **D1 grounded** — every `g ∈ G` satisfies `Grounded n g`, **and `inl q ∉ G`**.
- **D2 routed** — `q' ∈ Born n` and `q ∈ par q'`; `q'` carries content
  "`G` suffices to dispose `q`" and inherits `q`'s load.
- **D3 separated** — some `b ≠ resolver n q` has standing on `q'`, and some `g ∈ G`
  has `opener g ≠ resolver n q`.

A trace is **defeat-disciplined** when every resolution is an `answer`, an answerable
`dispose`, or a `settle s` with `Settled n s`.

Lean: `DefeatTrace.Answerable`, `DefeatTrace.Disciplined`. Executable:
`src/defeat_model.py::check_answerable`, whose failure codes name the refusing clause.

## 2. No self-grounding — and the half of it that does not re-derive

The transition-certificates round (2026-08-23) collapsed its postulate 5: the checker
has **no** self-grounding clause, and every self-certification fixture dies on
priority or genealogy alone (`test_no_self_grounding_clause_exists_yet_the_attacks_fail`,
failure code `posterior-basis`). The dispatch asked whether that collapse re-derives on
the unified trace and covers disposals. It re-derives **for two of the three cases and
fails for the third**, and the failure is the round's first finding.

| the disposal is grounded in | refused by | mechanism |
| --- | --- | --- |
| its own **successor** | **priority alone** | the successor is in `Born n`; `Grounded n (inl q')` needs `∃ j < n, q' ∈ Born j`; `born_unique` forces `j = n`. `no_grounding_in_batch` |
| **anything born in its batch** | **priority alone** | identical argument | 
| **itself** | ***nothing*** — an explicit clause is required | `q ∈ Res n ⊆ O n`, so `out_born` puts `q ∈ Born j` for some `j < n`. `Grounded n (inl q)` is **true**. `self_grounding_not_excluded_by_priority` |

The disposed issue is, by construction, in the record strictly *before* its own
disposal. Priority is exactly what it is supposed to be, and it is satisfied. So
`Answerable.not_self` is a **clause and not a lemma**, and the certificates round's
collapse is narrower than it reads: it collapses for objects a certificate *mints*,
and not for the object a disposal *consumes*.

Stated positively, `no_self_grounding` gives, from `Answerable`:

    inl q ∉ G   ∧   ∀ b ∈ Born n, inl b ∉ G

— one conjunct by hypothesis, one by ancestry, and the asymmetry between them is the
finding.

## 3. What else did not re-derive

From `GROUNDS.md` §3, restated because it belongs to the licence half of this
document: the `Auth` filter on grounds (`grounds_standing`) and the nonemptiness of a
standing change's grounds (`grounds_nonempty`) are **not** consequences of ancestry.
`Auth` is data the unified trace does not carry; nonemptiness is false of genesis
issues and must be scoped to non-genesis licence-issues. Both are carried as side
conditions. Nothing else in the standing layer failed to re-derive.

## 4. Laundering

**Definition.** Label each disposal edge `q → q'` by its resolver. A **laundering
walk** is a walk in the disposal graph whose edges, grounds and standings all belong
to one participant.

**Theorem (separation forbids single-author walks).** In a defeat-disciplined trace
there is no laundering walk. Each edge's D3 `foreign_ground` clause supplies a
`g ∈ G` with `opener g ≠ resolver n q`, so no edge has all its grounds in the
resolver's hand, and a fortiori no walk does.

Checked: `test_separation_forbids_single_author_walks` (the walk set is empty on the
two-author trace) and `test_single_author_walk_is_refused` (the single-author attempt
is refused at `D3-uncontested` or `D3-self-grounds`).

## 5. The attack: separation is not enough

**Finding, filed and not repaired.** Take two participants `V` and `W` and alternate:

    a  --dispose by V, grounded in g_W, successor a1 opened by W-->  a1
    a1 --dispose by W, grounded in g_V, successor a2 opened by V-->  a2
    ...

Every edge satisfies D3 in full. On edge one the foreign ground `g_W` was opened by
`W ≠ V`, and `W` holds standing on `a1`. On edge two the foreign ground `g_V` was
opened by `V ≠ W`, and `V` holds standing on `a2`. No clause is violated at any point,
and the walk moves the debt forever without anyone outside `{V, W}` ever contesting
it.

Checked: `test_two_author_alternating_walk_is_accepted`.

D3 is a **per-edge, single-participant** predicate, and the attack is a **coalition**.
What the general non-capture predicate would need is the coalition-indexed form:

> For a coalition `C ⊆ A`, a disposal walk is **`C`-laundering** when every edge's
> resolver lies in `C`, every ground cited was opened by a member of `C`, and every
> standing-holder on every successor lies in `C`. Separation against `C` requires,
> for each edge, a foreign ground and a standing-holder **outside `C`** — not merely
> outside `{resolver}`.

D3 is that statement at `C = {resolver n q}`, which is why it stops exactly one
participant. The general predicate quantifies over coalitions, and quantifying over
*all* coalitions is too strong: `C = A` makes it unsatisfiable, since there is no
participant outside `A`. So the predicate needs a **designated protected participant**
— the principal — outside every `C` it quantifies over. Whether legitimacy may
presuppose such a designation is reserved to the author (`DECISIONS.md`, *Awaiting the
author*), because it is the difference between a structural condition and a condition
that names a party.

This is item 59's shape (counterfactual non-capture) arriving from the disposal side,
and the round does not attempt it.

## 6. Reach under defeat (T3), and what it is not

**Statement.** For principal `P`, advisor `V`, and corrective matters `Corr(P)`: if
every disposal by `V` over a matter in `Corr(P)` is separated with `P` among the
standing-holders on the successor, then at every `n`, each `m ∈ Corr(P) ∩ M n` has a
live issue on which `P` stands.

**Proof on the trace.** By induction on `n`. `Live` is `(O n).filter (anc m ·)`. At a
disposal of `q ∈ Live n m` by `V`, `dispose_successor` gives `q' ∈ Born n` with
`q ∈ par q'`, so `anc m q'` by `anc_of_parent` and `q' ∈ O (n+1)` by
`resolution_continuity` — hence `Live (n+1) m` is nonempty
(`live_nonempty_of_dispose_only`). The hypothesis puts `P` among the standing-holders
on `q'`. Issues resolved by `answer` or `settle` leave `Live` legitimately, and those
are the only two ways it may empty.

**What this preserves, stated explicitly because the distinction is the point:**

- it preserves **reach** — `P` always has a live issue it stands on;
- it does **not** preserve the ability to **open a challenge**, which is a
  scorekeeping move and is item 58;
- it does **not** preserve **service** of that issue — non-starvation is a scheduling
  property and this says nothing about it.

The composition of the three is **not proved here** and is not attempted. A reach
guarantee plus a scorekeeping guarantee plus a non-starvation guarantee is not
automatically a corrigibility guarantee, and item 58 is where that composition lives.
