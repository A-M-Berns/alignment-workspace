# Answerability Conservation

## Statement

Fix a matter (m), an anchored semantic slice (Ain L), and a finite trace interval
starting at (n_0). Assume:

1. at (n_0), accumulated satisfaction, disposition, and current carrier loads join to
   (A);
2. every semantic change to a carrier is covered by a valid SDT certificate;
3. each nonterminal certificate satisfies Transfer Soundness and Completeness;
4. satisfaction receipts are sound and disposition receipts are authorized;
5. receipts persist;
6. the structural trace satisfies exact outstanding evolution, fresh successors, and
   matter ancestry from settled Continuity.

Then at every later (n),

\[
A=Sat_{[n_0,n]}(m)\vee Disp_{[n_0,n]}(m)
  \vee\bigvee_{q\in C_n(m)}\lambda_n(m,q).
\tag{AC-invariant}
\]

Therefore either the anchored slice has a complete certified terminal account, or the
current carrier frontier is nonempty and connected to the initial realization by a
composed valid Transfer history.

## Proof

Induct over batches. Unaffected outstanding carriers retain their load. For every
affected carrier family, `(TC)` replaces its incoming join by exactly the join of sound
terminal receipts and successor loads. Join associativity, commutativity, and idempotence
permit splitting, merging, and redundant carriers without changing the total. Receipts
are accumulated monotonically. Settled exact evolution preserves unresolved unaffected
carriers; fresh-successor ancestry places every certified child in
(Live_{n+1}(m)). Thus substitution preserves `(AC-invariant)`. If the unresolved join is
nonzero, at least one live issue has nonzero load and belongs to (C_n(m)). If it is zero,
the receipts join to (A). ∎

The executable finite-set model checks every one-parent split of a two-atom load: 256
choices of two successor loads, satisfaction, and disposition. Every accepted local
certificate preserves the invariant.

## What is substantive

The semantic contribution is the authenticated denotation, component soundness,
collective completeness, and terminal receipt validity. These prevent a fresh issue,
renaming, or duplicate half-load from masquerading as carry.

Continuity contributes the structural fact that unresolved carriers cannot vanish except
through resolution and that certified fresh successors are current descendants of the
same matter. It does not prove the semantic equation.

The induction and frontier flattening are bookkeeping. The theorem is nevertheless not
a restatement of Continuity: a trace with a live bogus successor satisfies every
structural requirement and falsifies `(AC-invariant)`. Conversely, semantic link tables
without exact outstanding evolution can name a successor that never becomes a live
carrier. Both layers are load-bearing.

The theorem is safety, not Progress. It allows an unchanged carrier to remain unresolved
forever and says nothing about attention, exercise, truth, or eventual terminal exit.

## Dependency diagram

```text
anchored semantic denotation A(m)
        |
        | semantic: sound Satisfy / authorized Dispose /
        |           sound + collectively complete Transfer
        v
matter-indexed load allocation on affected parent/successor sets
        |
        | structural: accepted Resolve + exact O evolution + fresh successors
        v
matter ancestry and Live_n(m)
        |
        | semantic derivation: nonzero loads select C_n(m) subset Live_n(m)
        v
composed current carrier frontier or complete terminal receipts
        |
        v
Answerability Conservation
```

Liability/underwriting is absent. It constrains aggregate supportability of concurrent
normative force; this theorem accounts for the identity and disposition of one inherited
semantic slice. The only commonality is that both may be transition certificates under
the prose umbrella “Proper Exercise.” No common conservation theorem was found.
