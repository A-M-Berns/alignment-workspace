# Definitions

All new names are provisional.

## 1. Minimal substrate

The structural substrate is the existing `DefeatTrace Q D S A`. No universal event sum is needed. Its prefix-indexed `O`, `Res`, `Born`, immutable `par`, resolution `kind`, participants, grounds, settlement view, and trace laws are enough to prove identity-level fates. An application may encode events, but the theorem reads only these projections.

Content requires one additional object per admitted anchored slice. For a join-semilattice with bottom:

```text
SliceLedger(T,L) =
  lam : Nat -> Q -> L       -- current issue load
  sat : Nat -> L            -- accumulated answer receipts
  stl : Nat -> L            -- accumulated closure receipts
```

The slice's birth, immutable denotation, and admission certificate remain application data. The theorem begins at its birth prefix with an initial account equation. This refines the anchored-slices ledger by replacing terminal `Disposition` with carried `dispose`, as required by the landed Defeat Principle.

## 2. Internal closure judgment

```text
Closes : Nat -> S -> Q -> Prop
```

`T.Settled n s` says that authenticated item `s` is available through the settlement boundary. `Closes n s q` is the reasoner's separate, prefix-relative judgment that `s` suffices to close `q` under the rules in force at `n`. A terminal settlement step must exhibit both, plus the immutable resolution record `T.kind n q = settle s`.

`Closes` is not derived from `Settled`. Its certificate should be an append-only event citing a finite strict-prefix basis and a prior licence. The generic Lean theorem takes `Closes` as a predicate and requires the certificate as a field; it does not certify the application-specific rules deciding it.

If cognition later rejects a closure rationale, the old settlement item and old resolution stay fixed. A fresh reconsideration obligation cites the old closure event and the defeating grounds. If the old normative load is owed again, its fresh slice or successor explicitly carries that load. Reopening is prospective; it does not mutate the terminal token.

## 3. Transition-local content discipline

Verbatim Lean-facing definition:

```text
LocalConservation(Closes,n) iff
  identity_frame:
    forall q in O_n \ Res_n, lam_(n+1)(q) = lam_n(q);
  incoming_sound:
    forall q' in Born_n,
      lam_(n+1)(q') <= join { lam_n(p) | p in par(q') };
  carry_complete:
    forall p in Res_n with kind_n(p) = dispose(G),
      lam_n(p) <= join { lam_(n+1)(q') | q' in Born_n, p in par(q') };
  closure_certificate:
    forall p in Res_n with kind_n(p) = settle(s) for some s,
      exists s, kind_n(p) = settle(s) and Settled_n(s) and Closes(n,s,p);
  sat_(n+1) = sat_n join
      join { lam_n(p) | p in Res_n, kind_n(p) = answer };
  stl_(n+1) = stl_n join
      join { lam_n(p) | p in Res_n, kind_n(p) = settle(s) for some s }.
```

`incoming_sound` blocks accretion attributed to an old slice. `carry_complete` blocks weakening at disposal. Together they allow splitting, merging, overlap, and representation changes only through load comparisons in the stable anchored domain. Semantic authentication and order reflection are what justify those comparisons; they remain ambient assumptions.

## 4. Segment and endpoint forms

Verbatim definition:

```text
Integrity(Lambda,Closes,a,b) iff
  forall i, a <= i < b -> LocalConservation(Lambda,Closes,i).
```

The proof-relevant primitive is this segment certificate. A consumer may define

```text
H_a <=_leg H_b iff there exists a segment from H_a to H_b carrying Integrity.
```

Composition requires exact agreement on the shared prefix state, ledger, anchored domain, and `Closes` interpretation. Reflexivity and concatenation then hold. Antisymmetry, thinness, and uniqueness of witnesses do not follow.

## 5. Immutable and evolving data

Immutable: event identity and birth index; parents; cited grounds and licences; resolver/opener; resolution kind; anchored slice denotation and birth; certificate basis; settlement receipt identity and arrival. These are the constitutive data required for replay.

May evolve prospectively: outstanding status; standing; applicable rule versions; current representations; carrier allocation; `Closes` judgments; and the set of admitted slices. Evolution creates events, versions, successors, or fresh slices. An authenticated bridge may change representation while preserving the anchored order; it does not change the anchor.

Strict pre-state citation, constitutive immutability, and answerability continuation compress provenance, authority, replayability, and anti-laundering at the record layer. They do not imply semantic carry. The one-clause `hollow` model separates them.
