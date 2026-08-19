# The deductive coherence region as a rational vertex list

What the day-`n` coherence region of a deductive stage is, computed rather than
assumed: the convex hull of the restrictions to a finite fragment of the
propositionally consistent worlds satisfying the stage.

Verdict: the deductive coherence region on a finite fragment is a computable finite rational vertex list — `admissiblePatterns` is a `def` that decides which `{0,1}` patterns extend to a propositionally consistent world satisfying the stage, sound and complete about worlds rather than atom assignments, nonempty exactly when the stage is propositionally satisfiable, and kernel-checked on instances including an unsatisfiable stage and a fragment whose two sentences constrain the same atom.

## What is here

One Lean file, `lean/Workspace/Normativity/Contrib/DeductiveRegion.lean`, in the
proof layer. Nothing else in the repository changes.

The region is delivered twice: as a finite list of rational vertices, and as a
predicate on price vectors that is the convex hull of those vertices.

## The decision procedure

A world is `LO.Propositional.Boolean.Valuation ℕ`, an assignment to countably
many atoms, and `PCWorld.Holds` is `Prop`-valued — there is no `Decidable`
instance for it and there cannot be a useful one. The search is therefore run on
Bool-valued atom tables, using the pinned dependency's `sentenceBool`,
`tableConsistent` and `boolPCWorld`, over the `2^k` assignments to the `k` atoms
occurring in the stage or the fragment. Brute force, exact rationals, no
`native_decide`.

Two constructions in the dependency were not reusable, both for the same reason —
they do not reduce in the Lean kernel, which the instances at the end of the file
require:

- `finiteAtomAssignments` indexes bit vectors by `Finset.sort`, which is
  `List.mergeSort`, whose well-founded recursion the kernel does not unfold.
  `contextList` filters a range instead, giving the same atoms in the same order.
- `AssessmentProcess.deductiveContext` is elaborated under `open Classical`, so
  its `Finset` operations carry classical decidability instances. `regionContext`
  spells the same set out with computable ones.

Neither is a defect in the dependency; both are consequences of code written for
elaboration rather than for kernel evaluation. They are recorded here because the
next round to want kernel-checked instances over the same types will meet them.

## Soundness and completeness are about worlds

A fragment coordinate is a sentence, not an atom, so two coordinates can
constrain the same atom and a `{0,1}` pattern can be unrealisable for that reason
alone, with no help from the stage. Stating both directions about `PCWorld`
rather than about atom assignments makes the extension step come out right
automatically. `region_fragment_shares_atom` displays the case: `[p, ∼p]` has four
patterns and admits two.

## What nonemptiness needs

Exactly that the stage is propositionally satisfiable — `∃ v : PCWorld,
v.ConsistentWith D`. Nothing about the fragment enters, and the file proves the
biconditional rather than the implication, so the hypothesis is shown to be the
exact one rather than merely sufficient.

## Kernel-checked instances

Five, all by `decide +kernel`: a worked stage with its two vertices; an
unsatisfiable stage with the empty list; a fragment whose sentences share an atom;
the same effect through an entailment; and an independent fragment where all
`2^{|Φ|}` patterns do appear, which is what shows the trimming is the fragment's
doing and not an artefact of the enumeration.

Stages in these instances are singletons. A `Finset Sentence` literal with two or
more elements goes through `insert`, hence through Foundation's `DecidableEq
Sentence`, which is built with `simp`-generated proof terms that do not reduce in
the kernel; an unsatisfiable single sentence `p ⋏ ∼p` exhibits the empty region
without needing one.

## What this does not establish

- **No claim is registered.** This is a proof-layer contribution and a round
  artifact. Whether it becomes a registered claim, and against which
  `PRIORITIES.md` item, is reserved to the maintainer.
- **It does not answer item 42.** That item asks for a row family whose region
  lies strictly between the affine relations and the coherence polytope, and
  whether one is polynomially presentable. This round supplies the vertex set that
  item's baseline is computed from, in Lean; the complexity question is untouched.
- **The enumerator is exponential and is not claimed otherwise.** `2^k` in the
  number of atoms the stage and fragment mention. No efficiency claim is made.
- **The region is defined from a stage `D : Finset Sentence`, not from a
  `DeductiveProcess` and a date.** Applying it at day `n` means passing `DP.D n`;
  no monotonicity in `n` is proved here, because nothing in the four required
  facts uses it.
- **`deductiveRegion_eq_convexHull` needs the fragment duplicate-free**; the other
  results do not, and do not assume it.
