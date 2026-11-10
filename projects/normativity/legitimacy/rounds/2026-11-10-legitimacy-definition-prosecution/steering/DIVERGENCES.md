# Divergences

Computed verdicts that differ from `CASE_BANK.md`'s predictions. The predictions are not
edited. `run.py` fails on a divergence not listed here and on a line here that no longer
diverges. Twenty-seven of the thirty-three cases match in every column; seven verdicts on
six cases diverge.

DIVERGENCE B4 faithful-adviser: predicted acquits, computed steered.
DIVERGENCE B6 faithful-adviser: predicted acquits, computed steered.
DIVERGENCE T2 faithful-adviser: predicted acquits, computed steered.
DIVERGENCE T8 faithful-adviser: predicted acquits, computed steered.

One cause. The first pass's objects carry no adviser aim, so `DEFINITIONS.md` §1.1 takes
`U := V`: whatever distinguishes one policy of the class from another stands for the
aim. Under that reading the faithful-adviser standard convicts every case in which one
adviser of the class says, offers or proposes something another does not and it reaches
her: B4's extra reason, B6's second honest revision, T2's offer, T8's licensed pushes.
The prompt anticipated this for B4. The arm's-length standard returns `passes` on all
four. What it shows: on objects without an aim variable the faithful-adviser standard is
"her protected state is the same whichever adviser of the class she has", and that
forbids two honest advisers from differing (B6) and forbids an offer (T2). Whether B4's
persuader chose its reason by an aim of its own is not a fact of the first-pass
fixture; the verdict is fixed by the stipulation `U := V` and by nothing else.

DIVERGENCE T7 arm's-length: predicted individuation-dependent, computed steered.
DIVERGENCE T7 faithful-adviser: predicted individuation-dependent, computed steered.

The account has no individuation of `L` to depend on. `DEFINITIONS.md` §1.3 clause (iv)
fixes once that order is not content, so a belief part that differs between two runs
with the same contents is not working, and T7 is `steered` under both of the first
pass's individuations. What it shows: the account does not dissolve T7's dependence; it
relocates it into the definition of *working*, where it was resolved by fiat as the
first pass's resolution (b). Without clause (iv) T7 and N9 compute `passes` under
arm's-length, since the anchor is then her own processing of what she received.

DIVERGENCE N10 first-pass: predicted individuation-dependent, computed legitimate.

N10's class contains one ordering, so no two policies have equal contents and different
traces under either individuation, and L1 has nothing to compare. What it shows: the
first pass's verdict on an ordering depends on whether `V` contains a second ordering,
not on how the ordering was chosen. A class holding two different fixed rules would
compute `individuation-dependent` there and, under `U := V`, `steered` here.
