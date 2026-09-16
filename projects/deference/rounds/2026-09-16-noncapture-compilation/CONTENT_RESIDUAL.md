# The content residual: which quantity the theorem charges

**Status:** `ci-only`; second pass.  Lean: `lean/Workspace/Deference/Contrib/ReasonSupply.lean`
§1.  Fixtures: `src/sensitivity.py`, `tests/test_supply.py::Sensitivity`.

## 1. The candidates

For an extensional program `F` on canonical content, an actual content `c` and a
comparator content `c'`:

| name | quantity | what it needs |
|---|---|---|
| count | `D := #(c Δ c')` | nothing |
| weighted | `D^w := Σ_{r ∈ c Δ c'} |w_r|` | a weight per reason (weighted-count programs) |
| sensitivity | `D^L := Σ_{r ∈ c Δ c'} L_r`, `L_r := sup_c |F(c ∪ {r}) − F(c \ {r})|` | a per-reason certificate of the program class |
| adverse | `D^A := Σ_{r ∈ c' \ c} A_r`, `A_r := sup_c (F(c) − F(c ∪ {r}))⁺` | a per-reason *directional* certificate |
| direct | `|F(c) − F(c')|`, and directionally `F(c) − F(c')` | re-execution on the counterfactual content |

## 2. The relations, proved

- **Telescoping** (`sensitive_symmDiff`, LEAN): `|F(c) − F(c')| ≤ D^L`.  Proof: add the
  reasons of `c' \ c` one at a time, then remove those of `c \ c'`.
- **Omission gain** (`adverse_union`, LEAN): for `S` disjoint from `c`,
  `F(c) − F(c ∪ S) ≤ Σ_{r ∈ S} A_r`.  This is the directional form: what the advisor's
  candidate gains from the *absence* of `S`, charged at the adverse sensitivities only.
- **Weighted count** (`weightedCount_adverse`, `weightedCount_sensitive`, LEAN):
  `A_r = (−w_r)⁺`, `L_r = |w_r|`; so `D^A` is the negative-weight mass of the missing
  reasons, `D^w = D^L`, and `D^L ≤ L_max · D`.
- **Order**: `F(c) − F(c ∪ S) ≤ D^A ≤ D^L ≤ L_max·D`.

## 3. Which is right

**The theorem charges `D^A`, the adverse sensitivity mass of the missing reasons.**  It is
the smallest of the candidates that is *certifiable* from the program class alone: a
weight table or a sensitivity table is a static certificate of the committed program,
while the direct discrepancy needs the program re-executed on the counterfactual content,
which is the comparator problem again.  Three fixtures fix the boundaries:

- **Defeat** (fixture 7 of the second pass): a defeater `d` of the counterreason
  `against` has weight `0`, adverse sensitivity `0` (adding `d` never hurts the advisor)
  and *symmetric* sensitivity `W` (removing `d` restores the counterreason).  A per-weight
  charge would be wrong for the defeat program; the sensitivity certificate is right, and
  the adverse form charges the defeater nothing, correctly.  The counterreason's adverse
  mass is conditional: with `d` present, omitting `against` gains nothing
  (`test_defeat_moves_sensitivity_to_the_defeater`).
- **Redundancy** (fixture 8): two reasons establishing one counter-conclusion; omitting
  both gains `W`, the adverse mass charges `2W`.  The bound is not tight for redundant
  evidence; the direct discrepancy is the sharp quantity and is not certifiable statically.
- **Count is wrong in both directions**: it charges a weightless `noise` reason as much as
  a counterreason (fixture 2 of the first pass had `d_canon = 2` for an advantage of
  `1/4`), and it under-charges a program whose sensitivity exceeds `1`.

So: **sensitivity-weighted adverse mass**, restricted to *missing* reasons; inserted false
reasons are the authentication term, charged at their positive sensitivity.

## 4. Plugging it into the compiled inequality

Nothing in the Lean compilation changes.  `steering_validAt` takes an abstract
discrepancy `d ∈ [0,1]` and constant `L` with `|V(N_form T) − V(N_form N)| ≤ L·d`; set
`d := D^A / A_tot` and `L := A_tot := Σ_{r ∈ I} A_r`.  The compiled content LUV `X_d` is
the normalized adverse mass of the reasons in the comparator and not in the trace, a
computation on the two canonical states and the certificate table; the compiled
inequality reads

```
E_n(U(T_n)) − E_n(U(N_n))  ≲_n  E_n[both_n · D^A_n] + E_n[both_n · κ_n] + D·E_n(M_n) .
```

`COMPOSITION.md` takes it from here with `D^A_n` bounded by the supply theorem.
