# Fully repaired Slice-wise Answerability Conservation

Fix matter \(m\), slice \(\alpha\) born at \(n_0\), and anchored denotation
\(A(m,\alpha)\). Assume:

1. authenticated and grounded admission at \(n_0\), with complete initial
   allocation;
2. for every prefix transition, generalized Transfer accounting covers every
   structurally or semantically changed carrier load for this slice;
3. every carrier outside the affected batch obeys the identity frame;
4. every affected post load and translation is semantically authenticated;
5. terminal Satisfaction is sound and every Disposition is authorized;
6. the trace satisfies settled Continuity.

Then for every \(n\ge n_0\),

\[
A(m,\alpha)=Sat_{\le n}(m,\alpha)\vee
Disp_{\le n}(m,\alpha)\vee
\bigvee_{q\in C_n(m,\alpha)}\lambda_n(m,\alpha,q).
\tag{SAC+}
\]

## Proof

Admission gives the base equation. At a transition, partition the old and new
carrier allocations into the generalized affected batch and its complement.
The identity frame gives equal joins on the complement. Generalized Transfer
replaces the old affected join with terminal receipts and the new affected
join. Finite associativity, commutativity, and idempotence reassemble the
global equation. Authentication makes every term an equation in the same slice
domain. Continuity supplies only which issues persist, are born, or are
resolved, plus matter ancestry and absorbing closure; it never supplies load
equality.

The persistent \(a\mapsto0\) countermodel violates assumption 2 or 3. The proof
never infers semantic persistence from structural membership in both
outstanding sets.

This repair generalizes PR72's resolution-batch Transfer rather than adding a
second semantic-edit lifecycle. No settled Continuity surgery is required.
