# Composition and cumulative erosion

## Faithful composition

Authenticated Transfer composition from PR73 remains valid for semantic
equations. Adequacy composes only when:

1. every era map is an order embedding on its admissible
   slice-relative quotient;
2. the quotients implement one anchored relevance commitment rather than
   unrelated era-local notions of relevance;
3. intermediate targets and contexts agree or have an authenticated
   order-isomorphism;
4. the comparison is made in the same stable anchored slice domain.

Two maps can each be faithful relative to their own quotient while their
composition is meaningless because one era declares a formerly relevant
distinction irrelevant. Quotient compatibility is therefore separate from
local order reflection.

## Stable anchor and erosion

Consider many eras. If each admissible quotient embeds order-reflectingly into
the same \(L_\alpha\), and each transfer commutes there, a distinction protected
at slice birth has distinct anchored images at every era. No finite sequence of
locally valid steps can gradually collapse it.

The stable codomain alone does not achieve this: lossy maps may all land in the
same codomain. The combination of stable anchor, fixed relevance commitment,
and order reflection blocks cumulative erosion. A proposed later quotient that
forgets a protected distinction fails adequacy at the first forgetting step.

This is a finite-prefix result. It needs no eventual-response or Progress
assumption.
