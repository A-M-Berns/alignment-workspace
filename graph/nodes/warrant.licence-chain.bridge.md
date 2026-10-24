---
id: warrant.licence-chain.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 2
author: "@smithy-verity"
---
## Statement
The claim asserts a chain of three standings for an announced verdict: licensed implies supported implies admissible. The declaration certifies, for a record state at one step, that a verdict licensed there (supported on the record's survivors by a certificate whose cited rows are live, and issued by an authorized event) is supported on the record's grounds under its docket and settlement, and admissible, that is, attained by some point of the settled region. The gaps: the first arrow is the definition of Licensed read back (Licensed is Supported plus authorization), so the content of the chain is the second arrow alone, Supported → Admissible by rational convexity of the settled region (`region_convex`, through `supportedOn_admissibleOn`), not by any projection; the chain holds at one record state and says nothing about transport across a record transition (item 115); the authorization clause is carried and not used; and the two converses fail, as the round's countermodels `admissible_not_supported` and `supported_not_licensed` show, which the claim's wording does not state.

## Source
projects/normativity/CLAIMS.md, entry `warrant.licence-chain` (class lean-proved, status active, origin round 2026-10-20-warrant-enforcement-semantics; answers item 56).
Documentation: verification: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md; context: projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md.
The definitions of Admissible, Supported and Licensed and the theorems `supported_admissible` and `licence_chain` in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean; wiki/Normative-Inductor.md, Entitlement, not licence; read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).
