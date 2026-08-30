# Composition with settled Normative Continuity

## Current PR71 state

The input to this pass is the corrected PR71 head, not its first draft:

* a bare \(Q\times Z\to\Omega_h\) is not a locality certificate;
* `(CFP)` certifies only that the exterior strategy is held fixed;
* the follow-up added a protected world observation \(p_R\) and `(BL)`;
* Exact NCSS uses the post-transition defect
  \(Active_{n+1}(c)\land\neg Rep_{n+1}(c)\land
  \neg\exists R\,Adeq_{n+1}(R,c)\);
* local closure adequacy constrains a proposed terminal resolution; Continuity supplies
  exact outstanding-set evolution and fresh successor carry.

This pass keeps the Exact NCSS relevance repair and weakens the interpretation of `(BL)`
as described in `LOCALITY_RESPONSE_STRUCTURE.md`.

## Dependency diagram

```text
Permit / authorization provenance
                 |
                 v
 typed PE certificate on (S, exercise, S')
   |              |                 |
   |              |                 +--> joint-liability feasibility
   |              +--> Met rising-edge witness
   +--> discharge or semantic burden transport
                         |
                         v
 existing Continuity: exact evolution, resolution discipline,
                      fresh successors, ancestry
                         |
                         v
             Answerability Conservation / Exact NCSS
                         |
          (not supplied by anything above)
                         v
        Progress, exercise fairness, repair fairness
```

Authorization, semantic soundness, structural carry, eventual progress, and joint
feasibility are therefore separate theorem layers.

## Coverage resolution as a PE instance

For a post-state live criticism burden

\[
b_{\sigma,c}:=Active_{n+1}(c)\land\neg Rep_{n+1}(c),
\]

`PE^resolve_coverage` checks the proposed resolution certificate and authenticated
post-state.  It may:

* discharge this coverage-to-registration burden by `Rep`, or by an authorized
  disposition;
* carry it to one or more live successor carriers, whose implementation certificate may
  exhibit an adequate route.

An adequate route alone is not a terminal discharge of an ongoing entitlement.  It
shows implementation quality while the burden remains carried.  This distinction
sharpens the old `CloseAdequate` wording: the predicate is best regarded as an instance
of `PE^resolve`, with terminal discharge and nonterminal carry kept separate.

### Exact NCSS as a corollary

Assume at transition \(n\to n+1\):

1. \(m_\sigma\) has a live structural carrier at \(n\);
2. \(c\) has the exact post-state defect
   \(Active_{n+1}(c)\land\neg Rep_{n+1}(c)\land
   \neg\exists R\,Adeq_{n+1}(R,c)\);
3. there is no authorized disposition of \(c\);
4. the proposed closure has a sound `PE^resolve_coverage` certificate;
5. settled Continuity's resolution/successor and exact evolution assumptions hold.

The burden cannot be soundly discharged by (2)–(3).  PE therefore requires transport to
a live successor carrier.  Continuity installs/preserves that carrier.  Hence

\[
m_\sigma\text{ remains live at }n+1
\quad\land\quad
\neg Implements_{n+1}(\sigma).
\]

The second conjunct is definitional from the exact defect; the non-silent survival of an
authenticated semantic burden is the compositional content.  This is local soundness
plus diachronic structure, not “assume NCSS inside `Resolve`.”

Removing any load-bearing premise has the known small countermodel: no post relevance
makes implementation vacuously true; registration or a replacement route removes the
defect; disposition permits closure; unsound PE permits bogus closure; absent Continuity
the carrier can silently vanish.

## No changes to Continuity

Settled Continuity may retain abstract `Permit`, `Resolve`, `Continue`, and persistent
`Met`.  PE is a realization/refinement layer for their semantic use, while the existing
theorem remains the structural engine.  Prerequisite inquiry likewise needs no second
lifecycle: an inquiry issue remains on the ordinary route, and a witness-backed
`PE^met` rising edge discharges its existing prerequisite.

Nothing here supplies fairness or Progress.  A live repair burden may persist forever;
Answerability Conservation says it cannot receive a bogus semantic exit, not that it is
eventually handled.
