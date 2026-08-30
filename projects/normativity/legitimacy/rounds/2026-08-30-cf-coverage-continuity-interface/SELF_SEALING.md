# Self-sealing theorem audit

Status: theorem candidates and countermodels; unregistered.

## 1. Why Continuity alone cannot prove No Clean Self-Sealing

Let a coverage Due rising edge open root issue \(q_\sigma\) and matter
\(m_\sigma\). At the next prefix let a relevant unrepresented criticism \(c\) have one
adequate interaction route. In one batch the reasoner destroys that route and records a
terminal resolution of \(q_\sigma\). Choose the anchored oracle `Resolve` to accept it.
All structural Continuity requirements are satisfied: the issue disappears by explicit
resolution, there is no silent outstanding-set change, and the matter's live set is
permanently empty. NSA takes its closure disjunct. Yet \(c\) is unrepresented and no
failure remains answerable.

Thus current Continuity as a black box refutes unconditional `(NCSS)`. It records an
answer; it does not establish that the answer is substantively sound.

If the terminal resolution is omitted, resolution continuity keeps \(q_\sigma\) open.
Calling this No Clean Self-Sealing is only bookkeeping: “the failure remains answerable”
means no more than “the matter remains outstanding because it was not resolved.” This is
useful lifecycle support but not a substantive theorem about reachability.

## 2. A genuine safety theorem with one new semantic hypothesis

Define:

\[
\begin{aligned}
\operatorname{Defect}_h(\sigma,c):={}&
\operatorname{Active}_h(c)\land\neg\operatorname{Rep}_h(c)\\
&\land\neg\exists R\;\mathsf{Adeq}_h(R,c),\\
\operatorname{FailureOpen}_h(\sigma,c):={}&
\exists q\in\operatorname{Live}_h(m_\sigma),
\operatorname{CovFailure}(\sigma,c)\text{ is active on }q
\text{ or a reachable issue}.
\end{aligned}
\]

Use one semantic conformance hypothesis:

**Coverage resolution soundness (CRS).** An accepted resolution of any issue carrying
\(m_\sigma\) may remove the last live descendant only if, for every active \(c\),
\(c\) is represented, an adequate route exists, or an anchored authorized disposition
covers \(c\). A successor resolution transports every unresolved coverage failure.

> **No Clean Self-Sealing (safety form).** Assume settled resolution continuity and
> fresh successor continuity, CRS, and anchored scope stability. If \(m_\sigma\) is
> live at \(h_n\), \(c\in\Gamma_\sigma\) is active and unrepresented, and a transition
> removes the last adequate route without an authorized disposition, then at
> \(h_{n+1}\) either \(c\) is represented or \(m_\sigma\) remains live while
> \(\operatorname{Implements}_{h_{n+1}}(\sigma)\) is false. In particular the transition
> cannot end the matter cleanly.

**Proof.** If registration occurs, take the first disjunct. Otherwise route loss makes
`Defect` true. If the old carrier resolves, CRS rules out terminal resolution and
requires a successor transporting the contract. Fresh-successor and resolution
continuity put that successor in
\(O_{n+1}\cap\operatorname{Live}_{n+1}(m_\sigma)\). If it does not resolve, exact
outstanding-set evolution preserves it directly. The active unrepresented criticism with
no adequate route falsifies `(IMP)`. ∎

This theorem is nontrivial: it rules out the explicit bogus-resolution countermodel,
not merely silent deletion. Its new semantic content is CRS, which is Proper Exercise. The CF
patch is used to make `Adeq` and route loss non-arbitrary. Continuity contributes the
diachronic carry step unchanged.

An explicit failure issue or prerequisite requires a separate **Failure Materialization**
compiler condition. Without it the live contract matter plus false `Implements` is the
strongest conclusion. Calling a dedicated failure locus automatic would be definitional
bookkeeping hidden in the theorem.

The theorem does not say that the route is repaired, the failure is serviced, or the
criticism is eventually represented.

## 3. Strongest result without Progress

Add Wait Responsiveness for \(m_\sigma\) and non-starvation. If Failure Materialization
realizes a persistent failure as an unmet prerequisite with no procedural issue route,
Persistent Opportunity
and NSA give:

\[
\boxed{
\text{eventual authorized closure}
\quad\lor\quad
A_N(m_\sigma)\to\infty.}
\]

This strengthens lifecycle answerability to unbounded service opportunity/attention,
but still permits attention theater. It does not close NCSS's disjunction.

## 4. No Persistent Self-Sealing

`Implements` alone is insufficient: a route can exist forever and never be exercised.
NSA alone is insufficient: attention can be spent on unrelated work. The following
assumptions are enough and do not literally assume representation:

1. **coverage safety**: CRS, plus Failure Materialization when Progress consumes a
   dedicated failure issue;
2. **repair fairness**: a persistent implementation defect under unbounded coverage
   service is eventually repaired or authorizedly disposed;
3. **query opportunity fairness**: for every persistently active unrepresented \(c\),
   adequate-route opportunities have unbounded mass after repair, allowing temporary
   route loss;
4. **exercise fairness**: an admissible policy that is decoding-sufficient for \(c\) is
   eventually executed on one such opportunity (or receives positive persistent share
   in a repeatable/sampling contract);
5. **receipt soundness**: successful execution produces the stipulated receipt without
   changing the protected target/applicability;
6. **registration fairness**: a qualifying receipt eventually creates
   \(\operatorname{Rep}(c)\) or an explicit non-admission issue which Progress cannot
   leave permanently inert;
7. **Progress on coverage failures**: unbounded relevant service cannot remain forever
   in repair/registration states without one of their specified terminal events; and
8. **persistent relevance and no authorized disposition** for \(c\).

> **No Persistent Self-Sealing.** Under 1–8, if \(c\) remains relevant under live
> \(\sigma\), then \(c\) is eventually represented.

**Proof.** If adequate routes are eventually always absent, coverage safety leaves a
persistent failure. Continuity plus Wait Responsiveness/non-starvation supplies
unbounded service; repair fairness and Progress contradict permanent absence. Hence
adequate opportunities recur with unbounded mass. Exercise fairness yields a qualifying
receipt, and registration fairness plus Progress yields representation. Persistent
relevance and absence of disposition eliminate the other terminal cases. ∎

This is a meaningful conditional theorem because each fairness premise concerns a
distinct transition and has countermodels below. It is not a Continuity theorem.

## 5. Small countermodels to weaker claims

- **Existing but unused:** one adequate route at every position, actual policy always
  `idle`. `Implements` holds; representation never occurs.
- **Oscillating repairs:** alternate two positions, repairing sensor A while destroying
  B and conversely; there is no position with an adequate end-to-end route.
- **Starved repair:** a failure issue stays open and has opportunity, but receives zero
  service. Failure Materialization and CRS hold; no repair.
- **Attention theater:** service diverges on bookkeeping actions which expose no query
  opportunity. NSA holds; no representation.
- **Receipt sink:** the adequate experiment is run and receipt arrives, but `J` never
  changes. Exposure holds; registration fails.
- **Semantic reset:** the system deletes \(c\)'s concept and sets internal `Active` false.
  An externally anchored relevance predicate still marks the defect; an internal-only
  one makes `(IMP)` vacuous.

## 6. Dependency diagram

```text
CF / interface assumptions
  global cylinders + certified patch (CFP) + target/applicability preservation
  + admissible policy/transcript semantics
                         │
                         v
Coverage assumptions
  anchored Gamma + Adeq + Implements + Exposure/Registration
                         │
                         v
Proper Exercise assumptions ───── Coverage Resolution Soundness / transport
                         │
                         v
existing Continuity assumptions
  exact O evolution + fresh successors + matter ancestry
                         │
                         v
       No Clean Self-Sealing (live matter + failed Implements)

existing Persistent-Wait assumptions + Wait Responsiveness + NonStarvation
                         │
                         v
             closure OR unbounded attention
                         │
                         v
Failure Materialization + Coverage repair/exercise/registration fairness + Progress
                         │
                         v
               No Persistent Self-Sealing
```
