# Coverage authentication

For a criticism slice, a same-slice Transfer certificate must authenticate at
least:

\[
(T_c,A_c,\Gamma_c,U_c,Q_c),
\]

where \(T_c\) is the target/estimand, \(A_c\) is the anchored applicability
condition, \(\Gamma_c\) records scope membership, \(U_c\) records unresolved
and registration status, and \(Q_c\) records the owed route-quality condition.

Exact equality is sufficient but not necessary. A transported equality is
valid when domain evidence proves that target and applicability diagrams
commute and the answerability status and quality obligation are preserved.
Merely retaining a criticism identifier is insufficient.

## Classification

- Exact or authentically transported equality is same-slice Transfer.
- A stronger scope, applicability class, or route-quality obligation carries
  the old slice and admits the increment as a fresh slice.
- Weaker applicability, narrower scope, or reduced route quality requires
  explicit disposition of the dropped content.
- A changed target is not translation unless a target-level isomorphism is
  authenticated.
- Registration can satisfy a slice only with a qualifying receipt and
  registration witness; route capability alone is nonterminal.

Thus target preservation with weakened applicability fails, as does preserved
applicability with a changed target. A genuine external factual event may
satisfy an anchored obsolescence rule. An evaluator's new classification of the
same facts cannot impersonate that event.

PR71's patch and locality certificates remain domain evidence used only when a
Coverage Transfer claims that a subsystem change preserves the relevant
target, applicability, or residual response structure. They need not be added
to every generic Transfer.
