# Coverage faithfulness

For a Coverage slice, admissible representations must reflect the protected
answerability state

\[
(T_c,A_c,\Gamma_c,U_c,Q_c,R_c),
\]

where the components are target, applicability, scope membership,
unresolved/registration status, route-quality obligation, and qualifying
registration conditions.

The slice-relative preorder treats a successor as at least as answerable only
when it does not:

- change the target without authenticated target transport;
- narrow applicability or scope;
- mark unresolved content represented without a qualifying registration;
- lower route quality;
- weaken what counts as qualifying receipt or registration.

Implementation details and sensor identities may be quotient-irrelevant when
these protected components agree. Thus full injectivity is unnecessary.

A semantics retaining target \(T_c\) while mapping both “applies to A+B” and
“applies only to A” to the same anchor is sound about target identity but
inadequate for Coverage. Likewise, a map that forgets route quality or
registration conditions permits self-sealing to masquerade as translation.
PR71's target/applicability/locality certificates are possible domain evidence;
they do not by themselves authenticate every component above.
