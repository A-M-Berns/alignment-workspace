# Reason Carry instance

Reason Carry is a direct Transfer instance. The anchored semantic atom is an unresolved
reason occurrence with source/provenance, answer mode, and the content it requires the
episode to answer. An issue carrier records the current representation of that reason.

The existing schematic

\[
r@q\text{ unresolved},\ q\to q'
\Rightarrow Disposition(r)\lor Translate(r,r',q')
\]

is the one-parent, one-child case. `Translate` proves source identity/provenance,
unresolved status, answer-mode mapping, and equality of semantic denotation. It need not
prove numerical comparison invariance; that remains a stronger cross-era Progress
certificate.

For a split, translations from (r) to a finite reason family must jointly join to the
old denotation. For a merge, the new reason representation may join several parent
denotations, but it must account for each and may not silently drop one. Defeat,
withdrawal, and release require typed disposition evidence; changing evaluator labels is
not disposition.

The same matter-frontier form works independently of Coverage:

\[
ReasonSpec(m)=Disposed_{\le n}(m)
\vee\bigvee_{q\in C_n(m)}ReasonLoad_n(m,q).
\]

This confirms that Transfer is not merely Coverage Resolution Soundness renamed.
Coverage atoms are criticisms and registration claims; Reason Carry atoms are reason
occurrences and answer-mode content.

Basic Progress remains episode-local and may count explicit revisions. Transfer prevents
semantic omission at those revisions but does not make infinite translation a stagnant
tail. Cross-era Progress needs an additional invariant—such as a preserved surface and
margin—over a composed Transfer chain.
