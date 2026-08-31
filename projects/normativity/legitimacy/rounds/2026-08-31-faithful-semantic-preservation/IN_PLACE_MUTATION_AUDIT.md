# In-place mutation audit

## The counterexample

At prefix \(n\), let the only live carrier \(q\) have
\(\lambda_n(m,\alpha,q)=a=A(m,\alpha)\). Keep \(q\) outstanding at \(n+1\),
resolve nothing, record no Satisfaction or Disposition, and set
\(\lambda_{n+1}(m,\alpha,q)=0\).

Settled outstanding evolution holds: the same occurrence remains live. PR73's
original hypotheses also hold vacuously because no affected resolution batch
exists. Its conservation equation fails at \(n+1\). Thus the gap is literal,
not terminological. PR72's Transfer prose had required a certificate for an
in-place edit, but PR73's theorem did not quantify over that requirement.

## Generalized affected batch

For each transition, matter, and slice, choose finite old and post carrier sets
\(P^-_n(m,\alpha)\) and \(P^+_{n+1}(m,\alpha)\). They must cover every:

- resolved old carrier with nonzero load;
- born post carrier with nonzero load;
- persistent carrier whose load changes;
- persistent carrier explicitly used in redistribution.

Outside these sets the identity frame applies:

\[
q\in Live_n(m)\cap Live_{n+1}(m),\quad q\notin P^-\cup P^+
\Longrightarrow
\lambda_{n+1}(m,\alpha,q)=\lambda_n(m,\alpha,q).
\tag{ID}
\]

Inside the batch require authenticated generalized Transfer:

\[
\bigvee_{q\in P^-}\lambda_n(m,\alpha,q)
=s\vee d\vee
\bigvee_{q'\in P^+}\lambda_{n+1}(m,\alpha,q').
\tag{GT}
\]

Every part of \(s,d\), and every post load has its usual domain certificate;
\(d\) additionally needs authorized Disposition.

## Why this is minimal

Candidate A alone protects only edits not declared explicit. Candidate B names
a certificate but does not state its collective conservation obligation.
Candidate C plus the identity frame covers structural succession, in-place
translation, redistribution, and terminal exits with one interface. A
disconnected semantic-edit lifecycle is unnecessary.

Identity is the default frame case and also has a trivial explicit certificate
when composition needs a proof object. Structural persistence never implies
semantic identity. Continuity is unchanged.
