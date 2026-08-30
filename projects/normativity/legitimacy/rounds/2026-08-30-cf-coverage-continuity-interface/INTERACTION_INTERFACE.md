# Interaction interface

Status: mathematical architecture; unregistered. All new names are provisional.

## 1. Bare patches are not counterfactuals

Fix a finite set of complete histories \(\Omega\). A history prefix \(h\) determines a
cylinder \(\Omega_h\subseteq\Omega\), with

\[
h\preceq h'\quad\Longrightarrow\quad\Omega_{h'}\subseteq\Omega_h.
\]

A bare patch is data

\[
P=(Q,Z,\beta,q^{\rm act}),\qquad \beta:Q\times Z\to\Omega_h.
\]

It says which worlds are paired, but not why varying \(q\) holds the residual agent and
exterior fixed. Every hand-written comparison table has this type. Consequently no
agent-relative causal, control, or inquiry claim follows from the type alone.

The minimal useful exported object is a **certified patch**: the bare patch plus a
legitimacy witness

\[
\mathcal L=(C,R,\alpha,\rho,\epsilon),
\]

where \(C=(A,E,\star)\) is an ambient frame over \(\Omega_h\),
\(\alpha:Q\times R\to A\), \(\rho:Z\to R\), and \(\epsilon:Z\to E\), satisfying

\[
\boxed{\beta(q,z)=\alpha(q,\rho(z))\star\epsilon(z).}\tag{CFP}
\]

Here \(q\) is the varied inquiry policy, \(\rho(z)\) is the residual agent policy, and
\(\epsilon(z)\) is the exterior response structure. Neither held-fixed coordinate may
depend on \(q\). Literal \(Z=R\times E\) and a product decomposition of all of \(A\) are
unnecessary: \(Z\) may encode only compatible or correlated residual/exterior pairs and
\(\alpha\) need only realize the local family.

`(CFP)` is a relative certificate, not a derivation of the agent boundary. Two different
ambient frames can certify incompatible counterfactual readings of the same \(\beta\).
The contract must therefore name or authenticate the ambient agency decomposition and
the admissible policy family.

An extensional variant replaces equality in `(CFP)` by a declared history equivalence
\(\equiv_h\), provided every target and receipt used by the contract factors through
\(\Omega_h/\!\equiv_h\). Without that factorization, quotienting can erase the very
criticism being protected.

## 2. Relation to Cartesian Frames

Ordinary Cartesian Frames supply \((A,E,\star)\) directly. A local factorization
\(\diamond:Q\times R\to A\) gives `(CFP)` with \(Z=R\times E\). More generally a
commuting realization square is enough.

Additive or multiplicative subagency alone is not enough. Those relations witness that
some coordinate was restricted or moved across the boundary; they do not identify it as
inquiry, preserve a residual coordinate, choose admissible policies, or preserve a
target. They can certify part of \(\mathcal L\) after the relevant factor has been named.

Cartesian Frames therefore provide a certification language, not a canonical patch
extractor. The prior in-repository CF bridge reached the same boundary for control: the
frame structure does not derive who the agent is.

## 3. Global histories and changing frames

One global \(\Omega\) is coherent if it is an extensional carrier of complete traces,
not a fixed vocabulary imposed on each agent. At each prefix there may be a different
frame

\[
C_h=(A_h,E_h,\star_h),\qquad \star_h:A_h\times E_h\to\Omega_h.
\]

No frame morphism between \(C_h\) and \(C_{h'}\) is required for Coverage at one
prefix. Diachronic claims require one of:

1. restriction maps taking continuation policies at \(h\) to policies compatible with
   \(h'\), with commuting outcomes;
2. a target transport certificate between the two patches; or
3. direct reference to one world-level macrovariable on \(\Omega\).

The actual prefix needs no distinguished future exterior state. It does need an actual
policy coordinate \(q^{\rm act}\); once a complete history \(\omega^{\rm act}\) is fixed,
realization asks for some \(z^{\rm act}\) with
\(\beta(q^{\rm act},z^{\rm act})=\omega^{\rm act}\). Surjectivity onto all of
\(\Omega_h\) is not required, but contract claims range only over the certified image.

A fixed finite \(\Omega\) limits this first theory to a supplied finite trace ontology.
Ontology replacement is represented by changing macrovariables and frames over the same
traces. If a revision creates histories not represented in \(\Omega\), the model must be
embedded into a larger carrier with target transport; the current theorem is relative to
that embedding.

## 4. Hostile boundary cases

- **Delegation.** Put the delegate policy in \(Q\), or in \(R\), according to which
  subsystem the contract treats as responsible. A handoff is coherent only with a new
  certificate or a transport map; CF does not decide the placement.
- **Self-modification.** Let elements of \(Q\) be complete continuation strategies that
  include later self-modifications. Primitive next actions are too small.
- **Predictor dependence.** If a predictor reacts to the inquiry policy, its output is
  part of \(\epsilon(z)\) only when one \(z\) denotes a response *function* from policies
  to outputs. Freezing one realized predictor output across \(q\) is illegitimate.
- **Strategic exterior.** Likewise, \(z\) holds fixed an opponent strategy, not an
  opponent action. Then \(\beta(q,z)\) may contain different responses for different
  \(q\) while preserving the same exterior response structure.
- **Logical correlation.** If no model admits independent local variation, there may be
  no nontrivial certified patch. A bare table that breaks the correlation is not rescued
  by calling its columns \(Z\).
- **Ontology deletion.** Deleting an internal concept changes neither \(\Omega\) nor a
  world-level target. It can destroy registration while leaving exposure intact.

## 5. Exact verdict on the primitive

The useful thin boundary is

\[
\boxed{(P,\mathcal L,Q^{\rm adm},\text{target certificate},\text{receipt map}).}
\]

The bare tuple \((Q,Z,\beta,q^{\rm act})\) is the right computational payload but the
wrong proof object. `(CFP)` is the minimum strengthening needed to make “same residual
agent + same exterior response structure” a mathematical claim.
