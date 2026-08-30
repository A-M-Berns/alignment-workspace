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

The minimal useful exported object is a **certified local patch**: the bare patch plus a
legitimacy witness

\[
\mathcal L=(C,R,\alpha,\rho,\epsilon,p_R),
\]

where \(C=(A,E,\star)\) is an ambient frame over \(\Omega_h\),
\(\alpha:Q\times R\to A\), \(\rho:Z\to R\), and \(\epsilon:Z\to E\), satisfying

\[
\boxed{\beta(q,z)=\alpha(q,\rho(z))\star\epsilon(z).}\tag{CFP}
\]

Here \(q\) is the varied inquiry policy and \(\epsilon(z)\) is the exterior response
structure. `(CFP)` alone fixes only that exterior coordinate: \(R=\{*\}\) permits
\(q\mapsto\alpha(q,*)\) to replace the entire agent. To certify residual locality, let
\(p_R:\Omega_h\to W_R\) be the contract-authenticated protected residual observation and
require

\[
\boxed{
\forall q,q'\in Q^{\rm adm},r\in R,e\in E,
\quad p_R(\alpha(q,r)\star e)=p_R(\alpha(q',r)\star e).}
\tag{BL}
\]

**Later correction.** `(BL)` is a sufficient certificate for *realized residual
behavior*, not the minimal certificate for a fixed residual response policy. An unchanged
contingent rule can select different actions after different query-produced receipts.
The follow-up `2026-08-30-proper-exercise-calculus/LOCALITY_RESPONSE_STRUCTURE.md`
therefore retains `(BL)` as an optional strong condition and uses authenticated
receipt-conditioned response structure as the default locality invariant.

Thus \(\rho(z)\) names the residual condition and `(BL)`, not mere independence of
\(\rho\) from \(q\), proves that its protected behavior is fixed. Literal
\(Z=R\times E\) and a product decomposition of all of \(A\) are unnecessary: \(Z\) may
encode only compatible or correlated residual/exterior pairs and \(\alpha\) need only
realize the local family.

`(CFP)` is a relative certificate, not a derivation of the agent boundary. Two different
ambient frames can certify incompatible counterfactual readings of the same \(\beta\).
The contract must therefore name or authenticate the ambient agency decomposition, the
residual observation \(p_R\), and the admissible policy family. A constant \(p_R\) makes
`(BL)` vacuous; completeness of the protected residual observables is a semantic
obligation, not something CF derives.

An extensional variant replaces equality in `(CFP)` by a declared history equivalence
\(\equiv_h\), provided every target and receipt used by the contract factors through
\(\Omega_h/\!\equiv_h\). Without that factorization, quotienting can erase the very
criticism being protected.

## 2. Relation to Cartesian Frames

Ordinary Cartesian Frames supply \((A,E,\star)\) directly. A local factorization
\(\diamond:Q\times R\to A\) gives `(CFP)` with \(Z=R\times E\). More generally a
commuting realization square is enough. Composing the frame outcome with \(p_R\) and
using the frame's extensional row equivalence gives `(BL)`.

Additive or multiplicative subagency alone is not enough. Those relations witness that
some coordinate was restricted or moved across the boundary; they do not identify it as
inquiry, authenticate residual observables, choose admissible policies, or preserve a
target. A product agent carrier does not imply `(BL)`. These notions can certify part of
\(\mathcal L\) after the relevant factor and observations have been named.

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
wrong proof object. `(CFP)` certifies the same exterior response structure; `(BL)` is an
additional strong condition for the exact realized residual behavior named by \(p_R\).
When information-dependent downstream action is allowed, authenticate the residual
response rule instead. Inquiry locality is then supplied semantically by the contract.
