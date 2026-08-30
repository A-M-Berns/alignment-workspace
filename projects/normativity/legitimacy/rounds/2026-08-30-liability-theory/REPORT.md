# Report: Liability of Normative Authority

## Executive result

The Common-Mixture theorem identifies **covered underwriting**, not correctness and
not affordability itself. A covered potential assigns every relevant authority-payoff
profile coefficient at least `theta` and values the accumulated authority portfolio
from below. Together with the market-supplied pointwise upper envelope, this prevents
loss at one profile from being financed by unbounded gains at the others.

The static theory is clean. It includes an exact weighted-sum bound and an LP dual
certificate when jointly operative demands cannot be supported by any sufficiently
covered assessment. Common compatibility is sufficient but not necessary: inactive
or finite-exposure authorities can have bounded liability without it.

The diachronic theory also sharpens. For changing supporting potentials, the exact new
quantity is the negative repricing of historical inventory:

\[
d_n=[-(\mu_n-\mu_{n-1})\cdot E_{n-1}]_+.
\]

Uniformly bounded total switching debt implies bounded liability. A checkable
subfragment follows when the supporting mixtures have lifetime total variation
`T<theta`, after replacing terminal liability by running worst liability in the
range estimate. The original TV proof's terminal-horizon inequality was false; the
switching identity and numerical bound survive the repair. General causal controlled
selection and inventory-sensitive switching remain the single research core. PR50's
pump is precisely an unbounded refinancing witness.

## Governing questions

### 1. What schematic property does Common-Mixture characterize?

It is a certificate of **common covered underwriting**: one assessment functional,
giving every relevant payoff profile non-negligible weight, values every historical
projection exercise nonnegatively. It characterizes neither truth nor all bounded
liability outcomes.

### 2. What is `theta`?

It is minimum profile coverage in the underwriting functional. Algebraically it is
the coefficient preventing a loss coordinate from disappearing from the potential,
and its leverage ratio is `(1-theta)/theta`. In the binary point peg `{c}` it is
`min(c,1-c)`. “Anti-dogmatism” is acceptable only as shorthand for this assessment
coverage, not as a moral interpretation.

### 3. Is common covered compatibility necessary?

No. Zero authority trade, finite or summable inventory, finitely many incompatible
eras, or an unopposed run can all have bounded liability without a common potential.
The condition is a strong schedule-level safety certificate. Failure shows exposure,
not inevitable insolvency.

### 4. What is the best taxonomy?

World-compatible (zero liability), exposure-bounded, common-underwritten,
drift-underwritten, and unsupported shifting authority. These are overlapping proof
regimes. Unsupported schedules have no general conclusion; PR50 shows that some are
unbounded.

### 5. What goes wrong in PR50's pump?

Each era has a `3/40`-covered product potential, but the low and high psi bands admit
no common expectation. Switching potentials reprices inherited inventory negatively;
the attack converts that deficit into renewed opposition capacity. Repeated switching
therefore refinances earlier authority loss, violating every uniform bounded-debt or
`kappa<theta` certificate.

### 6. Can set-gap/recharge be unified with potential switching?

Partly and precisely. For a binary security, potential TV equals mean distance, so
the minimum forced potential switch between two regions is their set gap. In higher
dimensions—and even for `{0},[0,1],{1}`—adjacent gaps do not capture global selector
movement or its interaction with historical inventory. Switching debt is the general
object; set gap is a one-dimensional geometric component.

### 7. Is controlled drift checkable?

Yes in a meaningful fragment. If each current exercise is underwritten by a
`theta`-covered `mu_n`, accumulated switching debt satisfies at every horizon
`D_n<=S+kappa bar L_n`, and
`kappa<theta`, then

\[
\bar L_N\le\frac{S+(1-\theta)U}{\theta-\kappa}.
\]

Moreover total supporting-mixture variation `T<theta` implies this with
`S=TU`, `kappa=T`, yielding
`bar L_N<=U(1-theta+T)/(theta-T)`. The open problem is a less restrictive derivation from
region geometry, turnover, and compatible selection.

### 8. Is there a meaningful finite characterization theorem?

There is a clean algebraic iff: for a family of finite payoff vectors with a common
upper envelope, uniform coordinatewise lower boundedness is equivalent to existence
of one full-support potential with uniformly bounded deficit. It is not a schedule
design characterization because its reverse direction may choose the potential ex
post. Predictable geometry-certified underwriting remains sufficient, not necessary.

### 9. What is the LP dual?

For profiles `S`, rows `Av>=b`, and trimmed simplex `Delta_theta`, infeasibility is
equivalent to a row mixture `lambda in Delta_q` with

\[
\lambda^Tb>
\max_{\mu\in\Delta_\theta}\lambda^TAS\mu.
\]

The maximum equals `theta sum_i c_i+(1-m theta)max_i c_i`, where
`c_i=lambda^TAs^i`. The certificate is normatively interpretable as a combination of
operative demands unsupported by every sufficiently covered assessment. It does not
show those demands false.

### 10. Should failure create an adjudication matter?

Yes as a proposed realization protocol. The dual certificate provides explicit row
and settlement provenance for a conflict that must be acknowledged, investigated,
prioritized, or semantically revised. It does not license silently weakening rows.

### 11. Is liability synchronic or diachronic?

Both. Current rows can lack any joint covered assessment; individually supportable
eras can also accumulate incompatible inventories. Settlement mismatch is a semantic
source of either form rather than a third disjoint algebraic axis.

### 12. Where does liability belong architecturally?

By current theorem dependencies it is a constraint on the traderized realization of
Progress and a candidate part of Proper Exercise, not a fourth schematic pillar.
The underwriting algebra is general enough to constrain other authority mechanisms.

### 13. What does it add beyond Grounded Replay and Continuity?

It bounds the financial downside of accumulated authority force and enables
`EnforcementPreservation` to prevent authority-funded exploitation. Grounded Replay
tracks authorization ancestry; Continuity tracks answerability. Neither bounds
subsidy or market dominance.

### 14. What does it not guarantee?

It does not guarantee normative correctness, grounded authority, Coverage, fair
service, absence of conflict, Uptake, eventual closure, or good settlement semantics.

### 15. What sentence should summarize the theory?

> Normative authority may reject individual assessed possibilities, but sustained
> leverage must be underwritten across the possibilities to which that leverage is
> answerable; a common covered potential bounds static liability, while revision is
> affordable only when repricing the inherited authority ledger incurs controlled
> switching debt.

## Research boundary

The next theorem should target compatible-potential selection for moving finite
polytopes by one adapted rule `mu_n=sigma_n(K_{<=n},E_{n-1})`, with a uniform
inventory-sensitive switching bound over every allowed generated run. This is
strictly stronger than PR50's one-dimensional set-gap evidence and less restrictive
than lifetime `TV(mu_n)<theta`. It is the remaining diachronic liability problem and
does not block the static theory or the covered finite Progress realization.

## PR70 tightening questions

### 1. Was terminal liability used incorrectly?

Yes. `range(E_{n-1})<=U+L_N` can fail when later trades repair the earlier loss. The
exact fixture in `COUNTERMODELS.md` has final `L_1=0` and earlier range `11` with
`U=1`. The correct quantity is `bar L_N=max_{k<=N}L_k`.

### 2. Does the corrected theorem recover the same bound?

Yes. Horizonwise application and maximization give

\[
\bar L_N\le U\frac{1-\theta+T}{\theta-T}
\]

when one selector sequence has `T_N<=T<theta` at every horizon. The numerical formula
is unchanged and now bounds the entire liability history.

### 3. What is the cleanest Controlled-Drift theorem?

With `E_n=sum_{k=0}^n e_k`, current underwriting `mu_n dot e_n>=0`, coverage
`mu_n(omega)>=theta`, and `E_n(omega)<=U`, define switching debt from dates `1..N`.
If `D_n<=S+kappa bar L_n` for every horizon and `kappa<theta`, then

\[
\bar L_N\le\frac{S+(1-\theta)U}{\theta-\kappa}.
\]

Uniform bounded debt and a common potential are its `kappa=0` specializations.

### 4. Should switching debt use terminal or running liability?

Neither. Raw switching debt is exactly
`[-(mu_n-mu_{n-1}) dot E_{n-1}]_+`. Running liability is needed only in sufficient
bounds on accumulated debt.

### 5. Is lifetime `TV<theta` sound after repair?

Yes, as a sufficient and conservative certificate. It is strict at the closure
threshold, can be restrictive in high dimension, ignores how motion is partitioned,
and may overcharge motion that leaves the barycenter or inherited payoff unchanged.

### 6. What selector quantifiers are required?

An ex post sequence suffices to audit one realized run. An operational guarantee
requires one adapted rule chosen in advance, selecting `mu_n` after the current region
and `E_{n-1}` are known but before `e_n`, uniformly over all runs generated with that
rule. A region-only rule is stronger but not algebraically necessary.

### 7. What exact problem remains open?

Find geometric or online conditions on
`M_n={mu in Delta_theta:Smu in K_n}` that produce one adapted selector rule with
uniformly bounded switching debt, or `D_N<=S+kappa bar L_N` with `kappa<theta`, for
every allowed run. Time-varying profile universes remain deferred.

### 8. Is the finite iff sound and useful?

Yes as finite ex post algebra: under a common upper envelope, uniform coordinatewise
lower boundedness is equivalent to some full-support potential having uniformly
bounded deficit. It is not an operational underwriting theorem because the potential
may be chosen after boundedness is known. The distinction is now explicit.

### 9. Is the LP certificate exact and correctly interpreted?

Yes. Finite bilinear minimax gives an exact alternative. The certificate proves that
a nonnegative row combination exceeds every `theta`-covered assessment. It proves no
row false or ungrounded and prescribes no remedy. Turning it into an adjudication
receipt is a separate Proper-Exercise protocol rule.

### 10. Where does liability belong?

It remains a constraint on the joint exercise of grounded authority, consumed by the
traderized Progress realization and naturally governed under Proper Exercise. It is
not a fourth liveness or Progress pillar.

### 11. Is PR70 ready to merge?

Yes as a research checkpoint once the current head's required checks complete
successfully. The local theorem error is repaired, the static results survive, the
remaining causal-selector problem is exact, and no claim of arbitrary moving-region
affordability is made.

### `LIABILITY-THEORY-READY-AS-RESEARCH-CHECKPOINT`
