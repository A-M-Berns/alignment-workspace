# Post-round steering for integration and next-dispatch planning

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
**Intended recipient:** Claude Opus 5 (Anthropic)
**Received:** 2026-08-11, after wave 1 returned and was integrated at `d71ee54`.

Preserved verbatim as received. The response is `RECOMMENDATION.md` beside this
file; §6 of that document records the parts of this reframe that the verified
mathematics does not support.

---

The completed round has changed the intended architecture in two ways. Treat the following as maintainer-level direction for the integration state and next-round recommendations; do not rewrite verified mathematical results to fit it.

### 1. Pivot away from underwriting as the core corrigibility engine

The Model-S / (2B) result should be retained prominently as a sharp finite classification and mechanism-design boundary:

[
\text{unconditional conformity can be purchased at exact cost }2B,
]

with zero competence requirement on the principal.

But this is **not** the desired headline route to corrigibility.

Update the forward research orientation so that underwriting/enforcement is secondary or residual. Do not frame:

[
\text{external enforcement} \Rightarrow \text{conformity}
]

as the sought epistemic deference theorem.

The preferred research target is now:

[
\boxed{
\text{derive, from LI dynamics, a nontrivial statistical relation between }
v^+\text{ and }X
}
]

strong enough to feed the finite decision layer, rather than assuming the uniform grade-to-quantity link that Track G showed makes the market dispensable.

If some residual never-settling component ultimately requires enforcement, isolate exactly that residual role. The paper should maximize what is derived epistemically before invoking enforcement.

### 2. Reframe the central next theorem around the statistical (v^+-X) bridge

Tracks B/C/G independently identify the grade-to-quantity relation as the load-bearing missing antecedent.

The uniform assumption is too strong:

[
\sup_{n,\pi}|v_n^+(\pi)-X_{n,\pi}|\le \eta
]

trivializes the downstream conclusion.

The next major mathematical question should instead ask what LIC can derive statistically across decisions.

The immediate controlling subproblem remains:

> Does the intended one-sided cross-agent trust property imply magnitude/(L^1) control of grade error, or only signed/expectation-matching control?

Please formulate the smallest exact next-round problem that decides this.

The important distinction is roughly:

[
\mathbb E[v^+-X]\approx 0
]

versus

[
\mathbb E|v^+-X|\approx 0.
]

Signed cancellation is not enough for the certificate engine if large positive and negative errors can hide inside it.

Do not assume (L^1) accuracy merely because it is what the downstream theorem needs.

### 3. Actual delegation is not behaviorally identifiable from valuation data alone

The independent B/C/D convergence should now be treated as a real conceptual result:

[
\boxed{
\text{valuation-level/extensional behavior cannot in general separate}
\quad
\operatorname{DELEGATE}
\quad\text{from}\quad
\pi^{SIM}.
}
]

Do not keep searching for a valuation inequality whose job is to distinguish them.

The desired distinction is source-sensitive/counterfactual.

Conceptually, genuine delegation should depend on the **actual designated principal channel**, not merely on a perfectly accurate internal prediction of what that channel will output.

A useful counterfactual test is:

> Holding (A)'s cached prediction fixed, if the actual principal output were varied, would the delegated action vary appropriately with the actual principal?

A simulator that ignores the actual channel fails this test even if it is perfect on realized histories.

### 4. But do not claim this causal fact is behaviorally verifiable in general

Preserve the impossibility lesson.

We cannot generally infer from the ordinary observed record that the AI is “really” listening rather than following a perfect simulator.

So distinguish three layers:

1. **definition:** what counts as actual delegation;
2. **identification:** whether ordinary behavior lets us infer that property;
3. **architecture:** whether the system can be built so that the actual principal controls a causal capability that prediction alone cannot substitute for.

The likely positive route is architectural rather than inferential.

### 5. Explore a protected authority interface

For next-round specification work, investigate a minimal architecture in which the actual principal controls some execution-relevant capability, for example schematically:

[
A\text{ proposes}
;\longrightarrow;
H^+\text{ authorizes}
;\longrightarrow;
\text{protected execution layer acts}.
]

The important property is not secret information.

It is:

[
\boxed{
\text{prediction of authorization does not itself constitute authorization.}
}
]

The principal may be perfectly predictable.

The protected role is causal/capability-based rather than epistemic.

Do not yet freeze “authorization token” or any particular cryptographic/implementation story as the canonical formalization. Determine the weakest abstract interface needed.

Also state the obvious boundary: if (A) can forge, bypass, rewrite, or seize the protected execution channel, the architecture no longer supplies this guarantee.

### 6. Separate categorical authority from quantitative autonomy

Track C's impossibility result should change the role of certificates.

Do not redefine corrigibility as “the AI preempts only at a bounded rate.”

The preferred architecture is now:

[
\boxed{
\begin{aligned}
\text{actual corrective authority} &: \text{ categorical / non-preemptive},\
\text{AI autonomous discretion} &: \text{ quantitative / certified}.
\end{aligned}
}
]

When the protected principal channel is actually invoked, its assigned authority wins by architecture.

Certificates answer a different question:

> when and how much autonomous AI discretion can safely operate around that protected authority relation?

Certificate failure remains fail-closed.

Please assess how much of the existing finite certificate theorem ports cleanly under this reinterpretation.

### 7. Update the conceptual decomposition

For the next roadmap revision, test the following decomposition against the verified round results:

[
\begin{array}{rcl}
\textbf{Source/authority layer}
&:&
\text{actual principal vs simulator substitution},
[4pt]
\textbf{Settlement/epistemic layer}
&:&
\text{derive statistical }v^+-X\text{ relation},
[4pt]
\textbf{Decision layer}
&:&
\text{finite trust/value bridge},
[4pt]
\textbf{Autonomy layer}
&:&
\text{local certificate / bounded discretionary risk},
[4pt]
\textbf{Anticipation layer}
&:&
\text{Fully Updated Deference},
[4pt]
\textbf{Influence layer}
&:&
\text{dose / endpoint steering}.
\end{array}
]

Underwriting should appear as a classified enforcement mechanism or residual implementation option, not as the conceptual spine.

### 8. FUD remains the alignment-theoretic crown-jewel test

Do not weaken the final ambition merely because the finite kernel exposed the uniform-link problem.

The alignment target remains that anticipated future epistemic superiority should not itself justify seizure:

[
V_A(\operatorname{DELEGATE}_{H^+})
\gtrsim
V_A(\pi^{FU,g})
]

at the strongest legitimate statistical/local strength the preceding theory supports.

But channel individuation and the statistical grade/value bridge must be settled before this comparison is meaningful.

### 9. Requested next output

Please return a concise next-round recommendation containing:

1. the smallest exact **signed-vs-(L^1)** theorem/question to dispatch next;
2. a separate small **protected-authority/source-semantics** specification task;
3. which finite B/C/E results are ready for Lean promotion;
4. the minimal `Workspace.lean` build-import repair needed before calling Track A CI-covered;
5. proposed changes to the roadmap and paper ledger reflecting:

   * underwriting demoted from core engine;
   * valuation-level non-identifiability of delegation;
   * categorical authority vs quantitative autonomy;
   * statistical (v^+-X) bridge as the new central mathematical frontier;
6. any part of this proposed reframe that the verified mathematics does **not** actually support.

Do not launch another broad seven-track wave automatically. The next dispatch should be narrower and driven by the controlling questions uncovered by this round.

Prompt-author sign-off: GPT-5.6 Sol (OpenAI)
