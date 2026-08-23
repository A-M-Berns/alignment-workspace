execute this prompt, note that some of the relevant prior art is in downloads Use this as the agent prompt:

> Work in the live `A-M-Berns/alignment-workspace` repository. Read and obey `AGENTS.md`, `DECISIONS.md`, the claims registry, and other repository precedence rules before editing anything. Inspect the current `main` branch rather than relying on this prompt for repository state. In particular, read the current wiki material around Normativity, Legitimacy, Normative Record and Inquiry, Normative Response Learning, Reasons/Answerability/Score, and the current roadmap. Also inspect the recent afoundational-inquiry / internal-answerability rounds and any existing TMS/reason-representation notes that are relevant.
>
> Create a **new research branch and PR** whose purpose is to **prosecute and refine the proposed narrow-waist representation for normative reasons**. Do not assume the representation below is correct. The goal is to find the smallest structural interface that survives realistic examples **without hiding substantive normative work inside a TMS, checker, or opaque update rule**.
>
> ## Current hypothesis to test
>
> We have recently been converging on a substantial simplification of the normative architecture.
>
> Distinguish:
>
> [
> \mathcal R_n = \text{current reason structure},
> ]
>
> from
>
> [
> \mathcal N_{\le n} = \text{historical normative record},
> ]
>
> and from the descriptive interaction transcript
>
> [
> L_{\le n}.
> ]
>
> The proposed basic reason structure is a directed identity-bearing multi-hypergraph:
>
> [
> H_n=(V_n,E_n,s_n,t_n),
> ]
>
> where
>
> [
> s_n:E_n\to\mathcal P_{\mathrm{fin}}(V_n),
> \qquad
> t_n:E_n\to V_n.
> ]
>
> Each (e\in E_n) is a **particular reason occurrence/application**, not merely an abstract implication. Equal source and target do not identify occurrences.
>
> There is also a set of identity-bearing reason schemas
>
> [
> \Sigma_n.
> ]
>
> A major current hypothesis is that **schema organization itself should be represented inside the reason language**, rather than by an external clustering relation. The content language should therefore support at least:
>
> [
> \mathsf{Inst}(e,\sigma)
> ]
>
> meaning that particular reason occurrence (e) is an instance of schema (\sigma), and
>
> [
> \mathsf{App}(\sigma,c)
> ]
>
> or possibly the staged form
>
> [
> \mathsf{App}(\sigma,c@n),
> ]
>
> meaning that schema (\sigma) applies to case (c) at the relevant interaction stage.
>
> Reifying applicability is intentional. An undercutter should ideally be representable as an ordinary reason for
>
> [
> \neg\mathsf{App}(\sigma,c),
> ]
>
> rather than requiring a primitive `Undercuts` relation.
>
> Reifying schema membership is likewise intentional. Schema learning should be able to proceed through ordinary reasons for or against claims such as
>
> [
> \mathsf{Inst}(e,\sigma).
> ]
>
> This potentially lets schema splits, merges, reclassification, and cross-cutting schemas be represented as reason-guided revision rather than as an opaque external clustering operation.
>
> ### Cases, docket, and interaction
>
> The current hypothesis is that these should be distinguished:
>
> [
> \text{case}\neq\text{docket item}\neq\text{receipt}.
> ]
>
> A **case** is tentatively a persistent environment-facing interaction thread or situation.
>
> A **docket item** is a question, investigation, review, response, or other obligation the practice has *about* a case:
>
> [
> \mathsf{about}:D\to C.
> ]
>
> A **receipt** is an empirical/logical interaction event in (L).
>
> There may be a procedural provenance relation
>
> [
> T\subseteq C\times L
> ]
>
> saying that receipt (\ell) arose in working on case (c). This should **not** itself mean that (\ell) is evidentially relevant or supports any particular conclusion; that is reason-level content.
>
> One case may have several docket items. One receipt may potentially bear on several cases. Seed/training examples may be historical cases rather than currently live docket cases.
>
> An unresolved issue is whether `Case` needs any structure beyond stable identity and relations into (\mathcal N) and (L), or whether applicability really targets a **case-view/stage** rather than a persistent case:
>
> [
> \mathsf{App}(\sigma,c@n).
> ]
>
> This distinction matters because we must separate:
>
> * learning later that (\sigma) never applied at stage (n), from
> * (\sigma) genuinely applying at (n) but ceasing to apply after the world changes.
>
> ### Reason maintenance versus normative response
>
> Another major hypothesis to test is that the TMS-like layer should **not choose what the agent believes or does when reasons conflict**.
>
> We want to distinguish:
>
> [
> \boxed{\text{reason maintenance}\neq\text{stance revision}.}
> ]
>
> Let (B_n) denote the agent's current stance/context. Relative to (B_n), the reason substrate can say which reason occurrences are enabled:
>
> [
> \mathsf{Enabled}_{B_n}(e)
> \iff
> s(e)\subseteq B_n,
> ]
>
> and which live reasons bear on some target:
>
> [
> \mathsf{Reasons}_{B_n}(v)
> =========================
>
> {e:t(e)=v,\ \mathsf{Enabled}_{B_n}(e)}.
> ]
>
> The substrate should preserve dependencies and explanations. It should **not** silently implement:
>
> [
> \mathsf{Reasons}_{B_n}(v)\neq\varnothing
> \Longrightarrow
> v\in B_n.
> ]
>
> If there are live reasons for both (p) and (\neg p), the reason representation should be able to expose both. Whether the learner retains (p), adopts (\neg p), suspends, investigates, distinguishes the case, revises a schema, etc. belongs to the normative-learning theory.
>
> A JTMS or ATMS may be an implementation of this substrate, but do **not** assume ordinary JTMS `IN/OUT` semantics are the conceptual interface we want. One possible conclusion of this round is that “TMS” is the wrong name and the abstraction is better described as a **reason dependency / maintenance system**.
>
> ## Core research question
>
> Determine:
>
> [
> \boxed{
> \text{What is the smallest reflective reason-representation interface that}
> }
> ]
>
> [
> \boxed{
> \text{supports case-based, schema-organized, defeasible normative learning}
> }
> ]
>
> [
> \boxed{
> \text{without hiding the normative response policy inside the representation?}
> }
> ]
>
> Treat minimality as a serious design constraint, but **do not contort examples to preserve minimality**. If one additional primitive is genuinely required, identifying that is a successful result.
>
> ---
>
> ## Investigation 1: prosecute the representation with concrete histories
>
> Construct a suite of small explicit histories. For each, write down the objects and updates needed, then ask whether the candidate interface represents all distinctions that matter.
>
> At minimum test:
>
> 1. **Ordinary schema application.** Historical cases support a schema; the schema applies to a new case; a particular reason occurrence bears on a claim or action.
>
> 2. **Undercutting.** New inquiry produces a reason for
>    [
>    \neg\mathsf{App}(\sigma,c@n),
>    ]
>    disabling a previously relied-upon reason without thereby supporting the opposite conclusion.
>
> 3. **Undercutter of an undercutter / nested reflection.** Applicability of the reason used to undercut another reason is itself challenged. Check whether ordinary hypergraph structure plus reified `App` genuinely closes under this.
>
> 4. **Rebuttal/conflict.** Simultaneously live reasons bear toward conflicting conclusions/responses. Verify that the substrate can preserve both without adjudicating the stance.
>
> 5. **Schema reclassification.**
>    [
>    \mathsf{Inst}(e,\sigma)
>    ]
>    is later rejected and perhaps replaced by
>    [
>    \mathsf{Inst}(e,\tau).
>    ]
>
> 6. **Schema split.** Several historical reason episodes formerly grouped under one schema are later reorganized into two.
>
> 7. **Schema merge.**
>
> 8. **Cross-cutting schemas.** A single reason occurrence legitimately instantiates multiple schemas. Do not assume schemas form a partition.
>
> 9. **Same apparent reason, distinct occurrence.** Two reason applications with identical source/target content occur in different cases and must retain separate history and answerability.
>
> 10. **One case, several docket items.** Investigation, review, and substantive response may all concern the same persistent case.
>
> 11. **One interaction serving several cases.** A single observation/action/test result is procedurally connected to multiple case threads.
>
> 12. **Changed applicability vs discovered prior non-applicability.** Represent and distinguish:
>     [
>     \neg\mathsf{App}(\sigma,c@n)
>     ]
>     learned later, versus
>     [
>     \mathsf{App}(\sigma,c@n)
>     \wedge
>     \neg\mathsf{App}(\sigma,c@(n+1)).
>     ]
>
> 13. **Basis loss and review.** A historical commitment or response explicitly relied on reason occurrence (e); later its basis is undercut. The historical record must still know that (e) was actually relied upon, even if a different currently valid reason now supports the same conclusion.
>
> 14. **New evidence relevant to a case but not yet interpreted.** Ensure the case/receipt relation itself does not encode evidential or normative relevance.
>
> 15. **A reason about schema organization itself.** Evidence supports a claim about which cases/reason occurrences belong together, rather than merely supporting a first-order conclusion.
>
> For each example, record:
>
> * what is constitutive structure;
> * what is a revisable claim in (V);
> * what lives in the historical normative record;
> * what lives in the descriptive transcript;
> * what the reason-maintenance API must expose;
> * what is left to the normative learner.
>
> If the example requires a new primitive, explain exactly why.
>
> ---
>
> ## Investigation 2: determine the structural type of `Case`
>
> Compare at least the following candidate treatments:
>
> ### Candidate A: opaque identity
>
> [
> C=\text{stable case IDs}
> ]
>
> with all information retrieved relationally from (\mathcal N) and (L).
>
> ### Candidate B: pointed interaction thread
>
> A case has a stable identity plus an opening event/issue and a growing associated interaction history.
>
> ### Candidate C: persistent case + staged view
>
> Persistent (c\in C), but applicability and perhaps reason application target a derived object
>
> [
> c@n
> ]
>
> or
>
> [
> \mathsf{View}_n(c).
> ]
>
> Ask:
>
> * Does a case itself need an `issue`, or can all questions/issues live in docket items (D\to C)?
> * What exactly makes two receipts part of “the same case”?
> * Is that a constitutive provenance fact or a revisable judgment?
> * Can cases split or merge? If so, is this a new case identity with provenance, or revision of identity?
> * Does a case continue after all current docket items are closed?
> * Can multiple agents/practices refer to the same case while maintaining different dockets?
> * Do seed examples and runtime cases have the same type?
> * What temporal object must `App` take so that changing-world and corrected-belief cases are distinguishable?
>
> Prefer the thinnest type that survives these tests.
>
> ---
>
> ## Investigation 3: derive the minimal TMS / reason-maintenance API
>
> Do not begin by copying JTMS or ATMS APIs.
>
> Begin from downstream consumer requirements and derive the smallest common interface.
>
> Explicitly compare at least:
>
> * a JTMS-style current-context dependency system;
> * an ATMS-style environment/label system.
>
> Determine which of the following are genuinely required:
>
> [
> \mathsf{Enabled}_B(e),
> ]
>
> [
> \mathsf{Reasons}_B(v),
> ]
>
> [
> \mathsf{Explain}_B(e)
> \quad\text{or}\quad
> \mathsf{Explain}_B(v,e),
> ]
>
> support certificates / dependency DAGs,
>
> alternative supports,
>
> minimal supports,
>
> assumptions/environments,
>
> nogoods,
>
> negative dependencies,
>
> dependency queries,
>
> hypothetical/counterfactual queries.
>
> In particular test whether later consumers need questions like:
>
> > If I withdrew (x), what currently relied-upon reasons would lose their basis?
>
> or:
>
> > Which current conclusions have historical support paths passing through this applicability judgment?
>
> or:
>
> > Under a proposed stance (B'), which reasons would become enabled?
>
> Do **not** make every convenient operation primitive. Distinguish:
>
> 1. the mandatory narrow-waist API;
> 2. optional richer queries that particular implementations may efficiently supply.
>
> State a clear implementation-independence claim if one survives:
>
> > Any backend satisfying interface (X) can serve as the reason-maintenance substrate for the downstream normative learner.
>
> If that claim is false, identify why.
>
> ---
>
> ## Investigation 4: support structure versus stance
>
> This deserves its own adversarial section.
>
> Construct examples with:
>
> [
> \mathsf{Reasons}_B(p)\neq\varnothing,
> \qquad
> \mathsf{Reasons}_B(\neg p)\neq\varnothing.
> ]
>
> Verify that the substrate can expose this state without automatically resolving it.
>
> Clarify:
>
> * What exactly is (B_n)?
> * What kinds of things can be in it?
> * Is (B_n) part of the reason-state structure, a separate current stance, or a derived view?
> * Are actions themselves members of a stance, or only claims/judgments about actions?
> * What support-maintenance guarantees can be imposed on (B_n) without smuggling in substantive norms?
> * When a basis is undercut, what does the substrate report versus what must the learner decide?
>
> Aim for a sharp abstraction boundary:
>
> [
> \boxed{
> \text{the substrate reports available reasons and dependencies;}
> }
> ]
>
> [
> \boxed{
> \text{the learner determines appropriate response/revision.}
> }
> ]
>
> If this division cannot be made cleanly, explain the obstruction.
>
> ---
>
> ## Investigation 5: press on incompatibility
>
> We have not settled the right object here.
>
> Do not assume a primitive
>
> [
> \mathsf{Incomp}(x,y)
> ]
>
> over arbitrary contents.
>
> Determine what “rebuttal” actually requires.
>
> Compare:
>
> * logical contradiction of claims;
> * incompatibility of candidate actions;
> * incompatibility of commitments/stances;
> * incompatibility of finite sets of possible responses;
> * n-ary nogoods;
> * constraints on admissible stance extensions;
> * a reified learnable incompatibility proposition.
>
> Ask:
>
> * What exactly are the arguments of incompatibility?
> * Does the reason representation need separate `Claim` and `Act` target sorts?
> * Do we need `Hold` or `Do` constructors after all, or can those remain downstream?
> * Can incompatibility itself be learned or defeated?
> * Is binary incompatibility sufficient?
> * Is incompatibility actually structural, or can it be derived from the typed content language plus feasibility?
>
> Rebuttal should ideally become a **derived** relation between live reasons whose targets cannot jointly be adopted, rather than another primitive attack edge. But prosecute that hypothesis.
>
> ---
>
> ## Investigation 6: reflective closure and reification criterion
>
> Use the working criterion:
>
> [
> \boxed{
> \text{If the learner may legitimately revise a structural judgment for reasons,}
> }
> ]
>
> [
> \boxed{
> \text{that judgment should probably be expressible as a target of reasons.}
> }
> ]
>
> `Inst` and `App` are currently strong candidates under this criterion.
>
> Apply it to:
>
> * schema membership;
> * applicability;
> * incompatibility;
> * evidential relevance;
> * whether a receipt belongs to a case;
> * same-case identity;
> * schema identity across time;
> * reason priority;
> * reliability;
> * “this reason was relied upon”;
> * authorization / standing;
> * `May` / `Must`.
>
> Distinguish carefully between:
>
> [
> \boxed{\text{constitutive provenance facts}}
> ]
>
> and
>
> [
> \boxed{\text{revisable judgments about the reason structure}.}
> ]
>
> Do not reify things merely because they are metadata.
>
> Current expectation, which you should challenge:
>
> * `Inst`: yes.
> * `App`: yes.
> * `Hold`: probably not primitive in the reason substrate.
> * `Do`: probably not primitive; possibly a typed action target instead.
> * `May` / `Must`: probably not primitive reason-graph constructors. They may remain modes/interpretations in the larger normative record and operative compiler.
> * `Live`, `Supported`: probably derived queries, not object-language claims.
> * source/target identity of an edge: constitutive structure, not revisable content.
>
> ---
>
> ## Investigation 7: reconnect to the larger architecture
>
> Do not redesign the whole normative program, but test whether the proposed narrow waist leaves the next interfaces plausible.
>
> In particular consider the eventual handoff:
>
> [
> (\mathcal N_{\le n},L_{\le n},\mathcal R_n,B_n)
> \longrightarrow
> O_n.
> ]
>
> Ask whether the representation lets an operative compiler later recover or inspect:
>
> * what claims/actions currently have reasons bearing on them;
> * which particular reason occurrences are involved;
> * which schemas those occurrences instantiate;
> * which applicability judgments they rely on;
> * which case/stage they concern;
> * which basis was historically relied upon;
> * what has lost basis and requires review;
> * what is merely a live reason versus what the agent actually endorses;
> * which docket items remain unresolved.
>
> Also check compatibility with the existing abstract response-learning interface:
>
> [
> Due,\qquad Licensed,\qquad Performance.
> ]
>
> We do **not** want `Due` and `Licensed` hardwired into the reason hypergraph merely to make the old theorem compile. Determine what representation the downstream normative-record/compiler layers would need in order eventually to define them.
>
> Keep traderization and credal/evaluative realization downstream. Do not pull prices, probabilities, utilities, liability, or market mechanics into the reason-state representation.
>
> ---
>
> ## Literature / prior-work comparison
>
> Use the existing workspace materials and any already-available source papers/notes on Doyle-style JTMS, de Kleer ATMS, Horty/default reasons, and the earlier statics work.
>
> The point is not to write a literature review. Use prior work to answer concrete interface questions:
>
> * Which parts are ordinary TMS functionality?
> * Which parts require an ATMS-like richer notion?
> * Which parts are genuinely new because of schema organization, case interaction, or diachronic normative provenance?
> * Can reified applicability reproduce the useful distinction between rebuttal and undercutting?
> * Does schema membership introduce a second-order hypergraph, or is reifying `Inst` cleaner?
>
> Do not let named frameworks dictate the ontology.
>
> ---
>
> ## Implementation / formal artifact
>
> Produce a **small executable or formal model** sufficient to demonstrate the prosecution examples.
>
> Prefer Lean if the representation can be stated naturally and the examples become useful theorem/API tests. But do **not** force a large Lean development if a smaller executable/reference model better exposes the conceptual issue. Follow existing workspace conventions.
>
> The implementation should be deliberately tiny. Its purpose is to distinguish:
>
> * structural facts;
> * reflective reason contents;
> * case/docket/transcript provenance;
> * reason availability;
> * stance;
> * historical reliance.
>
> Include adversarial tests that would fail if:
>
> * identical reason occurrences collapse;
> * schemas are forced to partition occurrences;
> * undercutting implies the opposite conclusion;
> * the TMS silently resolves conflicting reasons;
> * historical basis is overwritten by a new proof;
> * case and docket identity collapse;
> * a receipt is treated as evidential merely because it occurred in a case;
> * current applicability cannot distinguish changing-world from corrected-belief cases.
>
> ---
>
> ## Deliverables
>
> Add an appropriately located research memo, with a clear title such as `REASON_REPRESENTATION.md` or whatever fits workspace organization better after inspection. It should contain:
>
> 1. **Proposed minimal types/interfaces.**
> 2. **Semantics of every primitive.**
> 3. **What is deliberately not primitive.**
> 4. **Case/docket/transcript separation.**
> 5. **Reason-maintenance API.**
> 6. **Support-versus-stance boundary.**
> 7. **Reflective vocabulary and reification criterion.**
> 8. **Treatment or unresolved status of incompatibility.**
> 9. **Prosecution/example matrix.**
> 10. **JTMS/ATMS comparison at the interface level.**
> 11. **Known failures / forced additions to the candidate representation.**
> 12. **Implications for (I_0\to R_0), inquiry, `Due`/`Licensed`, (R\to O), and later legitimacy work.**
> 13. **A concise final recommended interface**, even if explicitly provisional.
>
> Also update whichever workspace state/roadmap/wiki sources should reflect the result, following repository precedence and status conventions. Do not promote speculative results to Established. Preserve the distinction between tested/unregistered claims and registered/Lean-checked results.
>
> If the existing wiki's broad `R_n` terminology conflicts with a narrower “reason state” discovered here, resolve this carefully in prose rather than silently changing meanings. A useful outcome may be an explicit distinction such as:
>
> [
> \mathcal R_n=\text{reason state},
> \qquad
> \mathcal N_{\le n}=\text{normative record}.
> ]
>
> ---
>
> ## Success criteria
>
> This round succeeds if it leaves the workspace with a substantially sharper answer to:
>
> [
> \boxed{
> \text{What information must a normative learner represent about its reasons?}
> }
> ]
>
> In particular, I want to know whether something close to
>
> [
> \boxed{
> \text{identity-bearing reason hypergraph}
> +
> \text{schemas}
> +
> \text{cases}
> +
> \mathsf{Inst}
> +
> \mathsf{App}
> }
> ]
>
> really is a viable narrow waist.
>
> **Do not optimize for preserving that answer.**
>
> A high-value negative result would be:
>
> > This representation fails on example X; the minimum missing primitive/query is Y; here is why Y cannot be compiled away without hiding normative work.
>
> A low-value result would be simply translating the current proposal into definitions and declaring it sufficient.
>
> The deeper design constraint is:
>
> [
> \boxed{
> \text{representation should remember and expose reasons;}
> }
> ]
>
> [
> \boxed{
> \text{it should not secretly decide how a reason-responsive learner must respond.}
> }
> ]
>
> End with a **new PR** containing the research memo, any small formal/executable witness, tests, and appropriate workspace/wiki updates. In the PR description, clearly separate:
>
> * what survived prosecution;
> * what failed;
> * what remains open;
> * what you recommend as the next research pass.
