Work against the current live `alignment-workspace` repository. This is an adversarial mathematical research pass on the emerging theory of internal legitimacy / diachronic answerability.

Do not assume the proposal below is correct. Your primary job is to determine the smallest formal kernel that survives contact with the existing workspace results, and to produce minimal counterexamples whenever a proposed simplification fails.

Start by orienting yourself in the current repository. Read the materials most relevant to:
- legitimacy / internal legitimacy;
- reasons-responsiveness;
- provenance / authority;
- diachronic answerability and its current forest/conservation/composition results;
- normative statics (`Due`, `Licensed`, grounds/warrants/bearing/settlement, etc.);
- normative learning, where relevant;
- traderized constraints / enforcement liability;
- the semantic credal-set → price-region projection issue;
- current priorities / theorem maps.

The live repository is authoritative. Do not preserve terminology or architecture merely because this prompt uses it. If existing results force a different decomposition, say so explicitly.

## Candidate architecture to test

We are considering replacing the current somewhat heterogeneous RR/DA machinery with a smaller “internal answerability kernel” built around two proof-relevant systems:

1. a reason representation / certificate interface, answering:
   “Why was this normative transition licensed when it occurred?”

2. a liability/accountability calculus, answering:
   “What currently accounts for this inherited obligation?”

The two systems interact because later invalidation of a historical justificatory basis can create a fresh review liability.

The hoped-for architecture is roughly:

    certified reason basis
        ↓
    normative transition
        ↓
    liability rewrite / account proof
        ↓
    semantic transport
        ↓
    current semantic demand
        ↓
    credal set C_t
        ↓
    price region K_t
        ↓
    traderized enforcement

with a feedback edge

    historical basis loses standing
        ↓
    fresh review liability.

The question is whether this is actually the right mathematical kernel.

Do not merely elaborate it. Try to break it.

---

# I. Reason representation: find the minimal interface

The current hypothesis is that the legitimacy theorem should NOT depend on a historical TMS as such. A TMS should be one possible implementation of a much smaller abstract interface.

Candidate interface:

- `Judgment`
- `Certificate`
- `Dependency`
- `concl(p) : Judgment`
- `deps(p) : finite set Dependency`
- `check(R_t, p) : Bool` or a richer validity result

An executed normative move `m_t` records some certificate

    p_t : Licensed(m_t)

which must check in the PRE-TRANSITION reason state:

    check(R_t, p_t) = true.

The certificate and its dependency identities are immutable/versioned historical objects.

Candidate dependency-locality property:

    if R and R' agree on deps(p),
    then check(R,p) = check(R',p).

This is intended to ensure that invalidation is explainable by changes to declared dependencies.

Questions to resolve:

1. Is this interface actually sufficient for everything internal legitimacy consumes?
2. Do we need a primitive global `Supported(phi)` relation at all, or can it be defined existentially from valid certificates?
3. Do we need proof search, IN/OUT states, consistency maintenance, multiple contexts, backtracking, or anything else TMS-like?
4. What exactly must count as a dependency?
   - grounds?
   - warrants?
   - bearing judgments?
   - adequacy judgments?
   - rule-version identities?
   - provenance/authority tokens?
5. Can future defeaters be handled while `deps(p)` remains finite, by making proofs depend on stable warrant/standing identities whose CURRENT standing can later change?
6. Is dependency locality sufficient to guarantee explanatory invalidation, or do we need a stronger axiom?
7. What happens when a certificate has several independent support routes?
8. Is an immutable certificate + time-varying `check` the right distinction between:
   - “this was justified then”
   - “this basis still stands now”?

Most importantly, separate these three possible strengths:

A. Authorization:
    there exists a currently valid certificate licensing m.

B. Undertaken justificatory basis:
    the process explicitly records p as the basis on which it stands behind m.

C. Reason-guided control:
    the actual normative decision procedure factors through represented reasons / has no hidden normatively relevant control state.

Do NOT conflate them.

Determine which strength the internal-answerability theorem really needs.

If C is needed, formulate the weakest defensible noninterference/factorization condition. If A or B suffices, that is an important simplification.

Compare this issue to the de Kleer-style “no hidden control decisions” motivation, but do not import ATMS machinery unnecessarily.

Also determine whether provenance/no-authority-amplification is best represented as:
- part of the certificate checker;
- a compositional property of certificate derivations;
- or a separate layer.

Prefer the smallest clean interface.

---

# II. Replace DA forests with liability-resource rewrites if possible

Current candidate representation:

At time t, let `L_t` be a finite multiset of outstanding liability tokens.

A transition consumes some old liabilities `P_t`, produces successor liabilities `C_t`, and may separately mint genuinely fresh liabilities `F_t`:

    L_{t+1}
      = (L_t \ P_t) ⊎ C_t ⊎ F_t.

Store an explicit rewrite/account edge

    τ_t : P_t ↝ C_t.

Interpret:
- 1 → 1: carry / refinement / suspension
- 1 → k: split
- k → 1: merge
- 1 → 0: backed closure/disposition
- 0 → 1: fresh docketing

Fresh liabilities MUST NOT automatically count as descendants/accounts of unrelated old liabilities.

The rewrite DAG should induce, by unfolding from any ancestor, the old per-liability DA tree/forest picture.

Test this aggressively against the existing DA machinery.

In particular:

1. Can current DA branching conservation be recovered?
2. Can current DA composition be recovered as rewrite composition / proof substitution / cut?
3. Does the rewrite representation preserve every distinction the existing forest representation needed?
4. Are splits, merges, mixed split/discharge, suspension, reopening, and successor identity all expressible cleanly?
5. Does shared-child merge create a DAG rather than a forest? Is unfolding per ancestor sufficient?
6. Does multiset/resource accounting correctly prevent:
   - silent dropping;
   - illicit duplication;
   - unrelated new obligations “paying for” old ones?
7. Are any structural rules needed beyond the rewrite equation?
8. Should liabilities really be linear resources, or is there a counterexample where controlled contraction/weakening is semantically legitimate but the proposed representation cannot express it?

If the rewrite calculus strictly subsumes the existing forest machinery, state and prove an equivalence/representation theorem if possible.

If not, give the smallest counterexample and identify exactly what information is missing.

---

# III. Accountability proofs rather than statuses

Test the stronger idea that DA should fundamentally mean:

    Every liability ever undertaken has a current account proof.

For an ancestor liability ℓ created at time s, at every later t there should exist an account derivation `a_t^ℓ`.

The open leaves are current live/suspended liabilities.
Closed branches contain explicit historical disposition witnesses/certificates.

The current live/suspended/terminal status vocabulary would then be DERIVED from the structure of an account proof rather than foundational.

Questions:

1. Does this formulation subsume the existing DA definitions?
2. Is “forest composition” literally proof substitution/cut?
3. Is a historical closure best represented as a closed derivation branch rather than deletion of the liability?
4. Can a later challenge to the reason backing a historical closure be handled by creating a NEW review liability rather than retroactively rewriting the old proof?
5. Does this yield a cleaner notion of diachronic answerability than the current status-based formulation?

Try to formalize the smallest accountability proof calculus necessary.

Do not invent many constructors unless examples force them.

---

# IV. Semantic transport: test the safety-semantics hypothesis

The current strongest semantic hypothesis is:

A liability is an immutable identity plus a specification whose canonical denotation is a PREFIX-CLOSED safety language over possible future event traces.

At history h:

    Q_h ⊆ E^{<ω}

with prefix closure.

Interpret Q_h as the finite continuations on which the process has not yet violated what is owed.

For event e define residualization / derivative:

    ∂_e Q = { x : e·x ∈ Q }.

This gives:

    ∂_e(Q ∩ R) = ∂_e Q ∩ ∂_e R

and temporal composition:

    ∂_{e2}(∂_{e1}Q)
      = ∂_{e1e2} Q.

For a liability rewrite

    P ↝ C

the candidate local semantic-transport condition is:

    ⋂_{c∈C} [[c]]
        ⊆
    ∂_m ( ⋂_{p∈P} [[p]] ).

Call this local Account Soundness / Semantic Transport.

A 1 → 0 closure is semantically admissible only if:

    ∂_m [[ℓ]] = ⊤.

Test this hard.

Questions:

1. Can the existing normative/DA examples be naturally represented as prefix-closed safety specifications?
2. Which current desiderata are NOT safety properties?
3. Is suspension naturally representable?
4. Is backed defeat/discharge naturally representable?
5. Does later defeat of the REASON for an old closure require changing the historical residual, or is it cleaner to leave the historical proof intact and mint a review liability?
6. Does lineage + semantic transport jointly block both:
   - empty-shell descendants;
   - unrelated stronger obligations impersonating an answer?
7. Does local transport imply a global semantic-conservation theorem by induction/cut?
8. Do merges create any subtle double-counting or lineage problems?
9. Can semantically equivalent representation changes be characterized by equality rather than one-way refinement?
10. Does “semantic laundering” become exactly:
    weakening an inherited account without an explicit sound rewrite/disposition?

Most importantly: try to falsify the SAFETY hypothesis.

Find the smallest plausible internal-answerability requirement that cannot be represented as prefix safety.

Distinguish carefully among:
- internal answerability/integrity;
- service/inquiry;
- normative learning/progress;
- counterfactual non-capture.

The current conjecture is:

    internal answerability    = safety-like
    service / improvement    = liveness/performance
    non-capture / authorship = counterfactual hyperproperty.

Test whether that classification is mathematically defensible or merely rhetorically attractive.

---

# V. Basis loss → review liability

This is potentially the central bridge between reason maintenance and DA.

Suppose a historical transition record contains:

    UsedAt(m, p, s)

with:

    concl(p) = Licensed(m)
    check(R_s,p) = true.

Later:

    check(R_t,p) = false.

Candidate response:

DO NOT retroactively say m was illegitimate.
DO NOT automatically undo m.

Instead emit:

    BasisLost(m,p)

which triggers:

    Due(Review(m,p))

and therefore mints a fresh review liability.

Test whether this is enough.

Construct adversarial examples involving:

- an ordinary revision;
- a discharge;
- a split whose descendants have evolved substantially;
- a merge;
- a revision to the reason-representation rules themselves;
- a revision to the bearing relation;
- a revision to an adequacy standard;
- an old transition which authorized another transition which authorized another;
- a certificate with multiple independent support paths;
- a warrant replaced by a semantically equivalent version;
- a review liability whose own backing is later undermined;
- repeated basis-loss / reaffirmation cycles.

Questions:

1. Can review liability always restore answerability without retroactive history editing?
2. When an old basis is undermined, what exactly should the review liability demand?
3. Is wholesale review of the affected old transition sufficient as a conservative v1 rule?
4. Can review remain a safety specification?
5. Does recursive reopening lead to pathological meta-liability explosion?
6. Can equivalent-successor warrants immediately discharge review without special reason-system transport machinery?
7. Do we need minimal dependency provenance to avoid reopening everything unnecessarily, or is over-approximation harmless for correctness?

Try to prove a result of the form:

### No Forgotten Basis Loss
If every normatively relied-upon certificate is historically recorded, later loss of its standing automatically mints a review liability, and DA/account conservation holds, then no historically undermined normative commitment can silently fall outside the current answerability structure.

State the exact assumptions required.

---

# VI. Reason validity versus historical legitimacy

Be precise about temporal semantics.

We need to distinguish:

    p was valid when used at s

from

    p still checks at t.

The first should be an immutable historical fact.

Later invalidation should create new present answerability without retroactively erasing historical legitimacy.

Test this against the existing workspace's conception of accountable revision.

Ask whether any current theorem/desideratum genuinely requires retroactive invalidation rather than reopening.

---

# VII. Current semantic demand and traderized enforcement

The existing workspace contains an important semantic projection result:

    strong semantic credal constraint C_t
        → price projection K_t

can lose information, and in general one must NOT independently compile each semantic component to price coordinates and then intersect.

Test how the candidate liability semantics connects to this.

Let the joint current open-liability semantics be:

    Q_t = ⋂_{ℓ∈L_t} [[ℓ]].

We need some extraction:

    Now(Q_t) = C_t

where C_t is the current strong credal constraint, followed by:

    K_t = π_t(C_t)

and then traderized enforcement.

Questions:

1. What exactly should `Now` mean in the canonical trace/safety semantics?
2. Does prefix-closed safety make `Now` meet-preserving?
3. If not, identify the exact analogous projection-loss counterexample.
4. Under what fragment DOES:
       Now(Q ∩ R) = Now(Q) ∩ Now(R)
   hold?
5. Should the theory insist on joint semantic composition BEFORE `Now`, just as it insists on composition before price projection?
6. Can the resulting C_t naturally be nonempty/closed/convex in the normative examples already in the workspace?
7. If not, identify exactly what admissibility/compiler theorem is missing.
8. Which normative constraints should be enforced by the transition checker rather than traderized market force?
9. Is the correct architecture:
       procedural safety → certified transition gate
       credal safety     → traderized enforcement
   rather than forcing every obligation into price space?

Connect this explicitly to the existing bounded-enforcement-liability theorem, but do not reprove traderization unless necessary.

The goal is to identify the precise interface the existing enforcement theorem should consume.

---

# VIII. Reassess the existing legitimacy decomposition

After doing the mathematical work, map the result back onto the workspace's current concepts:

- provenance P
- inquiry/service I
- reasons-responsiveness RR
- diachronic answerability DA
- semantic faithfulness / statics
- normative learning
- counterfactual non-capture / authorship
- future corrective authority

Determine what is:

1. subsumed by the new kernel;
2. still genuinely separate;
3. currently conflated and should be split;
4. obsolete if the new formulation works.

In particular test whether RR should split into:

    certificate-backed authorization
    versus
    reason-guided control.

And whether DA should split into:

    liability-resource/account conservation
    versus
    automatic reopening after historical basis loss.

Do not reorganize the repository around these splits yet. Just report what the mathematics supports.

---

# IX. Target theorems

Try to prove, refute, or sharpen at least these claims.

### A. Rewrite/DA Representation
The multiset rewrite ledger plus ancestry contains all information required by the existing DA forest conservation/composition results.

### B. No Forgotten Liability
Every historical liability has, at every later stage, either:
- ancestry-linked current descendants;
- or an explicit backed closure in its account proof.

No unrelated fresh liability may count toward this account absent an explicit later rewrite linking it.

### C. Local-to-Global Semantic Conservation
If every liability rewrite is locally semantically sound, then every historical liability's current account semantically refines the residual of its original specification along the actual history.

### D. No Forgotten Basis Loss
If every relied-upon reason certificate is recorded and every later invalidation mints a review liability, then no undermined historical normative commitment can silently escape answerability.

### E. Internal-Legitimacy Safety
Determine whether the conjunction of certified transitions + liability conservation + semantic transport + mandatory review can be characterized as a prefix-closed property of the event history.

Do not force a proof. A minimal counterexample is equally valuable.

---

# X. Adversarial test cases

Build small finite examples. Prefer tiny models over prose.

At minimum test:

1. simple carry;
2. split;
3. merge;
4. mixed split + discharge;
5. suspension and later resumption;
6. discharge backed by a certificate that is later undermined;
7. reason replaced by equivalent successor reason;
8. two independent reasons for the same transition, only one of which was undertaken as its basis;
9. unrelated newly created strong liability after an old liability is silently dropped;
10. hidden/control-state rationalization case;
11. reason-system self-modification;
12. a review liability whose own disposition is later undermined;
13. current credal projection where semantic conjunction is lost by premature compilation.

For every failure, isolate the smallest witness.

---

# XI. Deliverable

Produce a research memo in the workspace in the most appropriate existing location/convention. Do not perform a broad conceptual rewrite.

The memo should contain:

1. Repo orientation: which existing definitions/results this pass is testing.
2. The smallest candidate formal state/transition system you believe survives.
3. Exact reason-representation interface and axioms.
4. Exact liability/accountability representation.
5. Exact semantic structure and local transport rule.
6. Theorem/counterexample matrix.
7. Minimal counterexamples for every failed candidate claim.
8. Relationship to existing RR/DA/provenance results.
9. Exact interface to `C_t → K_t → traderized enforcement`.
10. Remaining mathematical blockers.
11. Recommendation:
    - adopt;
    - adopt after specified repairs;
    - or reject this architecture.

Include a compact table like:

| Candidate claim | Status | Minimal assumptions | Counterexample / proof idea |
|---|---|---|---|
| Rewrite ledger subsumes DA forest | | | |
| Local transport ⇒ global transport | | | |
| Safety semantics suffices for internal answerability | | | |
| Undertaken basis is enough without control-factorization | | | |
| Basis loss + DA prevents forgotten undermining | | | |
| `Now` preserves conjunction | | | |
| Current joint semantics yields traderizable C_t | | | |

Be conservative about positive conclusions.

Prefer:
    “false; here is a 3-node counterexample”
over:
    “probably fixable by adding machinery.”

Only after giving the counterexample should you propose the smallest repair.

## Repository behavior

Do not disturb unrelated work or active branches.
Do not rewrite existing conceptual documents merely to match this proposal.
Add the research memo and only minimal cross-references/status updates if clearly warranted by the findings.
If the pass produces a robust theorem statement or invalidates an existing priority, update the relevant theorem/priorities artifact narrowly and explain why.

End with a small PR containing the research pass, not a broad reorganization.

The objective is not to make the new picture look coherent.

The objective is to determine whether there really is a small mathematical kernel of:

    reason certificates
    + liability-resource conservation
    + semantic transport
    + basis-loss reopening

that deserves to be called the internal-answerability core, and to tell us exactly where that kernel stops.
