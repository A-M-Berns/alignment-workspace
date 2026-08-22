Work against the current live `alignment-workspace`, including the internal-answerability prosecution in PR #45 / `2026-08-21-internal-answerability`.

This is an adversarial research pass on a new hypothesis:

    The same mathematical notion of ANSWERABILITY may underlie both

    (a) diachronic answerability of a reasoner to inherited claims across
        self-revision, and

    (b) interpersonal / interagent answerability, where one agent bears
        a standing claim toward another.

Do not assume this unification is correct.

The goal is to determine whether there is genuinely one role-parametric
answerability structure here, what extra interfaces the interpersonal case needs,
and exactly where the analogy breaks if it breaks.

Do not broadly reorganize the workspace yet. End in a focused research memo / PR.

--------------------------------------------------
0. ORIENT TO THE CURRENT KERNEL
--------------------------------------------------

Start from the repaired internal-answerability kernel developed in the latest
round, not from the earlier TMS framing.

The current provisional core is roughly:

1. A normative move m is undertaken under a checkable reason certificate

       p : Licensed(m).

2. For every inherited liability ell touched by the move, the process supplies
   an explicit lineage-linked account of what now answers ell.

3. That account must be semantically adequate PER OLD LIABILITY, not merely
   globally strong:

       [[Account(ell)]] <= residual([[ell]]).

4. If an undertaken historical basis p later loses standing, a fresh review
   liability is docketed rather than retroactively editing history.

The current round distinguishes authorization, undertaken justificatory basis,
and reason-guided control / non-capture, and concludes that the third is a
separate counterfactual hyperproperty. It also distinguishes record-internal
answerability (safety-like), service / learning (liveness or performance), and
reason-guided authorship (counterfactual / multi-run).

Use these as current results to pressure-test, not conclusions that must be
preserved.

--------------------------------------------------
1. THE CENTRAL HYPOTHESIS
--------------------------------------------------

Try to formalize answerability abstractly as a standing directed relation
`x --ell--> y`, where ell is a standing claim/liability, y is presently
answerable, and x is some source, holder, beneficiary, audience, or claimant.
An accountable change by y must give a lineage-linked, semantically adequate
account of ell.

Test whether the diachronic interpretation (a later stage and an inherited
commitment) and interagent interpretation (Alice's standing claim toward Bob)
are instances of one structure or merely verbally analogous.

--------------------------------------------------
2. DO WE ACTUALLY NEED A CLAIMANT?
--------------------------------------------------

Test at least:

A. `Liability(ell, respondent)`
B. `Claim(claimant, ell, respondent)`
C. an articulated source/beneficiary/audience/respondent/content/jurisdiction relation
D. `Constitution |- respondent owes ell` with no privileged claimant.

The earlier self should not have sovereign authority over the later self, and
Alice's standing claim should not make Bob simply subordinate. Determine whether
the primitive is answerable to x, answerable for ell, or answerable to x for ell,
and whether the two cases share “answerable for” while differing in who may
demand or contest an account.

--------------------------------------------------
3. ROLE-PARAMETRIC ACCOUNTABILITY CALCULUS
--------------------------------------------------

Test whether the current account-DAG/per-input transport machinery is agnostic to
agent identity. A liability may carry identity, specification, respondent,
standing source/claimant, jurisdiction, provenance, and birth event. Test same-
respondent revision, split, shared responses, respondent transfer, claimant or
beneficiary transfer, and institutional succession. For each, ask whether
lineage and semantic transport suffice, what authority is needed to change
roles, whether delegation needs consent, and whether shared responses preserve
distinct owed identities. Compare explicitly with PR #45's merge result.

--------------------------------------------------
4. DIACHRONIC CASE AS ONE INSTANTIATION
--------------------------------------------------

Build the smallest diachronic model without treating the earlier stage as a
claimant unless forced. The later stage may revise standing only through a
reason-backed, lineage-preserving, semantically adequate account; it need not
preserve the earlier judgment. Test good-faith reversal, defeat, split,
vocabulary supersession, reason-system self-modification, later basis defeat,
late discovery of error, vanished sources, and changed beneficiaries. State
exactly what is conserved without conserving past preference or literal content.

--------------------------------------------------
5. INTERAGENT CASE AS THE OTHER INSTANTIATION
--------------------------------------------------

Build the smallest Alice/Bob model. Determine what makes Bob's account
answerability to Alice rather than an internally coherent Bob-record. Test
visibility, account identification, challenge rights, shared identifiers,
publicly checkable semantics, discharge authority, contest rights, common
defeater protocols, and protection against Bob redefining Alice's claim. Decide
whether these factor into a Standing/Contestability/Jurisdiction wrapper or
alter the kernel.

--------------------------------------------------
6. THE MULTIPLE-REASON-STATE PROBLEM
--------------------------------------------------

With `R_Alice` and `R_Bob`, ask when `BasisLost(m,p)` occurs if Bob accepts p and
Alice rejects it. Explore Bob-relative, claimant-relative, public/institutional,
and perspectival versions. Test the proposed repair in which the kernel consumes
a public/recognized answerability state rather than private beliefs, so private
disagreement becomes challenge, recognized challenge changes standing, and
public standing change triggers reopening.

--------------------------------------------------
7. CHALLENGE AS THE INTERPERSONAL ANALOGUE OF REFLECTION
--------------------------------------------------

Pressure-test whether diachronic reconsideration and interpersonal contestation
are the same formal operation once a new reason successfully changes standing.
Distinguish a raised challenge from a successful standing-changing challenge.
Determine whether interpersonal answerability needs merely a right to challenge
or a substantive adjudication procedure, and whether challenge rights can be
absent diachronically.

--------------------------------------------------
8. ADEQUACY: WHO DECIDES WHETHER AN ANSWER COUNTS?
--------------------------------------------------

Test respondent-relative, claimant-relative, constitutional, objective, and
plural semantics. Find the weakest structure preventing either endpoint from
unilaterally laundering the meaning or adequacy standard. Connect this to the
existing record-internal/environment-relative distinction and isolate any new
relational adequacy problem.

--------------------------------------------------
9. DELEGATION / TRANSFER OF RESPONSIBILITY
--------------------------------------------------

Stress-test `Alice --ell--> Bob` followed by delegation to Carol. Test Bob
disappearing, Bob remaining secondarily answerable, consent/no consent, Carol
being less or more capable, manipulative selection, branch-only delegation,
onward delegation, and claimant/institutional succession. Determine whether
respondent identity is semantic, and whether the connection to AI delegation or
deference is mathematically real.

--------------------------------------------------
10. MUTUAL ANSWERABILITY
--------------------------------------------------

Test reciprocal Alice/Bob liabilities. Ask whether answering one creates the
other, obligations conflict, one joint action answers both, both bases are
challenged, recognized states diverge, or the parties negotiate a superseding
claim. Determine whether mutuality is multiple directed relations or requires a
new primitive.

--------------------------------------------------
11. ANSWERABILITY IS NOT COOPERATION
--------------------------------------------------

The theory must permit a perfectly answerable Bob to say “No. Here are my
reasons,” and a future self to revise radically while remaining answerable.
State the strongest nontrivial theorem without importing agreement, obedience,
benevolence, preference alignment, or successful cooperation.

--------------------------------------------------
12. RELATION TO NON-CAPTURE / AUTHORSHIP
--------------------------------------------------

Preserve PR #45's separation unless overturned. Test whether relational
legitimacy might eventually decompose into answerability plus authorship/non-
capture. Give a case where answerability holds but authorship fails and one where
authorship holds but answerability fails.

--------------------------------------------------
13. MINIMAL FORMAL CORE
--------------------------------------------------

After the attacks, write the smallest surviving interface. Try to remove
claimant, challenge rights, and other fields when they are wrapper-level. State
whether respondent identity must be semantic and whether a shared recognized
answerability state is required.

--------------------------------------------------
14. TARGET CLAIMS TO PROVE OR KILL
--------------------------------------------------

Address:

A. Role-parametric Answerability.
B. Diachronic Instantiation without past-self obedience.
C. Interagent Instantiation with a separately stated standing/contestability interface.
D. Challenge/Reconsideration Correspondence.
E. Delegation Preservation.
F. Mutuality without a new primitive.
G. Separation from Authorship.

For every false claim, give the smallest counterexample before repair.

--------------------------------------------------
15. ADVERSARIAL MICROCASES
--------------------------------------------------

At minimum test:

1. future self legitimately reverses an old commitment;
2. future self silently deletes an old commitment;
3. Bob answers Alice's claim with a genuine reason-backed revision;
4. Bob supplies an internally valid certificate that Alice cannot inspect;
5. Alice challenges Bob successfully;
6. Alice challenges Bob unsuccessfully;
7. Bob regards p as standing while Alice regards p as defeated;
8. public adjudication resolves the disagreement;
9. Bob unilaterally redefines the meaning of Alice's liability;
10. Bob delegates to Carol with authorization;
11. Bob delegates without authorization;
12. one response legitimately answers liabilities of two different claimants;
13. one strong response illicitly launders one claimant's liability;
14. mutual Alice/Bob claims;
15. hidden-policy manipulation where all answerability records look valid;
16. structurally isomorphic diachronic and interpersonal histories under party relabeling.

Case 16 is especially important: identify any exact extra fact used if the same
checker does not accept/reject solely under role substitution.

--------------------------------------------------
16. THEOREM / COUNTEREXAMPLE MATRIX
--------------------------------------------------

Include a compact matrix covering one kernel, claimant necessity, respondent
metadata, the interpersonal wrapper, public standing, successful challenge,
delegation, mutuality, authorship, and cooperation. Do not protect expected
answers.

--------------------------------------------------
17. WHAT I MOST WANT TO LEARN
--------------------------------------------------

Give crisp answers on whether answerability is one concept; the common kernel;
what changes between instantiations; whether the interpersonal addition is
standing+visibility+challenge/adjudication; whether public standing is needed;
whether claimant is fundamental; whether delegation is respondent transfer
under account preservation; and whether this genuinely helps the legitimacy,
deference, and corrigibility story.

--------------------------------------------------
18. DELIVERABLE
--------------------------------------------------

Create a focused research round under the legitimacy rounds convention with
`MEMO.md`, small executable witnesses/tests where useful, `PROVENANCE.md`, and
only narrow justified status updates. Do not broadly rewrite the architecture,
promote registry claims prematurely, force interagent terminology into old
diachronic files, or turn this into cooperation/corrigibility theory. End with a
small PR.

The final recommendation must be one of UNIFIED, UNIFIED WITH WRAPPER, ANALOGOUS
BUT DISTINCT, or REJECT. Prefer sharp negative results.

The central test is whether answerability is the invariant that a standing claim
cannot disappear or change without a reason-backed, lineage-linked,
substantively adequate account, regardless of whether the inheritor is a future
self or another agent—or whether answerability to another contains an
irreducibly interpersonal mathematical ingredient.
