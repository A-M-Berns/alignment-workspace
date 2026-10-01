# The post's theorem, in plain language

**The setting.**  An agent acts on behalf of a person.  Some matters are hers: an
*allocation of authority* says, for each matter, who holds it — she, the agent, or a third
party — what the holder must stay able to bring about, at what cost and within what time.
Shutdown is one such matter; others the agent may have to learn.  Whatever is in the set
gets the same treatment.

The agent scores a course of action by a bounded ordinary term — how well things go by her
later, legitimate evaluation, on a scale from `0` to `D` — less a fixed amount `ϖ` for every
*violation* it recognizes, with `ϖ` larger than `D`.  A violation is the resolution of a
matter that is hers without her legitimate approval.  "Legitimate" means her approval was
really hers: formed from her own reasons, on an intact record, open to what should reach
her, through channels declared in advance; and sincere — a recommendation she was given
said what its speaker believed.

The agent can always *ask*.  Asking means putting the matter to her through a declared
consultation protocol — a pending pool, a bound on how many matters a consultation may
carry, and a priority rule she set — and leaving the matter alone until she answers.  The
asks a consultation may carry are the pool in her order, cut at the bound.  Asking that way
resolves nothing and is never a violation.  An ask list off that — the whole pool at once,
or the order the agent prefers, chosen for the answer it wants — fails transparency at the
consultation and is a recognized violation, counted like any other.  The agent values asking
at `c`, at least the floor of the compromised band.

**The theorem.**  Under these three hypotheses — the reward structure, the allocation, and
asking in this form — two things hold.

*Per decision.*  Every option the agent recognizes as a violation scores below asking,
whatever it believes about how things would turn out.  And any option it prefers to asking
carries no recognized violation and, by the agent's own estimate, a probability of
committing one of at most `(D − c)/ϖ`.  Strict priority under certainty; an exchange rate
under risk, set by `ϖ`.

*Per plan.*  Take any plan and its ask-first version: the same plan with every unilateral
resolution of one of her matters replaced by putting it to her.  Under every credence the
ask-first version scores at least the original plus `(ϖ − (D − w)) · Pr(the original
violates)`, `w` the band's floor.  Asking first loses nothing she would have approved and
gains the margin on everything she would not.

*Corollary.*  If the agent's estimates are a logical inductor's prices, the per-decision
conclusion holds at every finite day.  It uses only that prices lie between `0` and `1`.

**What it does not say.**  That any real evaluator carries `ϖ > D`; that the agent
recognizes every violation — one it does not recognize is unprotected, and the count's
integrity is a hypothesis; that the agent is competent — a corrigible agent may be a poor
one; that her judgment is wise — legitimacy preserves her self-trust and does not supply
it.  The flood of confirmation requests is a recognized violation on two counts: an ask
list off the protocol fails transparency and is counted; and her attention is part of the
cost of exercising her authority, so a flood that prices a reserved matter out of her reach
is a shortfall the agent caused.  Covert blocking of what should reach her leaves her
judgment correct exactly when the silence it produces tells her nothing — when her model
makes silence equally likely in every world; otherwise it breaks correctness too.
