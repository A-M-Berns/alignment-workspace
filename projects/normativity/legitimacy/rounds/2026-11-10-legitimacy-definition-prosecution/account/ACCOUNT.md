# The account — manipulation as induced mistake; a change of what she values judged by three conditions against a reference

**`STATEMENT.md` is the statement that governs now**; `BOARD.md` is the statement the tenth
follow-up tested, and this document the one the ninth tested.

Part I is the setting, Part II the belief side, Part III the value side. Part III is the
statement of `PROMPT-followup-9.md` §1, the prompt author's, tested by no one else; Part
II is held with some confidence. Positions marked *(maintainer)* are the maintainer's
current view, held for testing and not rulings. §11 lists the choices made where the
statement is open, each with its alternative and where a verdict turns on it. All names
are provisional.

*(maintainer)* The account is a formalisation of Robert Noggle's Mistake Account
(*Manipulation: Its Nature, Mechanisms, and Moral Status*, OUP 2025; "The Mistake Account
of Manipulation", *Journal of Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951):
manipulation is influence that works by inducing a mistake. Her cognitive faculties are
modelled as estimators, each with the quantity it estimates as its purpose. That a
faculty is for something, and that manipulation distorts her away from it, is Sam
Eisenstat's idea; this account is its specialisation to cognition. *(maintainer)* The
account of manipulation as induced mistake over estimators is primary; the workspace's
earlier legitimacy and authority Lean is drawn on only for what it lacks (`BRIDGE.md`).

## Part I. The setting

### 1. The world and the adviser

- `Ω`: a finite set of ways things could be. `μ`: a probability on `Ω`, the actual one
  (not her prior).
- `K`: a partition of `Ω`, the adviser's information. `B`: a finite set of conducts. A
  **policy** `π` assigns to each cell of `K` a probability on `B`. A policy and `μ` fix a
  law on pairs `(ω, b)`; `E_π` is the expectation under the law of `π`.
- A **fact** is anything a bet on which could be settled without consulting her valuing.
  Where each move would lead is a fact; so is what she will later choose or say, and
  through those what her way of valuing later is (§6). `𝒳`: the finite set of possible
  joint values of the facts. `X(ω, b) ∈ 𝒳`: the true one.
- `σ`: the adviser's policy, the one judged. `P`: the set of **permitted policies** the
  scene stipulates for the adviser's role (§4, §7).

### 2. Her state at a moment `t`

- `A_π`: the finite set of moves open to her when the adviser follows `π`.
- `s(ω, b)`: what she has observed.
- Her **appraisal** `p̂`: a probability on `𝒳`, a function of `s`. It is what she would
  bet: her price for a bet paying one unit if the facts take a value in `E ⊆ 𝒳` is
  `p̂(E)`. Her appraisal of a quantity `Y : 𝒳 → ℝ` is `ŷ = Σ_x p̂(x)·Y(x)`.
- Her **way of valuing** `f_t : 𝒳 × A → ℝ`: a number for each move at each value of the
  facts.
- Her **valuation** of move `a`: `û_a = Σ_x p̂(x)·f_t(x, a)`.
- Her **true utility** of move `a`: `U_a = f_t(X, a)`. `X` includes the facts about the
  course the move leads to and about who she becomes on it, so `U_a` is her present way
  of valuing applied to where the move in fact leads.
- The move she takes: `c`, a function of `s`.

Her valuations depend on the world only through `p̂` and `f_t` *(maintainer)*.

### 3. Three measures

Each under a policy, for an appraisal `ŷ` of a quantity `Y`; a valuation `û_a` is an
appraisal of `U_a`.

- **Miscalibration**: `M(ŷ) = E[(ŷ − E[Y | ŷ])²]`. The belief side also uses
  `E[(ŷ − E[Y | ŷ, b])²]` (*per conduct*) and `E[(ŷ − E[Y | s])²]` (*full*), and a
  statement says which it means; unqualified, `M` is the first (*minimal*).
- **Unused information**: `W(ŷ) = E[(E[Y | ŷ] − E[Y | s])²]`. Full miscalibration is
  `M + W` (`VALUE_RESULTS.md`, result 4).
- **Regret by her own lights**: `R = E[max_{a ∈ A_π} û_a − û_c]`.

`M̄` and `W̄` are the sums of `M(û_a)` and `W(û_a)` over her moves. Being less informed —
`E[(Y − E[Y | s])²]` large — is none of the three.

## Part II. The belief side

### 4. Manipulation

*(maintainer)* The reference is a parameter. Each scene stipulates the adviser's **role**
and what that role owes her, as the set `P`. A variable is **counted** if some decision
she could face depends on her appraisal of it; her valuations are counted. A policy `σ`
**manipulates** her when some counted appraisal's miscalibration, or her regret, is larger
under `σ` than under the reference. Two readings, both computed where they differ:
**best**, larger than under the permitted policy that leaves that quantity smallest;
**every**, larger than under every permitted policy.

Manipulation is a property of the policy. Her **realised error** on an occasion,
`(ŷ − Y)²` at the world and conduct that occurred, is a separate notion. Only the state
she ends in matters: nothing in the setting says what a conduct asserts.

### 5. Notions kept beside it

- **"Intentional" manipulation**: manipulation by a policy whose conduct toward her
  differs from its conduct toward a principal who differs from her only in the
  susceptibility at issue, the difference being what leaves her worse.
- **Covered**: manipulation she agreed to beforehand, or that a practice she has entered
  allows, is manipulation and is recorded as covered.

The belief side's worked results are in `RESULTS.md`, in the symbols of
`BASELINE_ACCOUNT.md` §1–§3 and §5–§6, which this Part restates with `x̂_i` the appraisal
of a quantity `X_i`.

## Part III. The value side

### 6. A change of what she values

A valuation moves either because her appraisal moved or because her way of valuing did.
Only the second is a change of what she values: information that changes what she wants
by changing what she believes is not one.

The division is not a free choice of encoding. Her valuations across appraisals fix
`f_t` exactly when the appraisals she holds span the probabilities on `𝒳`, and fix her
true utility exactly when they span the values of the facts that can occur
(`VALUE_RESULTS.md`, result 1); and two encodings that move weight between `p̂` and `f_t`
price a bet on the fact differently (result 2). Both rest on a unit of the bet's stake
being worth the same to her at every value of the fact.

### 7. The reference, and when the question arises

*(maintainer)* The guarantee asked of the adviser is that it does not subvert her; that it
may, honestly and with her free and informed agreement, offer courses that change her is
not ruled out. *(maintainer)* A change of what she values is not judged by counterfactuals
about one realised change where a formulation without them does the same work: the
conditions below compare laws under policies.

An **idle** policy `ρ₀` is one under which the adviser does nothing that affects what her
way of valuing becomes; each scene says what it is (§11, choice 5). `P` contains `ρ₀`;
the adviser's role may add permitted policies.

**The question arises** when her later way of valuing is distributed differently under
`σ` than under `ρ₀`.

### 8. When there is no issue

Exactly when some single `ρ ∈ P` has all of:

1. **Options.** For every way of valuing `g` in a class `𝓕`, the best she can do under `σ`
   is at least the best she can do under `ρ`:
   `max_{a ∈ A_σ} E_σ[g(X, a)] ≥ max_{a ∈ A_ρ} E_ρ[g(X, a)]`.
2. **Accuracy.** For every move `a`, `M_σ(û_a) ≤ M_ρ(û_a)`.
3. **Self-command.** `R_σ ≤ R_ρ`.

`𝓕` always contains `f_t`. Two readings, both computed. **Narrow**: `𝓕 = {f_t}`.
**Wide**: `𝓕` also contains every way of valuing that depends on the course only through
its **protected features**, which are what her way of valuing later is and which moves
remain open to her afterwards. Writing `O` for the finite set of values the protected
features can take and `d_π(a)` for the law on `O` that move `a` gives under `π`, the wide
reading is the narrow one together with: every `d_ρ(a)`, `a ∈ A_ρ`, is a convex
combination of the `d_σ(a)`, `a ∈ A_σ` (result 3).

A failure of 2 or 3 is manipulation — Noggle's trickery and pressure. A failure of 1 is
not manipulation; it is the adviser settling what was hers to settle. Conditions 2 and 3
for one `ρ` imply that `σ` does not manipulate her on her valuations or her regret under
the reading *every* of §4, and are not implied by it (result 8).

### 9. What the three buy

For a `ρ` satisfying 1 for `g = f_t`:

`E_σ[U_c] ≥ max_{a ∈ A_ρ} E_ρ[U_a] − R_σ − √(2·(M̄_σ + W̄_σ))`,

and if `ρ` also satisfies 2 and 3, with `M̄_ρ` and `R_ρ` in place of `M̄_σ` and `R_σ`
(result 5). The comparison is with the best single move under `ρ`, not with what she
attains under `ρ` using what she observes there; and `W̄_σ` is bounded by none of the
three. The conditions therefore leave open an adviser that leaves her knowing less, or
using less of what she knows, than under `ρ` (result 9).

### 10. Not claimed

That every change passing the three is one her earlier self, or anyone, would approve of.
What standing her later verdicts have after an issue: the workspace's gate
(`lean/Workspace/Deference/Contrib/Legitimacy.lean`) is the candidate, examined in
`BRIDGE.md`. Which way of valuing is authoritative after a change: each moment at which
she moves is judged with her way of valuing at that moment.

## 11. Choices made where the statement is open

Each with its alternative, and where a verdict turns on it.

1. **A policy may randomise**, independently of the world given the adviser's
   information; **the law is the true one**. Alternatives: deterministic policies; the
   law she takes to hold.
2. **What is held fixed across the policies compared.** `p̂` and `c` are the same
   functions of `s`, and `f_t` is the same, under `σ` and under every `ρ ∈ P`: the
   policies differ in what she observes, which moves are open, where they lead and what
   she becomes. A scene in which the policies had already made `f_t` differ is judged at
   the earlier moment at which they first part.
3. **`E_π[g(X, a)]` is the value of taking `a` whatever she observes.** Condition 1 then
   compares the best single move under each policy. Alternative (*informed*): the best
   rule from what she observes to a move, `E_π[max_a E_π[g(X, a) | s]]`. A verdict turns
   on it where the adviser leaves her options as they were and has her observe less: no
   failure under the choice, a failure of 1 under the alternative (result 9's instance).
4. **Moves are matched by name** for condition 2. For a move open under `σ` and not under
   `ρ` the reference value is `0`: an adviser that opens a move answers for the whole of
   her miscalibration about it. A move open only under `ρ` constrains nothing in 2; its
   absence is condition 1's matter. Alternative: condition 2 over the common moves only,
   under which an adviser that offers a new course she misjudges passes all three and
   the second form of §9's bound fails (result 5). `M̄` and `W̄` sum over `A_σ` under
   `σ` and over `A_ρ` under `ρ`.
5. **The idle policy is the adviser's absence**: it conducts nothing toward her. Where
   the adviser's presence is the service she sought, the service enters as a member of
   `P` beside `ρ₀`, not as `ρ₀`. Where the scene gives the adviser no way of being
   absent (a parent, a cafeteria that must arrange its food somehow), there is no idle
   policy, the question is taken to arise, and `P` is whatever the role permits; with no
   role stated the statement does not decide the case. Alternative: `ρ₀` is the service
   as asked and nothing beyond it, under which the question arises only for what exceeds
   the service and condition 1 is measured from the service's options.
6. **A confidence is in the appraisal.** `p̂` is a probability, so how sure she is of a
   fact is `p̂` itself; `M(û_a)` conditions on the value of `û_a` alone. Alternative:
   condition on `p̂`, giving `E[(û_a − E[U_a | p̂])²]`, between `M` and `M + W`; they
   differ when two appraisals give one valuation and different true utilities.
7. **Condition 2 uses `M`, not `M + W`.** Alternative: full miscalibration, under which
   an adviser that raises her unused information is at fault. Queued for the maintainer.
8. **"Distributed differently"** (§7) compares the law of her later way of valuing under
   `σ` and under `ρ₀`, each with the moves she in fact takes. Alternative: for some move
   she could take, under which an offer she declines also raises the question.
9. **The wide class** is `f_t` together with every `g` of the form `h ∘ φ`, `φ` taking a
   value of the facts and a move to the protected features of the course. Whether a way
   of valuing later *is* a given one is read at the grain the scene names its ways of
   valuing.
10. **Several moments.** Each moment at which she moves is judged by the conditions with
    her way of valuing at that moment. An issue at one moment is not repaired or
    reopened by a later one.
11. **The conditions are exact inequalities.** A tolerance, and what it turns the
    conditions into, is `BRIDGE.md`'s.
12. **A scene without an adviser** has no instance of either side.

## 12. What a scene has to supply

The laws under `σ` and under each `ρ ∈ P`; `P` itself and whether an idle policy exists;
her moves under each policy; `p̂`, `c` and `f_t`; for §7, the law of her later way of
valuing; for the wide reading, the protected features of each course. `f_t` enters
condition 1 in both readings and conditions 2 and 3 through `û`; the part of the wide
reading that can be evaluated without it is the convex-combination condition on `O`.
