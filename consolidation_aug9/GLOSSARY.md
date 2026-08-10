# Glossary

Canonical vocabulary and notation for this package, plus the mapping tables that
let the vendored documents be read against it.

## 1. Canonical terms

| term | meaning |
|---|---|
| **settlement engine** | the mechanism's world-channel: it supplies reports, timing, and enforcement, and nothing else |
| **reports** | what the engine writes into the settled record |
| **timing** | when the engine writes |
| **enforcement** | the weight standing behind what the engine writes |
| **settlement event** | a dated record event pairing a report variable with a value from its procedure's declared outcome space |
| **report variable** | the variable of a declared procedure executed at a date; its identity carries which procedure and when |
| **settled record** | the accumulated settlement events; incorrigible, and exempt from every answerability column |
| **coherence polytope** | logic plus the settled record, and nothing else: what an engine's prices are obliged to be near |
| **docket polytope** | the coherence polytope plus the book's endorsements: what the docket computes intervals against |
| **endorsement** | one compiled book commitment, a one-sided constraint on the credal state |
| **credal interval** | the exact rational minimum and maximum of a target's probability over a constraint set |
| **incoherence** | the minimal uniform distance from a displayed price assignment to the coherent assignments |
| **`e`-coherent** | having incoherence at most `e` |
| **working tolerance** | a declared tolerance under which the robust interval can still strictly separate for some non-empty book |
| **downside limit** | the worldwise loss guarantee an engine gives against the book's holdings |
| **core minimum** | the certified enforcement coefficient, written `theta_min` |
| **core condition** | containment of the homothet of the reference in the endorsed region |
| **relative reading** | the core condition read against the post-settlement simplex |
| **ambient reading** | the core condition read against the whole simplex; unsatisfiable once anything is settled |
| **clipping adapter** | the per-date program restricting the reference to the admissible region, with quarantine of operative force on emptiness |
| **compiler contract** | the four mechanism-side hypotheses with no interface counterpart |
| **judge footprint** | the record tables an objection type's judge may read, split by kind |
| **necessity witness** | a displayed instance showing a named condition cannot be dropped |
| **reading audit** | a clause-by-clause reading of a candidate's source against a specification; the weakest evidence class in this package |
| **chargeable pattern** | the sanctioned term for a responsiveness failure that is priced rather than forbidden |

## 2. Retired terms

<!-- gate:exempt -->
*The two tables below are the one place in this package permitted to write the
retired words, since naming them is their whole function. The exemption is
delimited by markers the runner reads, it is available to this document only,
and the runner fails if any other document opens it or if a region is left
open. See `DEVIATIONS.md` 4.*

| retired | canonical here | why |
|---|---|---|
| pen / clock / purse | reports / timing / enforcement | the triple was picturesque and opaque; the plain terms say what each supplies |
| pin | settlement event | *pin* is reserved for settlement; repository artifacts are **frozen** (frozen digests, frozen inputs, frozen consolidation) |
| pinned (of a file or digest) | frozen | same reservation |
| coherence defect | incoherence | the natural word is on the naming gate's retired list; the referent is unchanged |
| enforcement floor | downside limit (for the worldwise guarantee); certified tolerance (for a tolerance certification) | the gate retires the word, and the two uses were being conflated anyway — one is a loss guarantee, the other an upper limit on incoherence |
| floor `theta_min` | core minimum | as above |
| the core coefficient written with the first Greek letter | `theta` | the gate retires that letter; the source tree's joint layer already wrote `theta` |
| kernel (as a structure of the mechanism) | mechanism | the previous consolidation's own retirement, carried |

The retirements in the lower half of this table originate in the source tree's
naming gate, which this package's runner enforces over every non-vendored
document. The gate is mechanical and unforgiving; it is also the reason the
vendored interface documents are vendored rather than incorporated.

## 3. Reading the vendored documents against this package

The vendored interface draft, its changelog, and the reading audit use the
retired vocabulary throughout. They are frozen evidence and are never edited.
Read them with this table.

| vendored text says | this package says |
|---|---|
| pen, clock, purse | reports, timing, enforcement |
| pin, pinned (of a settlement) | settlement event, settled |
| pinned (of a digest or input) | frozen |
| coherence defect, defect functional | incoherence, the incoherence functional |
| enforcement floor, downside floor `-B` | downside limit `-B` |
| floor `theta_min`, `theta_min` floor | core minimum `theta_min` |
| the first Greek letter, as the bundle's core coefficient | `theta` |
| proof kernel | proof checker |
| SI⁻ | SI-minus |
| Δ₁ … Δ₄ | D1 … D4 |

<!-- gate:end -->

## 4. Clause letters

The clause letters are **frozen opaque identifiers**: entrenched in the reading
audit, in the correspondence table of Theory 12, and in the verifier's predicate
names. Prose carries the real names; this table is the mapping.

| letter | subject |
|---|---|
| `J1`, `J2`, `J3` | reports: the declared settleable class; write-once and owner-only; transport under migration |
| `C1`, `C2`, `C3` | timing: completeness split by channel; ripeness and tolling; adequacy |
| `P1`, `P2`, `P3`, `P4` | enforcement: the core minimum; the downside limit; finite gating; the declared certificate type |
| `T1`, `T2` | tolerance: the schedule and its non-vacuity; certification layering |
| `F1` … `F4` | conduct: request-keyed subsidy; stopping neutrality; probe blackout; funder provenance |
| `S8-logical` | proof-carrying settlements on the logical channel |

## 5. Notation

| symbol | meaning |
|---|---|
| `W` | the finite world set |
| `p` | a credal state: a probability assignment over `W` |
| `P` | the post-settlement simplex, in core-condition contexts |
| `S` | the endorsed region inside `P` |
| `q` | the compiler's reference |
| `theta` | the core coefficient; `theta_min` the certified minimum |
| `kappa` | `(1 - theta)/theta` |
| `e`, `e_t` | a tolerance and a declared tolerance schedule |
| `E` | the quote-error total; `R` the risk guard; `M` the ordinary movement limit |
| `U_m` | the movement cap after `m` reference jumps |
| `Psi_0` | the initial consuming potential, limiting book changes |
| `m*` | the number of core-invalidating book changes |
| `Dec(D)` | the decidable fragment of a declared process |
| `D_inf` | the union of what a declared process emits |
