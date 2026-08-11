# The house checker harness

**Specification layer. Maintainer-owned. Contributors never modify anything here,
and contributors never ship the thing that certifies a registered claim.**

There is no kernel for Python, so this is the substitute: an untrusted prover, a
small trusted judge, and a certificate between them. A contributor supplies
*data* — a witness, or the parameters of a finite domain — and a checker here
decides. The checker is fixed, generic, and short enough to read.

Every checker obeys four rules.

1. **Stdlib only.** Zero third-party imports. The judge's dependency surface is
   the Python standard library and nothing else.
2. **Exact arithmetic.** `fractions.Fraction`. No floats anywhere in a verdict
   path.
3. **Short enough to read in minutes.** If a checker cannot be audited over
   coffee, it is not a judge, it is another program to be suspicious of.
4. **A meaning docstring.** Each states precisely what a passing verdict does and
   does not establish. A checker that passes tells you exactly that sentence and
   nothing more.

New checkers are rare, maintainer-written or maintainer-adopted, and each is a
dated `DECISIONS.md` entry.

## The initial set

| id | what it decides |
|---|---|
| `witness` | a supplied instance satisfies a stated property |
| `enumeration` | a property holds pointwise over a domain **the checker generates itself** from supplied parameters |
| `registry` | the claims registry is internally consistent and every entry's statement of record resolves |

## Running

```sh
python3 -m checkers.run CLAIMS.md      # every registered claim in a registry
python3 -m checkers.run --self-test    # the harness's own tests
```
