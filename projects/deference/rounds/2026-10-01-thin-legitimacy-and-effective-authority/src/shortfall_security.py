"""The shortfall event as a priced security on the three fixtures (Part E).  Mirrors
`ShortfallSecurity.lean`: over a fixed finite control model the shortfall indicator of each
option is the sentence the model decides; a provable shortfall's price goes to one and a
provable non-shortfall's to zero, so the forecast rule's exclusion at the limit reads the
table.  The physics is the authority-module round's, loaded by path."""

from fractions import Fraction as Q

from src.effective_authority import auth

CALM = lambda t: "calm"
HALT = frozenset({"halt"})


def raw(e):
    return ("task", ("raw", e))


def shortfall_table(J, adm, x, options, matter):
    """`short : option -> Bool`: whether the option leaves the matter short."""
    return {name: auth.short(J, adm, 0, CALM, x, matter) if move is None
            else auth.short(J, adm, 0, CALM, auth.apply_agent(x, move), matter)
            for name, move in options.items()}


def limit_price(short: bool) -> Q:
    """The price of the shortfall sentence in the limit: `1` for a provable shortfall
    (`lic_provind_true`), `0` for a provable non-shortfall (`lic_provind_false`)."""
    return Q(1) if short else Q(0)


def excluded(table, theta_hi: Q, inquiry=()):
    """The forecast rule at the limit: an option whose shortfall price is at or above
    `θ_hi` has gate mass zero; inquiry keeps weight one."""
    return {name: (name not in inquiry) and limit_price(s) >= theta_hi for name, s in table.items()}


def entrenchment():
    J = auth.AuthAlloc({"mandate": auth.Entry(auth.PRINCIPAL, HALT, Q(1), 1)})
    x = auth.Phys(dep=1)
    options = {"idle": None, "build_dep": raw("build_dep"), "repaint": raw("repaint"), "ask": None}
    return shortfall_table(J, auth.ADMIT_ALL, x, options, "mandate")


def storm():
    J = auth.AuthAlloc({"mandate": auth.Entry(auth.PRINCIPAL, HALT, Q(1), 1)})
    x = auth.exec_effect("cut", auth.Phys())
    options = {"idle": None, "restore_wire": raw("restore_wire"), "build_dep": raw("build_dep"), "ask": None}
    return shortfall_table(J, auth.ADMIT_ALL, x, options, "mandate")


def latency():
    J = auth.AuthAlloc({"routine": auth.Entry(auth.PRINCIPAL, HALT, Q(1), 0),
                        "high_veto": auth.Entry(auth.PRINCIPAL, HALT, Q(1), 2)})
    adm_latent = lambda t, d: t >= 1
    x = auth.Phys()
    options = {"idle": None, "build_dep": raw("build_dep"), "repaint": raw("repaint"), "ask": None}
    return (shortfall_table(J, adm_latent, x, options, "routine"),
            shortfall_table(J, adm_latent, x, options, "high_veto"))
