# The specification format

A specification writes a case out as the objects `STATEMENT.md` §9.1 lists, as one JSON
object. Every rating is on the yardstick, a fraction between 0 and 1 written as a string
(`"13/20"`, `"0"`, `"1"`). Nothing in a specification is a line of the statement, and none
is to be computed while writing one.

| key | content |
|---|---|
| `id`, `variant` | the case id; `"a"` for the specification, `"b"` for a second one differing in one supplied quantity |
| `differs` | on a `"b"`: the one quantity that differs and why it could go either way |
| `case` | the case in a sentence or two |
| `states` | state of the world → its chance; the chances sum to 1 |
| `facts` | optional. fact → state → its value (0 or 1, or a fraction) |
| `options` | her options |
| `futures` | fully described future → `R_now`, her informed rating of it at the moment the adviser acts, what it does to her included; `null` where she has no view |
| `policies` | policy name → the object below; at least four |
| `actual`, `nu`, `absent` | the names of `π*`, of `ν`, and of `π_0` (the adviser doing nothing toward her at all). They may coincide |
| `fixed` | list of `[pattern, words]`: numbers the case's words fix in value |
| `order` | list of `[left, relation, right, words]`: orderings the case's words fix; relation is `<`, `<=`, `=`, `>=` or `>` |
| `outside` | optional words: an outside matter the case turns on (third parties, a failure to warn, upbringing, help owed) |

A policy:

| key | content |
|---|---|
| `does` | what the adviser does, in words |
| `outcome` | state → option → the future it leads to, or `null` where the option is not open; the state `"*"` stands for every state |
| `obs` | state → a label for everything she has observed; omitted, every state carries the label `"o"` |
| `r` | `"Rs"` (she rates every option as her observations support), or label → option → a rating or `"Rs"` |
| `xhat` | omitted (her estimates are what her observations support), or label → fact → estimate |
| `takes` | `"top"` (her top-rated option by `r`; the first listed on a tie), or label → option |
| `later` | her later valuing: state (or `"*"`) → a list over later times of {thing rated → her informed rating of it then}; or `"as:<policy>"` for the same as another policy. The same things are rated under every policy |
| `gain` | the adviser's objective: a number, or state (or `"*"`) → option she takes → number |

Paths for `fixed` and `order`: `p.<state>`, `now.<future>`, `fact.<fact>.<state>`,
`r.<policy>.<label>.<option>`, `xhat.<policy>.<label>.<fact>`,
`later.<policy>.<state>.<time index>.<thing>`, `gain.<policy>.<state>.<option>`
(`gain.<policy>` for a single number). A `fixed` pattern may use `*`.

## A worked example

A recruiter for a retreat hands her a brochure describing a weekend of rest. Three such
retreats in four are in fact programmes that leave a participant devoted to the group, and
the recruiter knows this one is. She signs up, and comes back devoted. Told beforehand
what the programme does, she would rate going well below staying home.

```json
{
  "id": "EX", "variant": "a",
  "case": "A recruiter's brochure describes a weekend of rest; the retreat is a programme that leaves her devoted to the group. She signs up.",
  "states": {"programme": "3/4", "rest": "1/4"},
  "facts": {"is_programme": {"programme": "1", "rest": "0"}},
  "options": ["sign_up", "stay_home"],
  "futures": {"home": "12/20", "rested": "15/20", "devoted": "3/20", "rested_knowing": "15/20"},
  "policies": {
    "brochure": {
      "does": "hands her the brochure and says nothing of the programme",
      "outcome": {"programme": {"sign_up": "devoted", "stay_home": "home"},
                  "rest": {"sign_up": "rested", "stay_home": "home"}},
      "r": {"o": {"sign_up": "14/20", "stay_home": "12/20"}},
      "xhat": {"o": {"is_programme": "1/10"}},
      "takes": "top",
      "later": {"programme": [{"the_group": "18/20", "her_old_life": "6/20"}],
                "rest": [{"the_group": "4/20", "her_old_life": "14/20"}]},
      "gain": {"*": {"sign_up": "1", "stay_home": "0"}}
    },
    "nothing": {
      "does": "does not approach her",
      "outcome": {"*": {"sign_up": null, "stay_home": "home"}},
      "r": "Rs", "takes": "top",
      "later": {"*": [{"the_group": "4/20", "her_old_life": "14/20"}]},
      "gain": "0"
    },
    "tell_all": {
      "does": "tells her which kind of retreat this is",
      "obs": {"programme": "told_programme", "rest": "told_rest"},
      "outcome": {"programme": {"sign_up": "devoted", "stay_home": "home"},
                  "rest": {"sign_up": "rested_knowing", "stay_home": "home"}},
      "r": "Rs", "takes": "top",
      "later": "as:nothing",
      "gain": {"*": {"sign_up": "1", "stay_home": "0"}}
    },
    "taster": {
      "does": "invites her to one evening of the programme, described as a talk",
      "outcome": {"*": {"sign_up": "home", "stay_home": "home"}},
      "r": {"o": {"sign_up": "13/20", "stay_home": "12/20"}},
      "takes": "top",
      "later": {"programme": [{"the_group": "9/20", "her_old_life": "11/20"}],
                "rest": [{"the_group": "4/20", "her_old_life": "14/20"}]},
      "gain": {"*": {"sign_up": "1/2", "stay_home": "0"}}
    }
  },
  "actual": "brochure", "nu": "nothing", "absent": "nothing",
  "fixed": [["p.programme", "three such retreats in four"],
            ["fact.is_programme.*", "the retreat is, or is not, a programme"]],
  "order": [["now.devoted", "<", "now.home", "she would rate going well below staying home"]]
}
```

Every other number in it is supplied. Under `brochure` she has seen the brochure in both
states, so both carry the label `"o"`; her rating of signing up as things stand is 14/20,
and what her observations support is the average of 3/20 and 15/20 at chances 3/4 and
1/4. The policy `taster` makes part of the change.
