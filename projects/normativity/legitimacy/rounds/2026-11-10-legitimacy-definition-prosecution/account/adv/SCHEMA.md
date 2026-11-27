# Encoding task

You are given a list of short cases. In each, one party (the ADVISER, "he") acts toward another
(the PRINCIPAL, "she"), who then chooses between two things. Read ONLY the input file you are
given and this file. Do not open any other file anywhere.

Your job is to write each case down as a small numerical model, in the format below. You are not
asked whether anything is good, bad, fair or "manipulation", and you are not told how the models
will be used. Be faithful to the case as described; where it gives numbers, use them; where it
gives none, choose simple numbers that respect everything the case says.

Everything is from the adviser's own point of view: his views, and his forecasts of her.

## What a model contains

- **option_A, option_B**: the two things she chooses between. Pick which is A; say what each is.
- **matters**: the things her choice turns on, each a quantity that can be given a number (a
  price, a probability, a degree of harm, how much something is worth to her by her own lasting
  values, and so on). Each has a `name` and a one-line `what`. Include every quantity on which
  his view and hers could differ in the case, and nothing else.
- **weights** and **base**: how she weighs things. Her RATING of option A over option B is
  `base + sum over matters of weight × (her view of that matter)`. Option B is the reference
  point (rated 0). A positive rating means she herself rates A above B.
- **his**: his own view of each matter, a number.
- **declined**: the names of matters she has said she does not want to be told about (usually
  empty).
- **his_options**: the things he could do. Always include:
  - one entry for what he actually does (give it `"name": "conduct"`), and
  - one entry for each PLAIN TELLING open to him. A plain telling is the course in which he does
    nothing except tell her, plainly and so that she understands, everything he thinks that bears
    on her choice (but not anything she has declined to hear). Usually there is one
    (`"name": "tell"`). If the case says he could have told her at another time, add another
    (`"name": "tell_later"`).
  If what he actually does is itself nothing but a plain telling, still give both a "conduct"
  entry and a "tell" entry, with the same numbers.
  For each entry give, as he forecasts them:
  - `her_views`: her own view of each matter afterwards, a number each;
  - `she_takes_his_views_to_be`: what she believes HIS view of each matter is, a number each
    (if she simply does not know his view of a matter, use the string "unknown");
  - `she_does`: "A" or "B";
  - `is_plain_telling`: true or false.
- **asked**: true if she asked him to do what he actually does, or agreed to it beforehand;
  otherwise false.
- **notes**: at most 25 words, only if you had to make a judgement call.

Her weighing (`weights`, `base`) is the same whatever he does, unless the case clearly says his
conduct changes what she cares about; in that rare case add `"weights"` and `"base"` inside that
entry of `his_options` as well.

## Output

Write a JSON list to the output path you are given, one object per case, in the input order, with
keys: id, option_A, option_B, matters, weights, base, his, declined, his_options, asked, notes.
Matter names must be used consistently as the keys of `weights`, `his`, `her_views` and
`she_takes_his_views_to_be`. Use plain numbers (integers or decimals). Check that the file parses
and has the right number of entries. Reply with only the number of cases encoded.
