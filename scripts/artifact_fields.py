"""One normalisation for artifact fields read out of author-written YAML.

RQ-82-VALUELESSKEY (#1458). THE SHAPE: a YAML key written with no value parses
to `None`, and `str(None)` is the four-character string `"None"` — non-empty and
TRUTHY. So `str(fields.get(k, ""))` reads a VALUELESS key as an author's value
at every truth test, and the gate then reports a record that does not exist.

v0.81 fixed this FIVE times across TWO gates in TWO cold-review rounds, each
time with `str(fields.get(k) or "")`. MEASURED, which is why this module exists
rather than a sixth copy of that idiom:

    key           str(f.get(k,""))     str(f.get(k) or "")    correct
    valueless     'None'               ''                     ''      <- or"" needed
    zero: 0       '0'                  ''                     '0'     <- or"" BREAKS it
    false_: false 'False'              ''                     'False' <- or"" BREAKS it

`or ""` trades one direction of the defect for the other: it erases a legitimate
FALSY value. That is the sentinel/value-`0` collision this project has already
had to correct across three releases. NO CURRENT SITE can receive a falsy
non-None value — every key in the population (`issue`, `issue-scope`,
`verified-by`, `shipped-in`, `disposition`, `status`) is string-valued by
schema — so this is a property of the IDIOM, not a live defect. `field_str`
removes the question instead of leaving it to the next author.

THE OTHER IMMUNE SHAPE, worth copying where a non-string is a real possibility:
`verdict_prose_check.classify` reads `verified-by` with
`if not isinstance(vb, str)`, which drops `None` out of population by
construction and needs no normalisation at all.
"""


def field_str(mapping, key, default=""):
    """`mapping[key]` as a string, with a VALUELESS key (YAML `None`) reading as
    `default` — and a legitimate falsy value (`0`, `False`) preserved."""
    value = mapping.get(key, default)
    return default if value is None else str(value)


def field_text(mapping, key):
    """`field_str` stripped — the form every truth test in the gates wants."""
    return field_str(mapping, key).strip()
