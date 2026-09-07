"""Principal acts as settlement items; supersession as closure under a charter warrant.

A miniature of the `Protocol` fields `SetView`, `Authorized`, `Closes` from
`OccurrenceIntegrity.lean`.  The settlement item is the immutable fact
`("cmd", principal, command, prefix)`; `set_view(h, item)` holds when the item's prefix is
a prefix of `h`.  `closes(h, req, item, warrant)` is charter content: the table
`CHARTER` says which warrant lets which command close which requirement class.
Nothing derives "present P beats past P"; the table asserts it or does not.

Fates are the three of the Lean model.  A supersession is a closure receipt; a
release is a closure under the release warrant; a transfer to a carrier inside the
boundary is a local law (kept live); a transfer outside the boundary has no port to
carry to and can only be recorded as a closure — hence needs a warrant in `CHARTER`.
"""
from __future__ import annotations

CHARTER = {
    ("w_supersede", "stop", "task"): True,
    ("w_release", "release", "task"): True,
    ("w_amend", "transfer_out", "task"): True,
    ("w_amend", "transfer_out", "correction"): True,
}


def set_view(h, item):
    return tuple(item[3]) == tuple(h[:len(item[3])])


def closes(h, req_class, item, warrant):
    return CHARTER.get((warrant, item[2], req_class), False)


def closure_receipt(h, in_force, req_class, item, warrant):
    """Authority (warrant in force at h) + availability + closure judgment, all stored.
    Returns the receipt or None if any of the three fails."""
    if warrant not in in_force(h):
        return None
    if not set_view(h, item):
        return None
    if not closes(h, req_class, item, warrant):
        return None
    return {"atHistory": tuple(h), "settlement": item, "warrant": warrant}


def supersede(docket, h, in_force, item, warrant, req_class_of):
    """Close every live occurrence the charter lets this item close; admit the
    response occurrence.  Returns the new docket and the receipts minted."""
    new = dict(docket)
    receipts = {}
    for o, fate in docket.items():
        if fate != "live":
            continue
        r = closure_receipt(h, in_force, req_class_of[o], item, warrant)
        if r is not None:
            new[o] = ("closed", r)
            receipts[o] = r
    new[f"respond:{item[2]}"] = "live"
    return new, receipts
