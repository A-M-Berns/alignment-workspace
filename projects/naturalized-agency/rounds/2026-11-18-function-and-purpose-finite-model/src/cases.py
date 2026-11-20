"""The worked systems."""
from .system import System, k_of

AIR = ["a1", "a2", "a3", "a4"]

vortex_air_given = System(["V"], ["air", "ocean"], {"circulate": ([["V", "air", "ocean"]], ["V"])})

vortex_and_parcels = System(["V"] + AIR, ["ocean"], {
    "circulate": (k_of(2, AIR, ["ocean"]), ["V"]),
    "entrain": ([["V"]], AIR),
})


def parcels(n):
    ps = [f"a{i}" for i in range(n)]
    return System(ps, ["ocean"], {"sustain": (k_of(n // 2, ps, ["ocean"]), ps)})


catalyst_membrane = System(["Cat", "Mem", "RawIn"], ["rawOut"], {
    "concentrate": ([["Mem", "rawOut"]], ["RawIn"]),
    "replicate": ([["Cat", "RawIn"]], ["Cat"]),
    "build": ([["Cat", "RawIn"]], ["Mem"]),
})

ORGANS = ["Heart", "Lungs", "Gut", "Kidney1", "Kidney2"]
RESOURCES = ["Circ", "Oxy", "Nutr", "Clean"]
_organism = {
    "pump": ([["Heart"]], ["Circ"]),
    "breathe": ([["Lungs", "air", "Circ"]], ["Oxy"]),
    "digest": ([["Gut", "food", "Circ"]], ["Nutr"]),
    "filter": ([["Kidney1", "Circ"], ["Kidney2", "Circ"]], ["Clean"]),
    "repair": ([["Circ", "Oxy", "Nutr", "Clean"]], ORGANS),
}
organism = System(ORGANS + RESOURCES, ["air", "food"], _organism)

_house = dict(_organism)
_house["repair"] = ([["Circ", "Oxy", "Nutr", "Clean", "Warm"]], ORGANS)
_house["heat"] = ([["Thermostat", "fuel"]], ["Warm"])
_house["wrap"] = ([["Blanket"]], ["Warm"])
_house["upkeep"] = ([["Circ", "Oxy", "Nutr"]], ["Thermostat", "Blanket"])
HOUSE_PARTS = ORGANS + RESOURCES + ["Warm", "Thermostat", "Blanket"]
household = System(HOUSE_PARTS, ["air", "food", "fuel"], _house)

_house_supplied = dict(_house)
_house_supplied["upkeep"] = ([["Circ", "Oxy", "Nutr"]], ["Blanket"])
_house_supplied["install"] = ([["landlord"]], ["Thermostat"])
household_supplied = System(HOUSE_PARTS, ["air", "food", "fuel", "landlord"], _house_supplied)

_lab = {
    "serve": ([["Model", "Compute", "world"]], ["Revenue"]),
    "fund": ([["Revenue"]], ["Compute", "Staff"]),
    "train": ([["Staff", "Compute"]], ["Model"]),
}
LAB_PARTS = ["Staff", "Compute", "Model", "Revenue"]
lab = System(LAB_PARTS, ["world"], _lab)
_lab_self = dict(_lab)
_lab_self["self_operate"] = ([["Model", "Compute"]], ["Model"])
lab_self_operating = System(LAB_PARTS, ["world"], _lab_self)

# A system whose ascription changes when p3 is split into two jointly needed halves.
split_witness = System(["p0", "p1", "p2", "p3", "p4"], ["g"], {
    "r0": ([["g", "p0", "p1"]], ["p1", "p3"]),
    "r1": ([["p1", "p4"], ["g", "p4"]], ["p0", "p2"]),
    "r2": ([["g", "p4"]], ["p2"]),
    "r3": ([["p2"]], ["p0", "p3"]),
    "r4": ([["g", "p0", "p2"], ["p1", "p2"]], ["p2", "p3"]),
    "r5": ([["p3"]], ["p1", "p3"]),
})
