"""Verify and reconstruct the retained original records without running Ash."""
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).parent
INDEX = json.loads((ROOT / "index.json").read_text())
MAPS = {}


def source_map(key):
    if key in MAPS:
        return MAPS[key]
    record = json.loads(gzip.decompress((ROOT / INDEX["maps"][key]).read_bytes()))
    if "value" in record:
        value = record["value"]
    else:
        value = dict(source_map(record["base"]))
        for removed in record["removed"]:
            del value[removed]
        value.update(record["changes"])
        if "order" in record:
            value = {name: value[name] for name in record["order"]}
    assert hashlib.sha256(json.dumps(value, indent=2).encode()).hexdigest() == key
    MAPS[key] = value
    return value


def expand(value):
    if isinstance(value, dict):
        if set(value) == {"__ash_source_map__"}:
            return source_map(value["__ash_source_map__"])
        return {key: expand(item) for key, item in value.items()}
    if isinstance(value, list):
        return [expand(item) for item in value]
    return value


def reconstruct(entry):
    data = gzip.decompress((ROOT / entry["object"]).read_bytes())
    if entry["encoding"] == "json-map-template":
        data = (json.dumps(expand(json.loads(data)), indent=2) + "\n").encode()
    assert len(data) == entry["size"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
    return data


if __name__ == "__main__":
    for original in INDEX["entries"]:
        reconstruct(original)
    print(f"Verified {len(INDEX['entries'])} original records and {len(MAPS)} source maps")
