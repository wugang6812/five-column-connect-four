"""Recreate the six source assets of the tagged release from a materialized checkout."""
import argparse
import tempfile
import zipfile
from pathlib import Path

from artifacts import LEAN, manifest, sha256


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out
    out.mkdir(exist_ok=True, parents=True)
    specs = manifest("sources.json")["assets"]
    files = manifest("modules.json")
    for group, spec in specs.items():
        dest = out / spec["name"]
        with tempfile.TemporaryDirectory(dir=out) as temp:
            archive = Path(temp) / dest.name
            with zipfile.ZipFile(archive, "w") as z:
                for name, (expected, key) in sorted(files.items(), key=lambda item: item[0][:-5].replace("/", ".")):
                    if key != group:
                        continue
                    source = LEAN / name
                    if sha256(source) != expected:
                        raise ValueError(f"Source changed: {name}")
                    entry = zipfile.ZipInfo(name, (2026, 11, 25, 0, 0, 0))
                    entry.create_system = 0
                    entry.external_attr = 0o100644 << 16
                    z.writestr(entry, source.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=7)
            if sha256(archive) != spec["sha256"]:
                raise ValueError(f"{dest.name}: archive digest differs (including compressor version)")
            if dest.exists() and sha256(dest) != spec["sha256"]:
                raise FileExistsError(f"Refusing to replace a different archive: {dest}")
            archive.replace(dest)
            print(dest)


if __name__ == "__main__":
    main()
