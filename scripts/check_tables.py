"""Independently decode the three historical table archives without invoking Lean."""
import argparse
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import zipfile

from artifacts import ROOT, checked_archive, manifest


def unpack(archive, dest):
    with zipfile.ZipFile(archive) as z:
        for item in z.infolist():
            rel = PurePosixPath(item.filename)
            target = dest.joinpath(*rel.parts)
            if rel.is_absolute() or ".." in rel.parts or not target.resolve().is_relative_to(dest.resolve()):
                raise ValueError("Invalid archive path")
            if item.is_dir():
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            with z.open(item) as src, target.open("wb") as out:
                shutil.copyfileobj(src, out)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--assets", type=Path, help="directory containing the three original ZIPs and the STop readback inputs")
    args = ap.parse_args()
    version = manifest("sources.json")["release"]
    upstream = json.loads((ROOT / "receipts/upstream-sources.json").read_text())
    checks = ROOT / "tools/tables"
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        for key in ("sg5", "sgz5r", "stop"):
            unpack(checked_archive(upstream[key], version, args.assets), base / key)
        unpack(checked_archive(manifest("stop-readback.json"), version, args.assets), base / "inputs")
        sg5 = Path("cap_bank_source/verify_bundle.py")
        if (base / "sg5" / sg5).read_bytes() != (checks / "sg5" / sg5).read_bytes():
            raise ValueError("Original SG5 checker differs from version control")
        commands = [
            [base / "sg5" / sg5],
            [checks / "sgz5r/wide_production_source/audit_export.py", base / "sgz5r/wide_production_source/export"],
            [checks / "stop/tools/verify_rendered_stop_cap.py", base / "stop",
             base / "inputs/staged_compact_only.bin", base / "inputs/exact_stop_cap_projection.txt",
             base / "inputs/predecessor.zip"],
        ]
        for cmd in commands:
            subprocess.run([sys.executable, "-I", "-X", "utf8", *cmd], check=True)


if __name__ == "__main__":
    main()
