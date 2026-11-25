"""Fetch versioned public proof data and verify it before installing any member."""
import hashlib
import json
import os
import re
import shutil
import tempfile
import urllib.request
import zipfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
STATE = ROOT / ".replay"


def manifest(name):
    return json.loads((ROOT / "certificates" / name).read_text(encoding="utf-8"))


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def checked_archive(spec, release, offline):
    name = spec["name"]
    if not re.fullmatch(r"[A-Za-z0-9_.-]+\.zip", name) or not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+", release):
        raise ValueError("Invalid release asset name or version")
    folder = offline if offline is not None else STATE / "downloads"
    dest = folder / name
    if not dest.exists() and offline is None:
        folder.mkdir(parents=True, exist_ok=True)
        url = f"https://github.com/wugang6812/five-column-connect-four/releases/download/{release}/{name}"
        temp = None
        try:
            with tempfile.NamedTemporaryFile(dir=folder, delete=False) as out:
                temp = Path(out.name)
                with urllib.request.urlopen(url, timeout=120) as response:
                    shutil.copyfileobj(response, out)
            if temp.stat().st_size != spec["size"] or sha256(temp) != spec["sha256"]:
                raise ValueError(f"Downloaded archive failed verification: {name}")
            os.replace(temp, dest)
        finally:
            if temp is not None:
                temp.unlink(missing_ok=True)
    if not dest.is_file() or dest.stat().st_size != spec["size"] or sha256(dest) != spec["sha256"]:
        raise ValueError(f"Missing or mismatched archive: {dest}")
    return dest


def unpack(archive, target, members, suffix):
    """Only allow exact inventoried members, including their content hashes."""
    with zipfile.ZipFile(archive) as z:
        if len(z.namelist()) != len(members) or set(z.namelist()) != members.keys():
            raise ValueError(f"Archive member list mismatch: {archive.name}")
        for name, digest in members.items():
            rel = PurePosixPath(name)
            if not re.fullmatch(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)*" + re.escape(suffix), name):
                raise ValueError(f"Invalid module path: {name}")
            dest = target.joinpath(*rel.parts)
            if not dest.resolve().is_relative_to(target.resolve()):
                raise ValueError(f"Destination outside module directory: {name}")
            if dest.exists():
                if sha256(dest) != digest:
                    raise ValueError(f"Modified local file: {dest}")
                continue
            data = z.read(name)
            if hashlib.sha256(data).hexdigest() != digest:
                raise ValueError(f"Archive member hash mismatch: {name}")
            dest.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(dir=dest.parent, delete=False) as out:
                tmp = Path(out.name)
                out.write(data)
            try:
                os.replace(tmp, dest)
            finally:
                tmp.unlink(missing_ok=True)


def sources(offline):
    files = manifest("modules.json")
    info = manifest("sources.json")
    for key, spec in info["assets"].items():
        entries = {name: h for name, (h, group) in files.items() if group == key}
        if len(entries) != spec["members"]:
            raise ValueError(f"Invalid source count for {key}")
        unpack(checked_archive(spec, info["release"], offline), LEAN, entries, ".lean")
    for name, (digest, _) in files.items():
        if sha256(LEAN / name) != digest:
            raise ValueError(f"Published source hash mismatch: {name}")
    return files


def replay_cache(offline, target):
    info = manifest("replay-cache.json")
    for name, digest in info["binds"].items():
        if sha256(ROOT / name) != digest:
            raise ValueError(f"Source snapshot differs from the one used for the replay cache: {name}")
    members = manifest("objects.json")
    if len(members) != info["archive"]["members"]:
        raise ValueError("Replay object count mismatch")
    unpack(checked_archive(info["archive"], info["release"], offline), target, members, ".olean")
