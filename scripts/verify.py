"""Replay the public Lean proof (Python 3.11+, official Lean toolchain)."""
import argparse
import concurrent.futures
import json
from graphlib import TopologicalSorter
import os
import platform
import re
import subprocess
import tempfile
from pathlib import Path

from artifacts import LEAN, ROOT, STATE, manifest, replay_cache, sources

COMMIT = "6a10ac8c22beadecabdbb0919c2b50214762f91d"
ENDPOINTS = ("five_columns_even_draw", "five_columns_draw", "five_columns_neither_player_wins")
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB = (
    "Mathlib.Algebra.BigOperators.Fin", "Mathlib.Algebra.Order.BigOperators.Group.Finset",
    "Mathlib.Data.Fin.VecNotation", "Mathlib.Data.Fintype.BigOperators",
    "Mathlib.Tactic.Choose", "Mathlib.Tactic.FinCases", "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Push",
)


def checked(args, **kwargs):
    return subprocess.run(args, cwd=LEAN, text=True, encoding="utf-8", check=True, **kwargs)


def environment(obj):
    prefix = Path(checked(["lean", "--print-prefix"], capture_output=True).stdout.strip())
    compiler = str(prefix / "bin" / ("lean.exe" if os.name == "nt" else "lean"))
    version = checked([compiler, "--version"], capture_output=True).stdout.strip()
    if COMMIT not in version or "4.34.0-rc2" not in version:
        raise ValueError(f"Unexpected Lean toolchain: {version}")
    paths = [obj]
    lock = json.loads((LEAN / "lake-manifest.json").read_text())
    for spec in lock["packages"]:
        p = LEAN / lock["packagesDir"] / spec["name"]
        head = checked(["git", "-C", str(p), "rev-parse", "HEAD"], capture_output=True).stdout.strip()
        if head != spec["rev"]:
            raise ValueError(f"Dependency revision differs for {spec['name']}")
        paths.append(p / ".lake/build/lib/lean")
    return compiler, dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths))), version


def axiom_check(output):
    reports = {}
    for name in ENDPOINTS:
        pat = r"'C4W5\." + name + r"' depends on axioms:\s*\[([^\]]*)\]"
        matches = re.findall(pat, output)
        if len(matches) != 1:
            raise ValueError(f"Missing or repeated axiom report for {name}")
        axioms = {s.strip() for s in matches[0].split(",")}
        if axioms != AXIOMS:
            raise ValueError(f"Unexpected axioms for {name}: {axioms}")
        reports[name] = sorted(axioms)
    return reports


def build(args, files):
    graph = manifest("imports.json")
    if {m.replace(".", "/") + ".lean" for m in graph} != files.keys():
        raise ValueError("Source and dependency inventories disagree")
    STATE.mkdir(exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix=args.mode + "-", dir=STATE))
    obj = run / "objects"
    obj.mkdir()
    compiler, env, version = environment(obj)
    print(version, flush=True)
    cached = set()
    if args.mode == "quick":
        if platform.system() != "Linux" or platform.machine() not in ("x86_64", "AMD64"):
            raise SystemExit("The optional quick replay cache requires x86-64 Linux. Use full for other platforms.")
        replay_cache(args.assets, obj)
        cached = {n[:-6].replace("/", ".") for n in manifest("objects.json")}
        if cached - graph.keys() or any(m in cached for m in ("C4W5.Even", "C4W5.FiveColumnsUnified")):
            raise ValueError("Unexpected modules in the replay cache")
    threads = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)
    lean = [compiler, "-j", str(threads), "-R", str(LEAN)]

    def compile_one(m):
        rel = Path(*m.split("."))
        out = (obj / rel).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        log = run / (m + ".log")
        with log.open("w", encoding="utf-8") as stream:
            status = subprocess.run(lean + ["-o", str(out), str((LEAN / rel).with_suffix(".lean"))],
                                    cwd=LEAN, env=env, stdout=stream, stderr=subprocess.STDOUT)
        if status.returncode or not out.is_file():
            raise RuntimeError(f"{m} failed\n" + log.read_text(encoding="utf-8", errors="replace")[-3500:])

    # Importing a saved .olean also loads its transitive dependencies. Some of
    # those (including the rules) are deliberately rebuilt from source.
    project_deps = {m: set(deps).intersection(graph) for m, deps in graph.items()}
    required = {}
    for m in TopologicalSorter(project_deps).static_order():
        prerequisites = set()
        for dep in project_deps[m]:
            prerequisites.update(required[dep] if dep in cached else {dep})
        required[m] = prerequisites
    missing = {m: deps for m, deps in required.items() if m not in cached}
    total = len(missing)
    print(f"{total} modules to compile, {len(cached)} verified cached modules", flush=True)
    done = 0
    pending = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while missing or pending:
            ready = [m for m, deps in missing.items() if not deps][:args.jobs - len(pending)]
            for m in ready:
                pending[pool.submit(compile_one, m)] = m
                del missing[m]
            if not pending:
                raise ValueError("Dependency cycle in the published graph")
            completed, _ = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            for task in completed:
                task.result()
                m = pending.pop(task)
                done += 1
                for deps in missing.values():
                    deps.discard(m)
                if done % 50 == 0 or done == total:
                    print(f"{done}/{total} compiled", flush=True)
    final = checked(lean + [str(LEAN / "CheckEndpoints.lean")], capture_output=True, env=env)
    output = final.stdout + final.stderr
    print(output, end="")
    reports = axiom_check(output)
    result = {"mode": args.mode, "toolchain": version, "compiled": done, "imported_from_cache": len(cached),
              "axioms": reports}
    (run / "acceptance.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Acceptance receipt: {run / 'acceptance.json'}")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("mode", choices=["sources", "deps", "quick", "full"])
    ap.add_argument("--assets", type=Path, help="read all needed archives offline from this directory")
    ap.add_argument("--jobs", type=int, default=2, help="simultaneous Lean processes (default 2)")
    args = ap.parse_args()
    if args.jobs < 1:
        ap.error("--jobs must be positive")
    if args.mode == "deps":
        checked(["lake", "exe", "cache", "get", *MATHLIB], env=dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1"))
        return
    files = sources(args.assets)
    print(f"{len(files)} project source hashes verified", flush=True)
    if args.mode != "sources":
        build(args, files)


if __name__ == "__main__":
    main()
