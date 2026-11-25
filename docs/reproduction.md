# Reproducing version 1.0.0

Use Git, Python 3.11 or later, and the Lean toolchain selected by `lean/lean-toolchain`. The released toolchain is Lean 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`. Mathlib is pinned at `cecebc3014fd27da46b2899d7639ea643a444a51`. Run the following commands from the clone's root.

```sh
git clone --branch v1.0.0 https://github.com/wugang6812/five-column-connect-four.git
cd five-column-connect-four
python3 scripts/verify.py deps
python3 scripts/verify.py quick --jobs 2
```

### What each replay establishes

| Command | Work done on your machine |
| --- | --- |
| `sources` | Download six source archives. Verify all 3,204 Lean files against the per-module SHA-256 inventory. Requires only Python. |
| `quick` | On x86-64 Linux, also verify and import 3,183 pinned Lean objects. Build the other 21 modules from the released sources. These include the game rules, the four table entry points, the compact even-height proof, the odd-height assembly, the no-ceiling proof, the independent opening checks, and the unified theorem. |
| `full` | Compile all 3,204 project modules in a fresh object directory from the verified sources. The external Lean distribution and locked Mathlib dependencies are shared with the quick replay. No project object is imported from the release cache. |

Both Lean modes end by starting another Lean process on `CheckEndpoints.lean`. It type-checks the exact mathematical statements and reports the transitive axiom dependencies of `five_columns_even_draw`, `five_columns_draw`, and `five_columns_neither_player_wins`. The checker requires each axiom set to equal `propext`, `Classical.choice`, and `Quot.sound`. Source and binary hashes establish byte identity. The Lean runs establish the corresponding proof claims.

For a cold project build use `python3 scripts/verify.py full --jobs 2`. Full replay includes heavy kernel reductions and may take many hours. `--jobs` limits concurrent Lean processes. Each process can use the logical cores visible to it. Lower the process count to 1 if memory is tight. Each run writes its own build directory, logs, and a machine-readable `acceptance.json` under `.replay/`. That directory can be removed after saving any receipts you want to keep.

### Offline verification

Prepare the pinned Lean toolchain and Mathlib packages once with `deps`. Download the six `c4w5-*-source.zip` files from the tagged Release. For quick replay also download `c4w5-linux-x86_64-replay-cache.zip`. Place the files in one directory and run:

```sh
python3 scripts/verify.py sources --assets /path/to/files
python3 scripts/verify.py quick --assets /path/to/files
# Or compile every project module using only the six source archives.
python3 scripts/verify.py full --assets /path/to/files
```

The download step verifies the archive before extraction, then verifies each Lean file. Generated modules are installed at their real import paths beneath `lean/`. A locally edited file causes an error. Use a fresh clone for replay while developing modifications in another checkout.

### Original archives and receipts

The Release also contains the three original `SOURCE_ONLY` ZIPs with the exact archive hashes in the upstream three-table acceptance receipt. They preserve the original table-level input layouts, renderers and manifests. The six smaller-purpose source archives used by the commands above present a single coherent import tree: SG3, SG5, SGZ5R, STop, odd certificates, and finite-height certificates. They include the five accepted shard splits. The three SG5 splits are K599, K612 and K613. The two SGZ5R splits are K0000 and K0626.

For an independent numerical readback, run `python3 scripts/check_tables.py`. For offline use, supply the three original SOURCE_ONLY ZIPs and `c4w5-stop-readback-inputs.zip` with `--assets /path/to/files`. The check decodes the policy and terminal-witness records for all three families. The SG3 upstream archive is also available separately. To recreate the six public Lean source archives after materializing them, run `python3 scripts/pack_sources.py --out _build/source-archives`.

The historical build reused 120 checked modules and built 894 during *final assembly*. The three optimized tables and SG3 had already been checked. In the historical JSON, the four Main hashes are hashes of compiled objects. The two fields for the unified entry and the even entry are source hashes. Private Drive file IDs were removed from the public copy of the three-table JSON. The original archive names, hashes, counts and axiom results are retained. [Source inventory](../certificates/modules.json) · [Historical receipts](../receipts/) · [Tagged assets](https://github.com/wugang6812/five-column-connect-four/releases/tag/v1.0.0)

### Solver and generator tools

`tools/certgen.cpp` searches a real board at a specified height and outputs a strategy-closed table. For example, run the following on Linux to obtain the table after Black's centre opening on the five-column, two-row board.

```sh
g++ -std=c++17 -O2 tools/certgen.cpp -o /tmp/c4w5-certgen
/tmp/c4w5-certgen 2 3 > /tmp/c4w5-h2.txt
```

The accompanying C++ tools cover the abstract zone and stretch searches and reply checks. The versioned tables are inputs to Lean, so replay does not depend on the solver selecting the same witness on a second search. Use the three original archives to inspect their family-specific generation and checking scripts.

### Papers and subsequent releases

The two LaTeX sources are standalone. For Ubuntu, install `texlive-latex-extra`, `texlive-xetex`, `texlive-lang-chinese`, `texlive-fonts-recommended`, `fonts-noto-cjk` and `fonts-linuxlibertine`. Run `python3 scripts/build_paper.py --out _build/paper`. This makes three passes per language and checks for unresolved references and missing characters. PDF bytes can differ between TeX installations.

For a new proof release, regenerate the source and dependency inventories, archive hashes and cache bindings for the new tag. Replay the corresponding mathematical statements, publish the matching assets under the tag, and preserve the preceding release for citation. The hosted workflow checks the proof and both manuscripts on pushes, pull requests and published releases. A DOI can be added to the citation metadata after archival deposit.
