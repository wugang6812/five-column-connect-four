# Five-Column Connect Four Is a Draw at Every Finite Height

On an empty board with **five columns and any finite number of rows**, both players can prevent a loss. This includes height zero. Gravity makes every move fall to the lowest free cell in its column. Four consecutive stones of one colour win horizontally, vertically or diagonally.

[English paper (PDF)](paper/en/five_columns_draw_en.pdf) · [中文论文 (PDF)](paper/zh/five_columns_draw_zh.pdf) · [中文说明](README.zh-CN.md) · [Version 1.0.0 and certificates](https://github.com/wugang6812/five-column-connect-four/releases/tag/v1.0.0)

## The theorem

```lean
theorem five_columns_draw (h : Nat) : IsDraw h (emptyBoard 5)
```

For positive even heights the proof combines a defensive pairing strategy with a checked first-player strategy. For odd heights the proof uses a separate pair of strategies. The final module combines both results and handles the empty, zero-height board. It also proves that neither player has a forced win. [Unified theorem](lean/C4W5/FiveColumnsUnified.lean) · [Game rules and meaning of a draw](lean/experiments/NarrowBoards.lean)

A board with a floor and no ceiling is a different game. A separate, certificate-free module proves the five-column case of the known infinite-height strip result of Yamaguchi, Tanaka and Yamaguchi. [Lean proof](lean/FiveColumnsInfinite_PureCore.lean) · [2014 paper](https://doi.org/10.1007/978-3-319-09165-5_14)

## Replay in Lean

On x86-64 Linux with Python 3.11+, Git, and Lean/Lake on your path, run these commands from the repository root. An elan installation will select the project's pinned toolchain.

```sh
python3 scripts/verify.py deps
python3 scripts/verify.py quick
```

The quick replay verifies source and object hashes, compiles 21 modules from source including all four table entry points, and checks the exact types and axiom dependencies of the three final finite-height declarations. The full replay compiles all 3,204 project modules from source. It can take many hours. [Full and offline instructions](docs/reproduction.md) · [Endpoint type checks](lean/CheckEndpoints.lean)

## Strategy certificates

| Table | What it proves | Strategy rows | Terminal witnesses | Shards |
| --- | --- | ---: | ---: | ---: |
| SG5 | `g5_tight`, `g5_mid` | 802,510 | 220,630 | 697 |
| SGZ5R | `g5_wide` | 905,511 | 272,542 | 787 |
| STop | `top_all` | 197,869 | 37,785 | 172 |

The even-height strategy also uses SG3, which has its own certificate. The table above counts only the three optimized families. The 1,014 modules in the original unified build receipt describe its final assembly stage. The public inventory counts the complete project import closure for the finite theorem, the no-ceiling theorem, and the companion opening and rules checks. [Acceptance records](receipts/) · [Certificate inventory](certificates/sources.json)

## Citation and related work

The English and Chinese manuscripts carry the byline **GPT, Claude and Gemini**. Cite the tagged version used in your work. Original project code and proof sources use the MIT license. Both manuscripts use CC BY 4.0. [Citation](CITATION.cff) · [Code license](LICENSE) · [Manuscript license](paper/LICENSE.txt)

The proofs for one to four columns are maintained in their own repository. [Narrow Connect Four](https://github.com/wugang6812/narrow-connect-four)
