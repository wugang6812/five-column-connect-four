# 五列四子棋在任意有限高度上都是和棋

从五列空盘开始，无论有多少行，双方都有不败策略。高度可以是零。每一步在一列落子，棋子落到该列最低的空格。横、竖或斜向先连成四子的一方获胜。

[中文论文](paper/zh/five_columns_draw_zh.pdf) · [英文论文](paper/en/five_columns_draw_en.pdf) · [正式版本与证书下载](https://github.com/wugang6812/five-column-connect-four/releases/tag/v1.0.0)

**读证明。** 论文先讲双方怎样防守，再说明哪些局面可以归约到有限张策略表。正偶数高度和奇数高度各自有证明。统一定理接上两支并处理零高度，同时得到双方都无法强制获胜。另有一份独立证明处理有底无顶的五列条带。无顶条带的和棋结论已有文献，论文给出五列情形的显式策略和 Lean 验证。[有限高度定理](lean/C4W5/FiveColumnsUnified.lean) · [无顶证明](lean/FiveColumnsInfinite_PureCore.lean) · [已有研究](https://doi.org/10.1007/978-3-319-09165-5_14)

**自己验证。** 在 x86-64 Linux 上安装 Git、Python 3.11 或以上及 elan，从仓库根目录运行以下两行。第一行准备锁定版本的数学库。第二行会下载带校验值的证书，在本机重新编译四个表入口、最终定理等 21 个模块，并核对最终三个声明的类型和公理。

```sh
python3 scripts/verify.py deps
python3 scripts/verify.py quick
```

需要从源码独立计算全部项目证明时，把第二行的 `quick` 换成 `full`。两条路径的输入、耗时区别和离线用法见[复现说明](docs/reproduction.md)。

**核对数字。** SG5、SGZ5R、STop 三张优化表共有 1,905,890 行策略、530,957 个终止见证，分为 1,656 片。SG3 单独列账。历史回执中的 1,014 个模块只统计最终合并阶段。本仓库的 3,204 个项目模块还包括上游依赖、无顶条带和独立规则接口。[三表回执](receipts/THREE_TABLES_ACCEPTANCE.json) · [最终合并回执](receipts/COMPACT_UNIFIED_BUILD.json) · [GitHub 公开机器的 v1.0.0 复验](https://github.com/wugang6812/five-column-connect-four/actions/runs/45598556691)

双语论文沿用稿件署名 GPT、Claude、Gemini，采用 CC BY 4.0。项目原创程序与 Lean 源码采用 MIT 许可。[引用信息](CITATION.cff) · [独立维护的一至四列项目](https://github.com/wugang6812/narrow-connect-four)
