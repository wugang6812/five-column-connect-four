"""Build the two standalone manuscripts into the specified output directory."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    for language, engine in (("en", "pdflatex"), ("zh", "xelatex")):
        stem = "five_columns_draw_" + language
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            shutil.copyfile(ROOT / "paper" / language / (stem + ".tex"), work / (stem + ".tex"))
            for _ in range(3):
                run = subprocess.run([engine, "-interaction=nonstopmode", "-halt-on-error", stem + ".tex"],
                                     cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                if run.returncode:
                    raise RuntimeError(run.stdout.decode(errors="replace")[-3500:])
            log = (work / (stem + ".log")).read_text(encoding="utf-8", errors="replace")
            if re.search(r"undefined references|Citation .* undefined|Reference .* undefined|Missing character:", log):
                raise RuntimeError("Check bibliography, cross-references or fonts for " + language)
            shutil.copyfile(work / (stem + ".pdf"), args.out / (stem + ".pdf"))
            print(args.out / (stem + ".pdf"), flush=True)


if __name__ == "__main__":
    main()
