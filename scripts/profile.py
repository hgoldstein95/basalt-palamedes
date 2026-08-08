import glob
import os
import re
import statistics
import subprocess
from tqdm import tqdm

NUM_RUNS = 2

BASE_CMD = [
    "lake",
    "env",
    "lean",
    "-Dtrace.profiler=true",
    "-Dweak.palamedes.trace=true",
]

STANDARD = [
    "PalamedesTest/Corpus/Simple/Eq2.lean",
    "PalamedesTest/Corpus/Simple/Eq2'.lean",
    "PalamedesTest/Corpus/Simple/Eq2Or5.lean",
    "PalamedesTest/Corpus/Simple/Eq2Or5'.lean",
    "PalamedesTest/Corpus/Simple/ThreePlusOne.lean",
    "PalamedesTest/Corpus/Range/Between5And10.lean",
    "PalamedesTest/Corpus/Range/BetweenLoAndHi.lean",
    "PalamedesTest/Corpus/Range/Gt5.lean",
    "PalamedesTest/Corpus/Range/ZeroOrInRange.lean",
    "PalamedesTest/Corpus/Arbitrary.lean",
    "PalamedesTest/Corpus/List/AllTwos/AllTwos.lean",
    "PalamedesTest/Corpus/List/AllEvens/AllEvens.lean",
    "PalamedesTest/Corpus/List/AllTwosEvenLen/AllTwosEvenLen.lean",
    "PalamedesTest/Corpus/List/EvenLen/EvenLen.lean",
    "PalamedesTest/Corpus/List/IncreasingByOne/IncreasingByOne.lean",
    "PalamedesTest/Corpus/List/LengthK/LengthK.lean",
    "PalamedesTest/Corpus/List/LengthKAllTwos/LengthKAllTwos.lean",
    "PalamedesTest/Corpus/List/SortedBetween/SortedBetween.lean",
    "PalamedesTest/Corpus/List/True/True.lean",
    "PalamedesTest/Corpus/Tree/AllTwos/AllTwos.lean",
    "PalamedesTest/Corpus/Tree/AVL/AVL.lean",
    "PalamedesTest/Corpus/Tree/BST/BST.lean",
    "PalamedesTest/Corpus/Tree/RBT/RBT.lean",
    "PalamedesTest/Corpus/Tree/CompleteTree/CompleteTree.lean",
    "PalamedesTest/Corpus/Tree/IncreasingByOne/IncreasingByOne.lean",
    "PalamedesTest/Corpus/Tree/Nonempty/Nonempty.lean",
    "PalamedesTest/Corpus/Tree/MaxDepth/MaxDepth.lean",
    "PalamedesTest/Corpus/Stack/GoodStack.lean",
    "PalamedesTest/Corpus/STLC/WellScoped/WellScoped.lean",
    "PalamedesTest/Corpus/STLC/WellTyped/WellTyped.lean",
    "PalamedesTest/Corpus/Tree/BadRBT/BadRBT.lean",
    "PalamedesTest/Corpus/Simple/OneOfFour.lean",
    "PalamedesTest/Corpus/Tuple/Pairs.lean",
    "PalamedesTest/Corpus/LeafTree/LeafTree.lean",
]

FOLD = [
    "PalamedesTest/Corpus/List/AllTwos/Fold.lean",
    "PalamedesTest/Corpus/List/AllEvens/Fold.lean",
    "PalamedesTest/Corpus/List/AllTwosEvenLen/Fold.lean",
    "PalamedesTest/Corpus/List/EvenLen/Fold.lean",
    "PalamedesTest/Corpus/List/IncreasingByOne/Fold.lean",
    "PalamedesTest/Corpus/List/LengthK/Fold.lean",
    "PalamedesTest/Corpus/List/LengthKAllTwos/Fold.lean",
    "PalamedesTest/Corpus/List/SortedBetween/Fold.lean",
    "PalamedesTest/Corpus/List/True/Fold.lean",
    "PalamedesTest/Corpus/Tree/AllTwos/Fold.lean",
    "PalamedesTest/Corpus/Tree/AVL/Fold.lean",
    "PalamedesTest/Corpus/Tree/BST/Fold.lean",
    "PalamedesTest/Corpus/Tree/RBT/Fold.lean",
    "PalamedesTest/Corpus/Tree/CompleteTree/Fold.lean",
    "PalamedesTest/Corpus/Tree/IncreasingByOne/Fold.lean",
    "PalamedesTest/Corpus/Tree/Nonempty/Fold.lean",
    "PalamedesTest/Corpus/Tree/MaxDepth/Fold.lean",
    "PalamedesTest/Corpus/Tree/BadRBT/Fold.lean",
    "PalamedesTest/Corpus/Stack/Fold.lean",
    "PalamedesTest/Corpus/STLC/WellScoped/Fold.lean",
    "PalamedesTest/Corpus/STLC/WellTyped/Fold.lean",
]

# Corpus files that are deliberately not benchmarked: the `AccuOpt` spelling is a third phrasing of
# a predicate `STANDARD` and `FOLD` already cover, and `IdxOf` exists to re-elaborate its own pinned
# term rather than to time a search.
EXCLUDED = [
    "PalamedesTest/Corpus/List/EvenLen/AccuOpt.lean",
    "PalamedesTest/Corpus/List/IdxOf/IdxOf.lean",
    "PalamedesTest/Corpus/List/LengthK/AccuOpt.lean",
    "PalamedesTest/Corpus/List/True/AccuOpt.lean",
]

# Which set to profile. `STANDARD` is the structurally-recursive spelling of each predicate;
# `FOLD` is the catamorphism spelling of the same properties, which exercises a different path
# through the search. Swap this line to profile the other set.
FILES = STANDARD

# The lists above are checked against the corpus in both directions, since either drift is silent:
# a rotted path profiles nothing, and a corpus file nobody listed is a benchmark quietly missing
# from the paper's table.
missing = [f for f in STANDARD + FOLD + EXCLUDED if not os.path.exists(f)]
if missing:
    raise SystemExit(
        "ERROR: these benchmark files do not exist (was the corpus moved?):\n  "
        + "\n  ".join(missing))

unlisted = sorted(
    set(glob.glob("PalamedesTest/Corpus/**/*.lean", recursive=True)) -
    set(STANDARD) - set(FOLD) - set(EXCLUDED))
if unlisted:
    raise SystemExit(
        "ERROR: these corpus files are in neither STANDARD, FOLD nor EXCLUDED:\n  "
        + "\n  ".join(unlisted))

# A declaration, from its `def` through the `:=` that starts its body. Classification reads these
# rather than the whole file so that a predicate or a docstring mentioning `Option` does not confuse
# the totality check.
DECLARATION = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*def\b.*?:=",
                         re.MULTILINE | re.DOTALL)

# `: G (Option α)` or `: Palamedes.Gen (Option α)` in a declaration's return type.
PARTIAL_RETURN_TYPE = re.compile(
    r":\s*(?:_root_\.)?(?:Palamedes\.)?(?:G|Gen)\s*\(\s*Option\b")


def is_total(path):
    """Does this benchmark's generator filter?

    Partiality is a fact about the *declared return type*: a generator that can reject a draw must
    be declared at `G (Option α)`. (This used to be detected by grepping for an `allow_partial`
    flag, which was removed when the declared type took over that job — leaving every benchmark
    classified `total` and the partial table silently empty.)
    """
    with open(path, "r") as f:
        decls = DECLARATION.findall(f.read())
    return not any(PARTIAL_RETURN_TYPE.search(d) for d in decls)


# Regular expression to match the desired output
pattern = re.compile(
    r'\[palamedes\.trace\] \[(\d+(?:\.\d+)?)\].*?⟪(.+)⟫⟪(.+)⟫')

# Dictionary to store extracted numbers by string
data = dict()

# Run the external script multiple times
iter = tqdm(FILES * NUM_RUNS, dynamic_ncols=True)
for file in iter:
    iter.set_description(file)
    try:
        result = subprocess.run(BASE_CMD + [file],
                                capture_output=True,
                                text=True,
                                check=True)
        output = result.stdout
        matches = pattern.findall(output)
        if not matches:
            raise SystemExit(
                f"\nERROR: no palamedes.trace nodes matched for {file} (trace format changed?)"
            )
        for (numRepr, typ, pred) in matches:
            label = (typ, pred)
            if label in data:
                data[label]["times"].append(float(numRepr))
            else:
                data[label] = {
                    "times": [float(numRepr)],
                    "total": is_total(file),
                }
    except subprocess.CalledProcessError as e:
        raise SystemExit(f"\nERROR: elaborating {file} failed:\n{e.stderr}")

label_pattern = re.compile(r"fun (.+) => (.+)")

total_lines = []
partial_lines = []

# Compute and print mean and standard deviation
for label, numbers in [item for item in data.items()]:
    mean = statistics.mean(numbers["times"])
    stdev = statistics.stdev(numbers["times"])
    total = numbers["total"]

    (typ, pred) = label

    pred = pred.replace("∃", "`$\\exists$`")
    pred = pred.replace("∨", "`$\\lor$`")
    pred = pred.replace("∧", "`$\\land$`")
    pred = pred.replace("Γ", "`$\\Gamma$`")
    pred = pred.replace("τ", "`$\\tau$`")
    pred = pred.replace("≤", "<=")

    typ = typ.replace("ℕ", "Nat")

    pred = pred.replace("TARGET", "`\\textbf{v}`")

    line = ("\\mintinline[mathescape=true,escapeinside=``]{text}|" + pred +
            "| & \\mintinline[mathescape=true,escapeinside=``]{text}|" + typ +
            "| & " + f"${mean:.2f}$ & (${stdev:.2f}$) \\\\")

    if total:
        total_lines.append(line)
    else:
        partial_lines.append(line)

with open("final-data.txt", "w") as f:
    for line in total_lines:
        f.write(line + "\n")
    f.write("\\hline\n")
    for line in partial_lines:
        f.write(line + "\n")
