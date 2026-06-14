import subprocess
import re
import statistics
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
    "PalamedesTest/Examples/Simple/Eq2.lean",
    "PalamedesTest/Examples/Simple/Eq2'.lean",
    "PalamedesTest/Examples/Simple/Eq2Or5.lean",
    "PalamedesTest/Examples/Simple/Eq2Or5'.lean",
    "PalamedesTest/Examples/Simple/ThreePlusOne.lean",
    "PalamedesTest/Examples/Range/Between5And10.lean",
    "PalamedesTest/Examples/Range/BetweenLoAndHi.lean",
    "PalamedesTest/Examples/Range/Gt5.lean",
    "PalamedesTest/Examples/Range/ZeroOrInRange.lean",
    "PalamedesTest/Examples/Arbitrary.lean",
    "PalamedesTest/Examples/List/AllTwos/AllTwos.lean",
    "PalamedesTest/Examples/List/AllEvens/Evens.lean",
    "PalamedesTest/Examples/List/AllTwosEvenLen/AllTwosEvenLen.lean",
    "PalamedesTest/Examples/List/EvenLen/EvenLen.lean",
    "PalamedesTest/Examples/List/IncreasingByOne/IncreasingByOne.lean",
    "PalamedesTest/Examples/List/LengthK/LengthK.lean",
    "PalamedesTest/Examples/List/LengthKAllTwos/LengthKAllTwos.lean",
    "PalamedesTest/Examples/List/SortedBetween/SortedBetween.lean",
    "PalamedesTest/Examples/List/True/True.lean",
    "PalamedesTest/Examples/Tree/AllTwos/AllTwos.lean",
    "PalamedesTest/Examples/Tree/AVL/AVL.lean",
    "PalamedesTest/Examples/Tree/BST/BST.lean",
    "PalamedesTest/Examples/Tree/RBT/RBT.lean",
    "PalamedesTest/Examples/Tree/CompleteTree/CompleteTree.lean",
    "PalamedesTest/Examples/Tree/IncreasingByOne/IncreasingByOne.lean",
    "PalamedesTest/Examples/Tree/Nonempty/Nonempty.lean",
    "PalamedesTest/Examples/Tree/MaxDepth/MaxDepth.lean",
    "PalamedesTest/Examples/Stack/GoodStack.lean",
    "PalamedesTest/Examples/STLC/WellScoped/WellScoped.lean",
    "PalamedesTest/Examples/STLC/WellTyped/WellTyped.lean",
    "PalamedesTest/Examples/Tree/BadRBT/BadRBT.lean",
]

FOLD = [
    "PalamedesTest/Examples/List/AllTwos/Fold.lean",
    "PalamedesTest/Examples/List/AllEvens/Fold.lean",
    "PalamedesTest/Examples/List/AllTwosEvenLen/Fold.lean",
    "PalamedesTest/Examples/List/EvenLen/Fold.lean",
    "PalamedesTest/Examples/List/IncreasingByOne/Fold.lean",
    "PalamedesTest/Examples/List/LengthK/Fold.lean",
    "PalamedesTest/Examples/List/LengthKAllTwos/Fold.lean",
    "PalamedesTest/Examples/List/SortedBetween/Fold.lean",
    "PalamedesTest/Examples/List/True/Fold.lean",
    "PalamedesTest/Examples/Tree/AllTwos/Fold.lean",
    "PalamedesTest/Examples/Tree/AVL/Fold.lean",
    "PalamedesTest/Examples/Tree/BST/Fold.lean",
    "PalamedesTest/Examples/Tree/RBT/Fold.lean",
    "PalamedesTest/Examples/Tree/CompleteTree/Fold.lean",
    "PalamedesTest/Examples/Tree/IncreasingByOne/Fold.lean",
    "PalamedesTest/Examples/Tree/Nonempty/Fold.lean",
    "PalamedesTest/Examples/Tree/MaxDepth/Fold.lean",
    "PalamedesTest/Examples/Tree/BadRBT/Fold.lean",
    "PalamedesTest/Examples/Stack/Fold.lean",
    "PalamedesTest/Examples/STLC/WellScoped/Fold.lean",
    "PalamedesTest/Examples/STLC/WellTyped/Fold.lean",
]

FILES = STANDARD

# Fail loudly if a path has rotted (e.g. the corpus was moved) rather than silently profiling
# nothing. InProgress/ files are exempt — they are expected to error, not vanish.
import os
missing = [f for f in FILES if not os.path.exists(f)]
if missing:
    raise SystemExit("ERROR: these benchmark files do not exist (was the corpus moved?):\n  "
                     + "\n  ".join(missing))

# Regular expression to match the desired output
pattern = re.compile(r'\[palamedes\.trace\] \[(\d+(?:\.\d+)?)\].*?⟪(.+)⟫⟪(.+)⟫')

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
            raise SystemExit(f"\nERROR: no palamedes.trace nodes matched for {file} (trace format changed?)")
        for (numRepr, typ, pred) in matches:
            label = (typ, pred)
            if label in data:
                data[label]["times"].append(float(numRepr))
            else:
                total = True
                with open(file, "r") as f:
                    if any(
                            map(lambda line: line.find("allow_partial") != -1,
                                f.readlines())):
                        total = False
                data[label] = {"times": [float(numRepr)], "total": total}
    except subprocess.CalledProcessError as e:
        print(f"\nError running script: {e} \n")

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
