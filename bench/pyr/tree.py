"""Rebuild a certificate's bisection tree (leaves, boxes at scale 2^15) from data_<NAME>.lean + <NAME>_params.txt
(same parsing as reemit_force.py)."""
import re, itertools, os, sys
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
ROOT = os.path.expanduser("~/work/riemann-submission")
def load(NAME):
    params = open(os.path.join(ROOT, f"{NAME}_params.txt")).read().split()
    Q, SA = int(params[0]), int(params[1]); aN = [int(x) for x in params[2].split(",")]; bN = [int(x) for x in params[3].split(",")]; cN = int(params[4])
    SCE = int(params[6]) if len(params) > 6 else 96
    s = open(os.path.join(ROOT, f"data_{NAME}.lean"), encoding="utf-8").read()
    bits = int(re.search(r"def bits : ℕ := (\d+)", s).group(1))
    covers = []
    for r in range(Q):
        body = re.search(rf"def cover{r} : List \(ℕ × ℕ × Bool\) := \[(.*?)\]", s, re.S).group(1)
        covers.append([(int(a), int(b), c == "true") for a, b, c in re.findall(r"\((\d+), (\d+), (true|false)\)", body)])
    bads = [[(a, b) for a, b, cl in cv if not cl] for cv in covers]
    leaves = []
    def build(pos, box):
        if (bits >> pos) & 1:
            k = (bits >> (pos + 1)) & 7; mid = (box[k][0] + box[k][1]) // 2
            a = list(box); a[k] = (box[k][0], mid); b2 = list(box); b2[k] = (mid, box[k][1])
            pos = build(pos + 4, tuple(a)); return build(pos, tuple(b2))
        leaves.append(box); return pos + 1
    pos = 0
    for tup in itertools.product(*[range(len(bd)) for bd in bads]):
        box = tuple(bads[r][tup[r]] for r in range(Q))
        pos = build(pos, box)
    return dict(Q=Q, SA=SA, aN=aN, bN=bN, cN=cN, SCE=SCE, covers=covers, bads=bads, leaves=leaves)
PAIRS5 = [(i, j) for i in range(6) for j in range(i + 1, 6)]
def terms(box, Q=5):
    """the term intervals of a leaf, in the order of the pairs (i<j): gaps i..j-1"""
    out = []
    for (i, j) in [(i, j) for i in range(Q + 1) for j in range(i + 1, Q + 1)]:
        out.append((sum(box[r][0] for r in range(i, j)), sum(box[r][1] for r in range(i, j))))
    return out
if __name__ == "__main__":
    d = load(sys.argv[1] if len(sys.argv) > 1 else "SixW35RKF")
    print(len(d["leaves"]), "leaves; scale 2^", d["SCE"], "; bad sizes", [len(b) for b in d["bads"]])
