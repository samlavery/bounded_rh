import sys
sys.path.insert(0, ".")
from gen_checker_mvt import checker
from size_m import AN, BN, SA
NAME = sys.argv[1] if len(sys.argv) > 1 else "MvtT"
cN = round(358287 * (1 - 0.01))
ORDER = [5, 12, 9, 0, 4, 14, 3, 7, 2, 8, 11, 1, 10, 13, 6]
txt = "import MvtCore\n\nset_option maxRecDepth 100000\n" + checker(NAME, SA, AN, BN, cN, ORDER) + "\n" + open("cover_text.lean").read() + f"end Zeta23Ext.Bridge.ThreePoint.{NAME}\n\nend\n"
open(f"{NAME}.lean", "w").write(txt)
print(len(txt))
