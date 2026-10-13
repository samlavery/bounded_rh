import sys
src = open(sys.argv[1], encoding="utf-8").read().split("\n"); out = []
for l in src:
    if l.startswith(("theorem ", "def ", "noncomputable def ")):
        if out and out[-1].rstrip().endswith(" in"):
            prev = out.pop(); out.append("#eval IO.monoMsNow"); out.append(prev)
        else: out.append("#eval IO.monoMsNow")
    if l.startswith("end Zeta23Ext"): out.append("#eval IO.monoMsNow")
    out.append(l)
open(sys.argv[2], "w", encoding="utf-8").write("\n".join(out))
print("stamps:", sum(1 for l in out if l == "#eval IO.monoMsNow"))
