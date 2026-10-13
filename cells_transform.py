"""Rewrite the generated cell lemmas: every `nlinarith` becomes `linarith only [...]` with the
explicit product fact it needs (interval multiplication = McCormick products), and every other
`linarith` is restricted to the two or four hypotheses it actually uses.  Statements unchanged."""
import re, os
from fractions import Fraction as Fr

RAT = r"\((-?\d+)(?:/(\d+))?:ℝ\)"
def rat(m): return Fr(int(m[0]), int(m[1]) if m[1] else 1)
def R(q): return f"({q.numerator}:ℝ)" if q.denominator == 1 else f"({q.numerator}/{q.denominator}:ℝ)"

SHIFTS = [""]          # SHIFTS[0] = Lean text of the shift lemmas, filled as cells are transformed
_shift_table = {}      # (hcx statement, hsx statement) -> lemma name

def shift_helpers(block):
    """Replace the two 4-line `hcx`/`hsx` shift proofs by references to one shared lemma per
    (anchor, side); the lemma states exactly the template's two equations."""
    m = re.search(r"  have hcx : (Real\.cos \(Real\.pi\*x\) = [^\n]*) := by\n((?:    [^\n]*\n){3})"
                  r"  have hsx : (Real\.sin \(Real\.pi\*x\) = [^\n]*) := by\n((?:    [^\n]*\n){3})", block)
    if not m: return block
    key = (m.group(1), m.group(3))
    if key not in _shift_table:
        name = f"shift_{len(_shift_table)}"
        _shift_table[key] = name
        def bullet(proof):
            ls = [l.strip() for l in proof.rstrip("\n").split("\n")]
            return "  · " + ls[0] + "\n" + "\n".join("    " + l for l in ls[1:]) + "\n"
        SHIFTS[0] += (f"\ntheorem {name} (x : ℝ) : {m.group(1)} ∧ {m.group(3)} := by\n"
                      f"  refine ⟨?_, ?_⟩\n" + bullet(m.group(2)) + bullet(m.group(4)))
    name = _shift_table[key]
    return block[:m.start()] + f"  have hcx := ({name} x).1\n  have hsx := ({name} x).2\n" + block[m.end():]

def transform_cell(block):
    """block: text of one `theorem wc_N ... := by ... linarith` (full-template cells only)."""
    m = re.search(r"theorem (wc_\d+) \(x : ℝ\) \(h₁ : " + RAT + r" ≤ x\) \(h₂ : x ≤ " + RAT + r"\)", block)
    if not m: return block
    L, U = rat(m.groups()[1:3]), rat(m.groups()[3:5])
    m2 = re.search(r"have ht1 : " + RAT + r" ≤ Real\.pi \* (\((?:x - " + RAT + r"|" + RAT + r" - x)\)) := by nlinarith", block)
    if not m2: return block
    RR = m2.group(3)
    ma = re.search(r"\(x - " + RAT + r"\)", RR)
    if ma:
        A = rat(ma.groups()); rlo, rhi = L - A, U - A
    else:
        mb = re.search(RAT + r" - x\)", RR); A = rat(mb.groups()); rlo, rhi = A - U, A - L
    assert rlo >= 0, (m.group(1), rlo)
    s = block
    def sub1(pat, rep):
        nonlocal s
        s2, n = re.subn(pat, rep, s, count=1)
        assert n == 1, (m.group(1), pat)
        s = s2
    RRe = re.escape(RR)
    sub1(r"(have ht1 : " + RAT + r" ≤ Real\.pi \* " + RRe + r" := by) nlinarith",
         r"\1 exact mul_ge_of pi_lo (show " + R(rlo) + r" ≤ " + RR + r" by linarith only [h₁, h₂]) (by norm_num) (by norm_num) (by norm_num)")
    sub1(r"(have ht2 : Real\.pi \* " + RRe + r" ≤ " + RAT + r" := by) nlinarith",
         r"\1 exact mul_le_of pi_hi (show " + RR + r" ≤ " + R(rhi) + r" by linarith only [h₁, h₂]) Real.pi_pos.le (by linarith only [h₁, h₂]) (by norm_num)")
    # Taylor steps: inner linarith uses h, h2; the side goals use ht1 / ht2
    sub1(r"have h := cos_lower \(by linarith\) ht2 \(by norm_num\)", r"have h := cos_lower (by linarith only [ht1]) ht2 (by norm_num)")
    sub1(r"have h := cos_upper \(by norm_num\) ht1 \(by linarith\)", r"have h := cos_upper (by norm_num) ht1 (by linarith only [ht2])")
    sub1(r"have h := sin_lower \(by norm_num\) ht1 \(by linarith\)", r"have h := sin_lower (by norm_num) ht1 (by linarith only [ht2])")
    sub1(r"have h := sin_upper \(by linarith\) ht2 \(by norm_num\)", r"have h := sin_upper (by linarith only [ht1]) ht2 (by norm_num)")
    s = re.sub(r"(taylor(?:Cos|Sin) [^\n]*norm_num\n)    linarith\n", r"\1    linarith only [h, h2]\n", s)
    # the shift identities may swap cos and sin (half-integer anchors): pick the matching Taylor pair
    fc = re.search(r"have hcx : Real\.cos \(Real\.pi\*x\) = \([-0-9]+:ℝ\) \* Real\.(cos|sin) ", s).group(1)
    fs = re.search(r"have hsx : Real\.sin \(Real\.pi\*x\) = \([-0-9]+:ℝ\) \* Real\.(cos|sin) ", s).group(1)
    pc = "[hc1, hc2]" if fc == "cos" else "[hs1, hs2]"
    ps = "[hs1, hs2]" if fs == "sin" else "[hc1, hc2]"
    sub1(r"(have hcxl : [^\n]* := by rw \[hcx\];) linarith", r"\1 linarith only " + pc)
    sub1(r"(have hcxu : [^\n]* := by rw \[hcx\];) linarith", r"\1 linarith only " + pc)
    sub1(r"(have hsxl : [^\n]* := by rw \[hsx\];) linarith", r"\1 linarith only " + ps)
    sub1(r"(have hsxu : [^\n]* := by rw \[hsx\];) linarith", r"\1 linarith only " + ps)
    sub1(r"(have hb1 : " + RAT + r" ≤ Real\.pi\*x := by) nlinarith",
         r"\1 exact mul_ge_of pi_lo h₁ (by norm_num) (by norm_num) (by norm_num)")
    sub1(r"(have hb2 : Real\.pi\*x ≤ " + RAT + r" := by) nlinarith",
         r"\1 exact mul_le_of pi_hi h₂ Real.pi_pos.le (by linarith only [h₁]) (by norm_num)")
    sub1(r"(have hp1 : " + RAT + r" ≤ 2\*gam\*\(Real\.pi\*x\) := by) nlinarith \[hg\.1, hg\.2\]",
         r"\1 linarith only [mul_le_mul hg.1 hb1 (by norm_num) (by linarith only [hg.1])]")
    sub1(r"(have hp2 : 2\*gam\*\(Real\.pi\*x\) ≤ " + RAT + r" := by) nlinarith \[hg\.1, hg\.2\]",
         r"\1 linarith only [mul_le_mul hg.2 hb2 (by linarith only [hb1]) (by norm_num)]")
    MC = ("linarith only [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxl), "
          "mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxu), mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hsxu), "
          "mul_nonneg (sub_nonneg.2 hp2) (sub_nonneg.2 hsxl), hp1, hp2, hsxl, hsxu]")
    sub1(r"(have hT1 : " + RAT + r" ≤ 2\*gam\*\(Real\.pi\*x\)\*Real\.sin \(Real\.pi\*x\) := by) nlinarith",
         r"\1 exact prod_lo (by norm_num) hp1 hp2 hsxl (by norm_num) (by norm_num)")
    sub1(r"(have hT2 : 2\*gam\*\(Real\.pi\*x\)\*Real\.sin \(Real\.pi\*x\) ≤ " + RAT + r" := by) nlinarith",
         r"\1 exact prod_hi (by norm_num) hp1 hp2 hsxu (by norm_num) (by norm_num)")
    sub1(r"(abs_ge_of_(?:le|ge)) \(by linarith\)", r"\1 (by linarith only [hcxl, hcxu, hT1, hT2])")
    sub1(r"(have hD0 : \(1:ℝ\) < 2\*\(Real\.pi\*x\)\^2 := by) nlinarith",
         r"\1 linarith only [mul_le_mul hb1 hb1 (by norm_num) (by linarith only [hb1])]")
    sub1(r"(have hD : 2\*\(Real\.pi\*x\)\^2 - 1 ≤ " + RAT + r" := by) nlinarith",
         r"\1 linarith only [mul_le_mul hb2 hb2 (by linarith only [hb1]) (by norm_num)]")
    sub1(r"(have hsq : [^\n]*:= by norm_num\n)  linarith\n", r"\1  linarith only [hfin, hsq]\n")
    assert "nlinarith" not in s, m.group(1)
    if os.environ.get("NORMNUM1"):
        s = s.replace("unfold taylorCos taylorErr; norm_num\n", "unfold taylorCos taylorErr; norm_num1\n")
        s = s.replace("unfold taylorSin taylorErr; norm_num\n", "unfold taylorSin taylorErr; norm_num1\n")
        s = re.sub(r"(have hsq : [^\n]*:= by) norm_num\n", r"\1 norm_num1\n", s)
        s = re.sub(r"(have hfin := wfun_ge x " + RAT + " " + RAT + r") \(by norm_num\) \(by norm_num\)", r"\1 (by norm_num1) (by norm_num1)", s)
    s = shift_helpers(s)
    s = s.replace("  have hpl := pi_lo\n  have hph := pi_hi\n", "")
    assert "hpl" not in s and "hph" not in s, m.group(1)
    return s

def transform_cells(text):
    parts = re.split(r"(?=\ntheorem wc_)", text)
    out = [parts[0]] + [transform_cell(p) for p in parts[1:]]
    return "".join(out)

def finalize_shifts():
    """Wrap the collected shift lemmas as a module snippet (call after all cells are transformed)."""
    body = SHIFTS[0]
    SHIFTS[0] = ("\n/-! ###### shift lemmas (one per anchor and side) ###### -/\n\nnoncomputable section\n"
                 "open Real\nnamespace Zeta23Ext.Bridge.ThreePoint\n" + body + "\nend Zeta23Ext.Bridge.ThreePoint\n\nend\n")

if __name__ == "__main__":
    import sys
    print(transform_cells(open(sys.argv[1], encoding="utf-8").read()))
