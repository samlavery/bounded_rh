"""Assemble AT7T.lean: AT7c with the band-profile (τ = (q+1)/q) bridge and m = 154.
Usage: assemble_at7t.py PROFILE.lean|PLACEHOLDER OUT.lean
  PROFILE.lean: a section proving `Zeta23Ext.BridgeW.band_profile_holds : BandProfile` (bridge-port), inserted after
  the τ chain; PLACEHOLDER inserts a `sorry` stand-in (compile test of the assembly only, never for submission;
  its output must be named AT7T_PLACEHOLDER_SORRY.lean and never copied to UPLOAD_*)."""
import sys, os
H = os.path.dirname(os.path.abspath(__file__)); W = os.path.join(H, "..")
src = open(os.path.join(W, "AT7c.lean"), encoding="utf-8").read()
dev = open(os.path.join(H, "TauDev.lean"), encoding="utf-8").read()
body = dev[dev.index("noncomputable section"):]
assert body.rstrip().endswith("end")
prof = sys.argv[1]
if prof == "PLACEHOLDER":
    assert "PLACEHOLDER_SORRY" in sys.argv[2], "placeholder output must be named *PLACEHOLDER_SORRY*"
    PROF = ("\nnoncomputable section\nnamespace Zeta23Ext.BridgeW\n"
            "/-- PLACEHOLDER (assembly compile test only) -/\ntheorem band_profile_holds : BandProfile := by sorry\n"
            "end Zeta23Ext.BridgeW\nend\n")
else:
    PROF = "\n" + open(prof, encoding="utf-8").read() + "\n"
TAIL_N = '''
noncomputable section

namespace AMW

open Filter Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- **The n-point bound for the AM window under the band profile** (`c (m − q) ≤ (q+1)/q`), from a certificate. -/
theorem am_dyadic_n_τ (hP : BandProfile) {n : ℕ} (hn : 3 ≤ n) {W : WCert n} (hW : W.Adm) {bmin : ℝ}
    (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) {c κ : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 * n ≤ m)
    (hA0τ : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (((n - 1 : ℕ) : ℝ) + 1) / ((n - 1 : ℕ) : ℝ))
    (hκ : κ ≤ Phi_w' n c m W.B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := n_point_bound_w'_τ hP n c m W hn hm hW hbmin hb hc hCert hA0τ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star' T (2 * T)
  have h0 : (κ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Phi_w' n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

end AMW

end
'''
MARK = "/-! ###### tail: the AM seven-point bound from the certificate `AMW.Cert.AT7_cert_full` ###### -/"
assert src.count(MARK) == 1
BANNER = "/-! ###### the band profile: block bounds under `c (m − q) ≤ (q+1)/q` (AMTOPA's band bound, after Gebendorfer) ###### -/\n\n"
src = src.replace(MARK, BANNER + body + PROF + TAIL_N + "\n" + MARK)
def rep(old, new):
    global src
    assert src.count(old) == 1, old[:80]; src = src.replace(old, new)
rep("""theorem kappa_le : candidateKappa ≤ Phi_w' 7 ((787380 : ℝ) / 100000000) 133 W7.B := by""",
    """theorem kappa_le : candidateKappa ≤ Phi_w' 7 ((787380 : ℝ) / 100000000) 154 W7.B := by""")
rep("""  am_dyadic_n (n := 7) (by norm_num) W7_adm (by norm_num : (0 : ℝ) < (41468 : ℝ) / 100000000) W7_bmin (by norm_num) (m := 133)
    (by norm_num) (by norm_num) kappa_le cert_AM""",
    """  am_dyadic_n_τ band_profile_holds (n := 7) (by norm_num) W7_adm (by norm_num : (0 : ℝ) < (41468 : ℝ) / 100000000) W7_bmin
    (by norm_num) (m := 154) (by norm_num) (by norm_num) kappa_le cert_AM""")
# header
rep("Riemann.fail submission: an unconditional critical-line proportion of 6734302/10000000 = 0.6734302, for the",
    "Riemann.fail submission: an unconditional critical-line proportion of 6734383/10000000 = 0.6734383, for the")
rep("half-space by reflection).  Constant Φ = (H_W − B(m−6)/m)/(1 − c(m−6)/m) at m = 133, ≥ 0.673430201.",
    "half-space by reflection).  The block bound uses the band profile min((q+1)/q, E_band) ≤ defect (q = 6, τ = 7/6;\n"
    "AMTOPA's band bound, after Gebendorfer), so c(m−q) ≤ 7/6 replaces c(m−q) ≤ 1.\n"
    "Constant Φ = (H_W − B(m−6)/m)/(1 − c(m−6)/m) at m = 154, ≥ 0.673438375.")
rep("Sources and attributions:\n", "Method: τ = 7/6 band profile (AMTOPA Lemma, via Gebendorfer 2026 Lemma 3.3) on the AT7 seven-point certificate.\n\n"
    "Sources and attributions:\n"
    "* the band profile (τ = (q+1)/q in place of 1): AMTOPA, zeta-exact-pressure (MIT), as presented in\n"
    "  Gebendorfer, \"Zeta Geometry and Class Cap\" (preprint), Lemma 3.3; proved here (`band_profile_holds`);\n")
open(sys.argv[2], "w", encoding="utf-8").write(src)
print(len(src.encode()), "bytes ->", sys.argv[2])
