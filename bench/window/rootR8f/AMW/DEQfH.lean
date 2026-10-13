import AMW.DEDefs
import AMW.DEQfCells

/-! ###### AMW/DEQfH — obligation H from a checked cell table (mvt-engine; D track, step 6)

For a piecewise-linear certificate `c` (`AMW/DEDefs`, knots `k/N`, `N = DkInv`) the check `certHOk c S sN vlo`
gives `CertHNonneg c`, i.e. `ĝ(α) ≤ qf(α)` for every `α ≥ 0` (`certH_of_ok`):
* knot interval `k ≤ N − 2`: `S k` Taylor cells (`AMW.DQ.knotOk`, `knot_sound`);
* `[1 − 1/N, 1]`: `ĝ = N y_{N−1} (1 − α)` (as `y_N = 0`) against `qf ≥ vlo² (1 − α) / ZQ` (`edge_sound`);
* `α ≥ 1`: `qf = 0` there and `ĝ ≤ 0` from the knot signs `y_k ≤ 0` (`k ≥ N`, `y_N = 0`). ###### -/

noncomputable section

open Real

namespace AMW.DE

open AMW.DQ

/-- the knot values as rationals -/
def yQ (c : PLCert) (k : ℕ) : ℚ := (c.Y k : ℚ) / c.E

theorem yQ_cast (c : PLCert) (k : ℕ) : ((yQ c k : ℚ) : ℝ) = c.y k := by
  unfold yQ PLCert.y; push_cast; ring

/-- every check of obligation H for `c`: the edge bound `vlo` on `sN` cells, the edge interval, the knot signs
beyond the band, and `S k` cells on each knot interval `k = 0 … N − 2` -/
def certHOk (c : PLCert) (S : List ℕ) (sN : ℕ) (vlo : ℚ) : Bool :=
  decide (2 ≤ c.DkInv) && decide (0 < c.E) && decide (0 < sN) && vloOk c.DkInv sN vlo &&
    edgeOk c.DkInv (yQ c (c.DkInv - 1)) vlo && decide (c.Y c.DkInv = 0) &&
    ((List.range c.n).all fun k => decide (k ≤ c.DkInv) || decide (c.Y k ≤ 0)) &&
    (List.range (c.DkInv - 1)).all fun k =>
      decide (0 < S.getD k 1) && knotOk c.DkInv (S.getD k 1) k (yQ c k) (yQ c (k + 1))

theorem qfAM_eq_on {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : qfAM α = AMW.qfAM α := by
  unfold qfAM AMW.qfAM Ivam
  rw [if_pos (by rw [abs_of_nonneg h0]; exact h1), abs_of_nonneg h0]

theorem qfAM_nonneg (α : ℝ) : 0 ≤ qfAM α := by
  unfold qfAM
  split_ifs with h
  · exact div_nonneg (vConvAM_nonneg (abs_nonneg α) h) (sq_nonneg _)
  · exact le_rfl

/-- obligation H from its checks, each a separate hypothesis (so that a certificate can decide them one at a time) -/
theorem certH_of_parts {c : PLCert} {S : List ℕ} {sN : ℕ} {vlo : ℚ} (hN : 2 ≤ c.DkInv) (hE : 0 < c.E)
    (hsN : 0 < sN) (hv : vloOk c.DkInv sN vlo = true) (he : edgeOk c.DkInv (yQ c (c.DkInv - 1)) vlo = true)
    (hYN : c.Y c.DkInv = 0) (hsg : ∀ k < c.n, k ≤ c.DkInv ∨ c.Y k ≤ 0)
    (hk : ∀ k < c.DkInv - 1, 0 < S.getD k 1 ∧
      knotOk c.DkInv (S.getD k 1) k (yQ c k) (yQ c (k + 1)) = true) :
    CertHNonneg c := by
  intro α hα
  set N := c.DkInv with hNdef
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hE' : (0 : ℝ) < c.E := by exact_mod_cast hE
  set k := ⌊α * N⌋₊ with hkdef
  have h1 : (k : ℝ) ≤ α * N := Nat.floor_le (mul_nonneg hα hN'.le)
  have h2 : α * N ≤ k + 1 := (Nat.lt_floor_add_one _).le
  rw [ghat_seg c (by omega) k h1 h2]
  rcases lt_or_ge k (N - 1) with hlt | hge
  · -- a knot interval inside the band
    obtain ⟨hs, hko⟩ := hk k hlt
    have hx : α ∈ Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N) :=
      ⟨by rw [div_le_iff₀ hN']; exact h1, by rw [le_div_iff₀ hN']; exact h2⟩
    have hq := knot_sound (by omega) hs hko α hx
    have hk1 : (k : ℝ) + 1 ≤ N - 1 := by
      have : k + 1 ≤ N - 1 := by omega
      have h' : ((k + 1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h'; push_cast at h'; exact h'
    have hα1 : α ≤ 1 := by
      have : α * N ≤ N := by linarith
      nlinarith
    rw [qfAM_eq_on hα hα1, ← yQ_cast, ← yQ_cast, mul_comm α]
    exact hq
  · rcases eq_or_lt_of_le hge with heq | hgt
    · -- the last interval `[1 − 1/N, 1]`
      have hkr : (k : ℝ) = N - 1 := by rw [← heq, Nat.cast_sub (by omega)]; push_cast; ring
      have hα1 : α ≤ 1 := by
        have : α * N ≤ N := by linarith
        nlinarith
      have hx1 : α ∈ Set.Icc ((1 : ℝ) - 1 / N) 1 := by
        constructor
        · have e : (1 : ℝ) - 1 / N = (N - 1) / N := by field_simp
          rw [e, div_le_iff₀ hN']; linarith
        · exact hα1
      have hq := edge_sound hN hsN hv he α hx1
      have hyN : c.y N = 0 := by unfold PLCert.y; rw [hYN]; simp
      rw [qfAM_eq_on hα hα1, ← heq, Nat.sub_add_cancel (by omega), hyN]
      rw [yQ_cast] at hq
      have e : c.y (N - 1) + (0 - c.y (N - 1)) * (α * N - ((N - 1 : ℕ) : ℝ)) = (N * c.y (N - 1)) * (1 - α) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [e]; exact hq
    · -- beyond the band: `ĝ ≤ 0 ≤ qf`
      have hY : ∀ j : ℕ, N ≤ j → c.y j ≤ 0 := by
        intro j hj
        unfold PLCert.y
        refine div_nonpos_of_nonpos_of_nonneg ?_ hE'.le
        rcases lt_or_ge j c.n with hjn | hjn
        · rcases hsg j hjn with hle | hneg
          · have : j = N := by omega
            rw [this, hYN]; simp
          · exact_mod_cast hneg
        · rw [c.Y_eq_zero hjn]; simp
      have hyk := hY k (by omega)
      have hyk1 := hY (k + 1) (by omega)
      have ht0 : 0 ≤ α * N - k := by linarith
      have ht1 : α * N - k ≤ 1 := by linarith
      have e : c.y k + (c.y (k + 1) - c.y k) * (α * N - k)
          = (1 - (α * N - k)) * c.y k + (α * N - k) * c.y (k + 1) := by ring
      rw [e]
      have : (1 - (α * N - k)) * c.y k + (α * N - k) * c.y (k + 1) ≤ 0 := by
        have a1 : (1 - (α * N - k)) * c.y k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hyk
        have a2 : (α * N - k) * c.y (k + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hyk1
        linarith
      exact this.trans (qfAM_nonneg α)

theorem certH_of_ok {c : PLCert} {S : List ℕ} {sN : ℕ} {vlo : ℚ} (h : certHOk c S sN vlo = true) :
    CertHNonneg c := by
  simp only [certHOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hN, hE⟩, hsN⟩, hv⟩, he⟩, hYN⟩, hsg⟩, hk⟩ := h
  exact certH_of_parts hN hE hsN hv he hYN hsg hk

end AMW.DE
