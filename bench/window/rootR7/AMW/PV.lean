/-
AMW/PV.lean — the positive-variation certificate for the AMTOPA profile, and its admissible window.

p := vAM/MAM.  On each of the 64 cells [i/128, (i+1)/128] of [0, 1/2], p′ = vAMd/MAM is bounded above by
its value at the midpoint m_i = (2i+1)/256 plus 78/256 (|vAMd′| = |vAMdd| ≤ 78, the mean value
theorem).  The midpoint value is bounded term by term: sin(√2 m_i) from the Taylor enclosure, and
sin(2πj m_i) = sin(π·j(2i+1)/128) from a table of outward enclosures of sin(πq/128), q ≤ 64, each
checked once against `sinPiI` (AMW/Trig.lean), and periodicity/reflection.  Hence
∫₀^{1/2} max(p′,0) ≤ Σ_i max(U_i,0)/160 = 0.04259 ≤ ρ = 9/200, a rational the kernel evaluates
(`pvCheck`); the budgets √p(0) + 2ρ ≤ 1, p(0) + 4ρ ≤ 1 hold with p(0) = 0.80428.
Hence `admWindow_phiW`.
-/
import AMW.Trig
import AMW.Window
import AMW.Profile

noncomputable section

open Real Set MeasureTheory

namespace AMW

open Zeta23

/-! ### the rational checker -/

def sumQ (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumQ f n + f n

def allQ (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allQ f n && f n

theorem sumQ_eq (f : ℕ → ℚ) (n : ℕ) : sumQ f n = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumQ, ih, Finset.sum_range_succ]

theorem allQ_iff (f : ℕ → Bool) (n : ℕ) : allQ f n = true ↔ ∀ j < n, f j = true := by
  induction n with
  | zero => simp [allQ]
  | succ n ih =>
    rw [allQ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact h1 j h
      · exact h ▸ h2
    · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

/-- outward enclosures of sin(πq/128), q = 0, …, 64, in units of 10⁻¹⁰. -/
def sinTabZ : List (ℤ × ℤ) := [(-23, 23), (245412211, 245412336), (490676618, 490676821), (735645460, 735645741), (980171177, 980171535), (1224106475, 1224106910), (1467304418, 1467304929), (1709618512, 1709619097), (1950902796, 1950903456), (2191011930, 2191012663), (2429801281, 2429802085), (2667127010, 2667127885), (2902846163, 2902847107), (3136816751, 3136817762), (3368897838, 3368898914), (3598949628, 3598950767), (3826833546, 3826834747), (4052412323, 4052413585), (4275550080, 4275551398), (4496112407, 4496113780), (4713966444, 4713967869), (4928980966, 4928982440), (5141026455, 5141027976), (5349975184, 5349976748), (5555701288, 5555702893), (5758080847, 5758082491), (5956991955, 5956993634), (6152314796, 6152316505), (6343931713, 6343933451), (6531727285, 6531729047), (6715588390, 6715590173), (6895404278, 6895406078), (7071067175, 7071068989), (7242470227, 7242471943), (7409510684, 7409512305), (7572087929, 7572089455), (7730104029, 7730105464), (7883463803, 7883465147), (8032074872, 8032076129), (8175847718, 8175848890), (8314695739, 8314696827), (8448535296, 8448536304), (8577285771, 8577286701), (8700869608, 8700870463), (8819212365, 8819213148), (8932242757, 8932243471), (9039892700, 9039893347), (9142097347, 9142097932), (9238795136, 9238795661), (9329927819, 9329928287), (9415440501, 9415440916), (9495281672, 9495282037), (9569403240, 9569403558), (9637760555, 9637760831), (9700312443, 9700312679), (9757021224, 9757021424), (9807852739, 9807852907), (9852776368, 9852776508), (9891765053, 9891765168), (9924795306, 9924795400), (9951847233, 9951847310), (9972904538, 9972904601), (9987954536, 9987954590), (9996988163, 9996988211), (9999999977, 10000000023)]

def tabI (q : ℕ) : ℚ × ℚ :=
  (((sinTabZ.getD q (0, 0)).1 : ℚ) / 10000000000, ((sinTabZ.getD q (0, 0)).2 : ℚ) / 10000000000)

def tabOk : Bool :=
  allQ (fun q => sinPiOk ((q : ℚ) / 128) && decide ((tabI q).1 ≤ (sinPiI ((q : ℚ) / 128)).1)
    && decide ((sinPiI ((q : ℚ) / 128)).2 ≤ (tabI q).2)) 65

def ineg (I : ℚ × ℚ) : ℚ × ℚ := (-I.2, -I.1)

/-- an enclosure of sin(πr/128). -/
def sinLook (r : ℕ) : ℚ × ℚ :=
  if r % 256 ≤ 64 then tabI (r % 256)
  else if r % 256 ≤ 128 then tabI (128 - r % 256)
  else if r % 256 ≤ 192 then ineg (tabI (r % 256 - 128))
  else ineg (tabI (256 - r % 256))

def midQ (i : ℕ) : ℚ := (2 * i + 1) / 256

/-- upper bound for the j-th term `−cAM j·ωAM j·sin(ωAM j·m_i)` of `vAMd m_i`. -/
def termU (i j : ℕ) : ℚ :=
  if j = 0 then -(s2LoQ * max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)))
  else if 0 ≤ -(2 * j * cAM j) then -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).2
  else -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).1

def termOk (i : ℕ) : Bool := decide (0 ≤ fl (s2LoQ * midQ i)) && decide (s2HiQ * midQ i ≤ 1)

def cellU (i : ℕ) : ℚ := sumQ (termU i) 13 + 78 / 256

def pvCheck (ρ : ℚ) : Bool :=
  tabOk && allQ termOk 64 && decide (sumQ (fun i => max (cellU i) 0) 64 / 160 ≤ ρ)

/-! ### soundness -/

theorem tabI_sound (h : tabOk = true) {q : ℕ} (hq : q < 65) :
    InI (tabI q) (Real.sin (Real.pi * ((q : ℝ) / 128))) := by
  rw [tabOk, allQ_iff] at h
  have hq' := h q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
  obtain ⟨⟨hok, h1⟩, h2⟩ := hq'
  have hs := sinPiI_sound _ hok
  push_cast at hs
  exact ⟨(Rat.cast_le.mpr h1).trans hs.1, hs.2.trans (Rat.cast_le.mpr h2)⟩

theorem ineg_sound {I : ℚ × ℚ} {x : ℝ} (h : InI I x) : InI (ineg I) (-x) := by
  obtain ⟨h1, h2⟩ := h
  unfold ineg InI; push_cast; exact ⟨neg_le_neg h2, neg_le_neg h1⟩

theorem sinLook_sound (h : tabOk = true) (r : ℕ) :
    InI (sinLook r) (Real.sin (Real.pi * ((r : ℝ) / 128))) := by
  have hper : Real.sin (Real.pi * ((r : ℝ) / 128)) = Real.sin (Real.pi * (((r % 256 : ℕ) : ℝ) / 128)) := by
    have hr : (r : ℝ) = ((r % 256 : ℕ) : ℝ) + ((r / 256 : ℕ) : ℝ) * 256 := by
      exact_mod_cast (by omega : r = r % 256 + r / 256 * 256)
    rw [hr, show Real.pi * ((((r % 256 : ℕ) : ℝ) + ((r / 256 : ℕ) : ℝ) * 256) / 128)
      = Real.pi * (((r % 256 : ℕ) : ℝ) / 128) + ((r / 256 : ℕ) : ℝ) * (2 * Real.pi) by ring]
    exact Real.sin_add_nat_mul_two_pi _ _
  rw [hper]
  unfold sinLook
  have hq256 : r % 256 < 256 := Nat.mod_lt _ (by norm_num)
  generalize r % 256 = q at hq256 ⊢
  split_ifs with h1 h2 h3
  · exact tabI_sound h (by omega)
  · have e : Real.sin (Real.pi * ((q : ℝ) / 128)) = Real.sin (Real.pi * (((128 - q : ℕ) : ℝ) / 128)) := by
      rw [Nat.cast_sub h2, show Real.pi * ((((128 : ℕ) : ℝ) - (q : ℝ)) / 128)
        = Real.pi - Real.pi * ((q : ℝ) / 128) by push_cast; ring, Real.sin_pi_sub]
    rw [e]; exact tabI_sound h (by omega)
  · have e : Real.sin (Real.pi * ((q : ℝ) / 128)) = -Real.sin (Real.pi * (((q - 128 : ℕ) : ℝ) / 128)) := by
      rw [Nat.cast_sub (by omega : 128 ≤ q), show Real.pi * (((q : ℝ) - ((128 : ℕ) : ℝ)) / 128)
        = Real.pi * ((q : ℝ) / 128) - Real.pi by push_cast; ring, Real.sin_sub_pi]; ring
    rw [e]; exact ineg_sound (tabI_sound h (by omega))
  · have e : Real.sin (Real.pi * ((q : ℝ) / 128)) = -Real.sin (Real.pi * (((256 - q : ℕ) : ℝ) / 128)) := by
      rw [Nat.cast_sub (by omega : q ≤ 256), show Real.pi * ((((256 : ℕ) : ℝ) - (q : ℝ)) / 128)
        = 2 * Real.pi - Real.pi * ((q : ℝ) / 128) by push_cast; ring, Real.sin_two_pi_sub]; ring
    rw [e]; exact ineg_sound (tabI_sound h (by omega))

theorem termU_sound (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) (j : ℕ) :
    -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * (midQ i : ℝ))) ≤ ((termU i j : ℚ) : ℝ) := by
  unfold termU
  have hm0 : (0:ℚ) ≤ midQ i := by unfold midQ; positivity
  by_cases hj : j = 0
  · subst hj
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [if_true]
    obtain ⟨h0, h1⟩ := hok
    rw [cAM_zero, ωAM_zero, one_mul]
    have hm' : (0:ℝ) ≤ midQ i := by exact_mod_cast hm0
    have hs2 := s2LoQ_le
    have hθ0 : 0 ≤ Real.sqrt 2 * midQ i := mul_nonneg (Real.sqrt_nonneg 2) hm'
    have hθ1 : Real.sqrt 2 * midQ i ≤ 1 := by
      have : ((s2HiQ * midQ i : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
      push_cast at this
      nlinarith [s2HiQ_ge]
    have hl0 : (0:ℝ) ≤ ((fl (s2LoQ * midQ i) : ℚ) : ℝ) := by exact_mod_cast h0
    have hlθ : ((fl (s2LoQ * midQ i) : ℚ) : ℝ) ≤ Real.sqrt 2 * midQ i :=
      (fl_le _).trans (by push_cast; exact mul_le_mul_of_nonneg_right hs2 hm')
    have hsin := sin_ge_of hl0 hlθ hθ1
    have hsin0 : 0 ≤ Real.sin (Real.sqrt 2 * midQ i) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (hθ1.trans (by linarith [Real.pi_gt_three]))
    have hlb : ((max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)) : ℚ) : ℝ)
        ≤ Real.sin (Real.sqrt 2 * midQ i) := by
      push_cast
      exact max_le hsin0 ((fl_le _).trans (by exact_mod_cast hsin))
    have hs2lo0 : (0:ℝ) ≤ ((s2LoQ : ℚ) : ℝ) := by simp only [s2LoQ]; push_cast; norm_num
    push_cast at hlb ⊢
    nlinarith
  · simp only [hj, if_false]
    have hω : ωAM j = 2 * Real.pi * j := by simp [ωAM, hj]
    have hS := piMul_sound (sinLook_sound htab (j * (2 * i + 1)))
    have e : -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * (midQ i : ℝ)))
        = ((-(2 * j * cAM j) : ℚ) : ℝ)
          * (Real.pi * Real.sin (Real.pi * (((j * (2 * i + 1) : ℕ) : ℝ) / 128))) := by
      rw [hω]; simp only [midQ]; push_cast; ring_nf
    rw [e]
    obtain ⟨h1, h2⟩ := hS
    split_ifs with he
    · have he' : (0:ℝ) ≤ ((-(2 * j * cAM j) : ℚ) : ℝ) := by exact_mod_cast he
      push_cast at he' h2 ⊢
      exact mul_le_mul_of_nonneg_left h2 he'
    · have he' : ((-(2 * j * cAM j) : ℚ) : ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
      push_cast at he' h1 ⊢
      exact mul_le_mul_of_nonpos_left h1 he'

theorem vAMd_mid_le (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) :
    vAMd (midQ i) ≤ ((sumQ (termU i) 13 : ℚ) : ℝ) := by
  rw [sumQ_eq, Rat.cast_sum, vAMd]
  exact Finset.sum_le_sum fun j _ => termU_sound htab hok j

theorem vAMd_lipschitz (x y : ℝ) : vAMd y ≤ vAMd x + 78 * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := vAMd) (s := Set.univ) (C := 78)
    (fun x _ => (hasDerivAt_vAMd x).differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs, (hasDerivAt_vAMd x).deriv]; exact abs_vAMdd_le x)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  linarith [le_abs_self (vAMd y - vAMd x)]

theorem deriv_vAM_div : deriv (fun s => vAM s / MAM) = fun s => vAMd s / MAM :=
  funext fun s => ((hasDerivAt_vAM s).div_const MAM).deriv

/-- **positive variation of vAM/MAM from a passing check.** -/
theorem posVar_of_check {ρ : ℚ} (h : pvCheck ρ = true) :
    ∫ s in (0:ℝ)..(1 / 2), max (deriv (fun s => vAM s / MAM) s) 0 ≤ (ρ : ℝ) := by
  simp only [pvCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨htab, hcells⟩, hsum⟩ := h
  rw [allQ_iff] at hcells
  rw [deriv_vAM_div]
  have hM : (0:ℝ) < MAM := MAM_pos
  set a : ℕ → ℝ := fun k => (k : ℝ) / 128 with ha
  have hcont : Continuous fun s => max (vAMd s / MAM) 0 :=
    (((continuous_iff_continuousAt.mpr fun x => (hasDerivAt_vAMd x).continuousAt)).div_const MAM).max
      continuous_const
  have hcell : ∀ i < 64, ∫ s in a i..a (i + 1), max (vAMd s / MAM) 0
      ≤ 1 / 128 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
    intro i hi
    have hab : a i ≤ a (i + 1) := by simp only [ha]; gcongr; push_cast; linarith
    have hmid : ((midQ i : ℚ) : ℝ) = (2 * i + 1) / 256 := by simp only [midQ]; push_cast; ring
    have hvm := vAMd_mid_le htab (hcells i hi)
    have hpt : ∀ s ∈ Set.Icc (a i) (a (i + 1)), max (vAMd s / MAM) 0
        ≤ ((max (cellU i) 0 : ℚ) : ℝ) / MAM := by
      intro s hs
      have hd : |s - (midQ i : ℝ)| ≤ 1 / 256 := by
        rw [hmid, abs_le]
        simp only [ha, Set.mem_Icc] at hs
        push_cast at hs
        obtain ⟨hs1, hs2⟩ := hs
        constructor <;> linarith
      have hlip := vAMd_lipschitz (midQ i : ℝ) s
      have hU : vAMd s ≤ ((cellU i : ℚ) : ℝ) := by
        simp only [cellU]; push_cast
        linarith
      push_cast
      exact max_le ((div_le_div_of_nonneg_right hU hM.le).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hM.le)) (div_nonneg (le_max_right _ _) hM.le)
    calc ∫ s in a i..a (i + 1), max (vAMd s / MAM) 0
        ≤ ∫ s in a i..a (i + 1), ((max (cellU i) 0 : ℚ) : ℝ) / MAM :=
          intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _) hpt
      _ = 1 / 128 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          simp only [ha]; push_cast; ring
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := fun s => max (vAMd s / MAM) 0) (a := a) (n := 64) (fun k _ => hcont.intervalIntegrable _ _)
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a 64 = 1 / 2 := by simp only [ha]; norm_num
  rw [ha0, haN] at hsplit
  rw [← hsplit]
  refine (Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.mp hi)).trans ?_
  have hq : ((sumQ (fun i => max (cellU i) 0) 64 / 160 : ℚ) : ℝ) ≤ (ρ : ℝ) := by
    exact_mod_cast hsum
  refine le_of_eq_of_le ?_ hq
  rw [sumQ_eq, ← Finset.mul_sum, ← Finset.sum_div]
  push_cast
  simp only [MAM]
  ring

/-! ### the AMTOPA profile and its admissible window -/

set_option maxRecDepth 100000 in
theorem pvCheck_AM : pvCheck (9 / 200) = true := by decide +kernel

theorem deriv2_vAM_div : deriv (deriv (fun s => vAM s / MAM)) = fun s => vAMdd s / MAM := by
  rw [deriv_vAM_div]
  exact funext fun s => ((hasDerivAt_vAMd s).div_const MAM).deriv

theorem vAM_zero_div_le : vAM 0 / MAM ≤ 81 / 100 := by
  rw [vAM_zero, MAM]; norm_num

theorem profile_AM : Profile (fun s => vAM s / MAM) (1 / 10) (14 / 5) (312 / 5) (9 / 200) where
  δ_pos := by norm_num
  A₁_nonneg := by norm_num
  A₂_nonneg := by norm_num
  even := fun s => by simp only [vAM_even]
  contDiff := (vAM_contDiff.of_le le_top).div_const MAM
  pos := fun s hs => div_pos (vAM_pos_wide (by linarith)) MAM_pos
  ge_quarter := fun s hs => by
    have := vAM_ge_core hs
    rw [MAM, le_div_iff₀ (by norm_num)]; linarith
  le_one := fun s _ => by rw [div_le_one MAM_pos]; exact vAM_le s
  deriv_le := fun s _ => by
    rw [deriv_vAM_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
    linarith [abs_vAMd_le s]
  deriv2_le := fun s _ => by
    rw [deriv2_vAM_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
    linarith [abs_vAMdd_le s]
  posVar := by
    have h := posVar_of_check pvCheck_AM
    push_cast at h
    exact h
  budget := by
    have h0 : Real.sqrt (vAM 0 / MAM) ≤ 9 / 10 := by
      rw [show (9 / 10 : ℝ) = Real.sqrt (81 / 100) by
        rw [show (81 / 100 : ℝ) = (9 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt vAM_zero_div_le
    linarith
  budget_sq := by linarith [vAM_zero_div_le]

/-- the window constant of the AMTOPA window. -/
def cAMW (ϱ : ℝ → ℝ) : ℝ := cMod ϱ (14 / 5) (312 / 5 + 2 * (14 / 5) ^ 2)

/-- **The AMTOPA window is admissible.** -/
theorem admWindow_phiW {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    AdmWindow (phiW ϱ L w) L w (cAMW ϱ) :=
  admWindow_fP profile_AM hϱ hw hwL

end AMW

end
