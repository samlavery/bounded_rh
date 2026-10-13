import AMW.AMS02Inst
import AMW.MinMode

/-! ###### `AMS02` with minorant terms: the slope inequality `cscheck` from per-term bounds for any reads
(`cscheck_sound`), and the minorant slope test `ctestM` / leaf `sleafM` (per expanded pair term a convex combination
of the constant and extended tangents at grid points, AMW/MinMode.lean), emitted by genmin.py (bridge-port). ###### -/

noncomputable section

namespace AMW.Cert.AMS02

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

set_option maxHeartbeats 40000000 in
/-- **the slope inequality from per-term bounds**: any reads whose terms each satisfy the per-term inequality of the
slope test give the certificate inequality on the box -/
theorem cscheck_sound (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T : ℕ) {x0 eu0 ed0 : ℕ} {v0 : Bool} {x1 eu1 ed1 : ℕ} {v1 : Bool} {x2 eu2 ed2 : ℕ} {v2 : Bool} {x3 eu3 ed3 : ℕ} {v3 : Bool} {x4 eu4 ed4 : ℕ} {v4 : Bool} {x5 eu5 ed5 : ℕ} {v5 : Bool} {x6 eu6 ed6 : ℕ} {v6 : Bool} {x7 eu7 ed7 : ℕ} {v7 : Bool} {x8 eu8 ed8 : ℕ} {v8 : Bool} {x9 eu9 ed9 : ℕ} {v9 : Bool} {x10 eu10 ed10 : ℕ} {v10 : Bool} {x11 eu11 ed11 : ℕ} {v11 : Bool} {x12 eu12 ed12 : ℕ} {v12 : Bool} {x13 eu13 ed13 : ℕ} {v13 : Bool} {x14 eu14 ed14 : ℕ} {v14 : Bool} {x15 eu15 ed15 : ℕ} {v15 : Bool} {x16 eu16 ed16 : ℕ} {v16 : Bool} {x17 eu17 ed17 : ℕ} {v17 : Bool} {x18 eu18 ed18 : ℕ} {v18 : Bool} {x19 eu19 ed19 : ℕ} {v19 : Bool} {x20 eu20 ed20 : ℕ} {v20 : Bool}
    (h : cscheck l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T x0 eu0 ed0 v0 x1 eu1 ed1 v1 x2 eu2 ed2 v2 x3 eu3 ed3 v3 x4 eu4 ed4 v4 x5 eu5 ed5 v5 x6 eu6 ed6 v6 x7 eu7 ed7 v7 x8 eu8 ed8 v8 x9 eu9 ed9 v9 x10 eu10 ed10 v10 x11 eu11 ed11 v11 x12 eu12 ed12 v12 x13 eu13 ed13 v13 x14 eu14 ed14 v14 x15 eu15 ed15 v15 x16 eu16 ed16 v16 x17 eu17 ed17 v17 x18 eu18 ed18 v18 x19 eu19 ed19 v19 x20 eu20 ed20 v20 = true)
    (H0 : rtok v0 (bitOf T 0) (l0) (u0) (q0) x0 eu0 ed0 = true → ∀ s : ℝ, (((l0) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u0) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 0) x0 : ℝ) - (tK (bitOf T 0) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 0) : ℝ) - (tM (bitOf T 0) x0 : ℝ) ∧ 32768 * (tval (bitOf T 0) x0 : ℝ) + 327680000000000 * (d * (s - (((q0) : ℕ) : ℝ) / 32768)) - 10 * (mchg v0 (bitOf T 0) (l0) (u0) (q0) x0 eu0 ed0 : ℝ) ≤ 327680000000000 * wfun s)
    (H1 : rtok v1 (bitOf T 1) (l0 + l1) (u0 + u1) (q0 + q1) x1 eu1 ed1 = true → ∀ s : ℝ, (((l0 + l1) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u0 + u1) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 1) x1 : ℝ) - (tK (bitOf T 1) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 1) : ℝ) - (tM (bitOf T 1) x1 : ℝ) ∧ 32768 * (tval (bitOf T 1) x1 : ℝ) + 327680000000000 * (d * (s - (((q0 + q1) : ℕ) : ℝ) / 32768)) - 10 * (mchg v1 (bitOf T 1) (l0 + l1) (u0 + u1) (q0 + q1) x1 eu1 ed1 : ℝ) ≤ 327680000000000 * wfun s)
    (H2 : rtok v2 (bitOf T 2) (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2) x2 eu2 ed2 = true → ∀ s : ℝ, (((l0 + l1 + l2) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u0 + u1 + u2) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 2) x2 : ℝ) - (tK (bitOf T 2) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 2) : ℝ) - (tM (bitOf T 2) x2 : ℝ) ∧ 32768 * (tval (bitOf T 2) x2 : ℝ) + 327680000000000 * (d * (s - (((q0 + q1 + q2) : ℕ) : ℝ) / 32768)) - 10 * (mchg v2 (bitOf T 2) (l0 + l1 + l2) (u0 + u1 + u2) (q0 + q1 + q2) x2 eu2 ed2 : ℝ) ≤ 327680000000000 * wfun s)
    (H3 : rtok v3 (bitOf T 3) (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3) x3 eu3 ed3 = true → ∀ s : ℝ, (((l0 + l1 + l2 + l3) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u0 + u1 + u2 + u3) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 3) x3 : ℝ) - (tK (bitOf T 3) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 3) : ℝ) - (tM (bitOf T 3) x3 : ℝ) ∧ 32768 * (tval (bitOf T 3) x3 : ℝ) + 327680000000000 * (d * (s - (((q0 + q1 + q2 + q3) : ℕ) : ℝ) / 32768)) - 10 * (mchg v3 (bitOf T 3) (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (q0 + q1 + q2 + q3) x3 eu3 ed3 : ℝ) ≤ 327680000000000 * wfun s)
    (H4 : rtok v4 (bitOf T 4) (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4) x4 eu4 ed4 = true → ∀ s : ℝ, (((l0 + l1 + l2 + l3 + l4) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u0 + u1 + u2 + u3 + u4) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 4) x4 : ℝ) - (tK (bitOf T 4) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 4) : ℝ) - (tM (bitOf T 4) x4 : ℝ) ∧ 32768 * (tval (bitOf T 4) x4 : ℝ) + 327680000000000 * (d * (s - (((q0 + q1 + q2 + q3 + q4) : ℕ) : ℝ) / 32768)) - 10 * (mchg v4 (bitOf T 4) (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (q0 + q1 + q2 + q3 + q4) x4 eu4 ed4 : ℝ) ≤ 327680000000000 * wfun s)
    (H5 : rtok v5 (bitOf T 5) (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5) x5 eu5 ed5 = true → ∀ s : ℝ, (((l0 + l1 + l2 + l3 + l4 + l5) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u0 + u1 + u2 + u3 + u4 + u5) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 5) x5 : ℝ) - (tK (bitOf T 5) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 5) : ℝ) - (tM (bitOf T 5) x5 : ℝ) ∧ 32768 * (tval (bitOf T 5) x5 : ℝ) + 327680000000000 * (d * (s - (((q0 + q1 + q2 + q3 + q4 + q5) : ℕ) : ℝ) / 32768)) - 10 * (mchg v5 (bitOf T 5) (l0 + l1 + l2 + l3 + l4 + l5) (u0 + u1 + u2 + u3 + u4 + u5) (q0 + q1 + q2 + q3 + q4 + q5) x5 eu5 ed5 : ℝ) ≤ 327680000000000 * wfun s)
    (H6 : rtok v6 (bitOf T 6) (l1) (u1) (q1) x6 eu6 ed6 = true → ∀ s : ℝ, (((l1) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u1) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 6) x6 : ℝ) - (tK (bitOf T 6) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 6) : ℝ) - (tM (bitOf T 6) x6 : ℝ) ∧ 32768 * (tval (bitOf T 6) x6 : ℝ) + 327680000000000 * (d * (s - (((q1) : ℕ) : ℝ) / 32768)) - 10 * (mchg v6 (bitOf T 6) (l1) (u1) (q1) x6 eu6 ed6 : ℝ) ≤ 327680000000000 * wfun s)
    (H7 : rtok v7 (bitOf T 7) (l1 + l2) (u1 + u2) (q1 + q2) x7 eu7 ed7 = true → ∀ s : ℝ, (((l1 + l2) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u1 + u2) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 7) x7 : ℝ) - (tK (bitOf T 7) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 7) : ℝ) - (tM (bitOf T 7) x7 : ℝ) ∧ 32768 * (tval (bitOf T 7) x7 : ℝ) + 327680000000000 * (d * (s - (((q1 + q2) : ℕ) : ℝ) / 32768)) - 10 * (mchg v7 (bitOf T 7) (l1 + l2) (u1 + u2) (q1 + q2) x7 eu7 ed7 : ℝ) ≤ 327680000000000 * wfun s)
    (H8 : rtok v8 (bitOf T 8) (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3) x8 eu8 ed8 = true → ∀ s : ℝ, (((l1 + l2 + l3) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u1 + u2 + u3) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 8) x8 : ℝ) - (tK (bitOf T 8) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 8) : ℝ) - (tM (bitOf T 8) x8 : ℝ) ∧ 32768 * (tval (bitOf T 8) x8 : ℝ) + 327680000000000 * (d * (s - (((q1 + q2 + q3) : ℕ) : ℝ) / 32768)) - 10 * (mchg v8 (bitOf T 8) (l1 + l2 + l3) (u1 + u2 + u3) (q1 + q2 + q3) x8 eu8 ed8 : ℝ) ≤ 327680000000000 * wfun s)
    (H9 : rtok v9 (bitOf T 9) (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4) x9 eu9 ed9 = true → ∀ s : ℝ, (((l1 + l2 + l3 + l4) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u1 + u2 + u3 + u4) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 9) x9 : ℝ) - (tK (bitOf T 9) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 9) : ℝ) - (tM (bitOf T 9) x9 : ℝ) ∧ 32768 * (tval (bitOf T 9) x9 : ℝ) + 327680000000000 * (d * (s - (((q1 + q2 + q3 + q4) : ℕ) : ℝ) / 32768)) - 10 * (mchg v9 (bitOf T 9) (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (q1 + q2 + q3 + q4) x9 eu9 ed9 : ℝ) ≤ 327680000000000 * wfun s)
    (H10 : rtok v10 (bitOf T 10) (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5) x10 eu10 ed10 = true → ∀ s : ℝ, (((l1 + l2 + l3 + l4 + l5) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u1 + u2 + u3 + u4 + u5) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 10) x10 : ℝ) - (tK (bitOf T 10) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 10) : ℝ) - (tM (bitOf T 10) x10 : ℝ) ∧ 32768 * (tval (bitOf T 10) x10 : ℝ) + 327680000000000 * (d * (s - (((q1 + q2 + q3 + q4 + q5) : ℕ) : ℝ) / 32768)) - 10 * (mchg v10 (bitOf T 10) (l1 + l2 + l3 + l4 + l5) (u1 + u2 + u3 + u4 + u5) (q1 + q2 + q3 + q4 + q5) x10 eu10 ed10 : ℝ) ≤ 327680000000000 * wfun s)
    (H11 : rtok v11 (bitOf T 11) (l2) (u2) (q2) x11 eu11 ed11 = true → ∀ s : ℝ, (((l2) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u2) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 11) x11 : ℝ) - (tK (bitOf T 11) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 11) : ℝ) - (tM (bitOf T 11) x11 : ℝ) ∧ 32768 * (tval (bitOf T 11) x11 : ℝ) + 327680000000000 * (d * (s - (((q2) : ℕ) : ℝ) / 32768)) - 10 * (mchg v11 (bitOf T 11) (l2) (u2) (q2) x11 eu11 ed11 : ℝ) ≤ 327680000000000 * wfun s)
    (H12 : rtok v12 (bitOf T 12) (l2 + l3) (u2 + u3) (q2 + q3) x12 eu12 ed12 = true → ∀ s : ℝ, (((l2 + l3) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u2 + u3) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 12) x12 : ℝ) - (tK (bitOf T 12) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 12) : ℝ) - (tM (bitOf T 12) x12 : ℝ) ∧ 32768 * (tval (bitOf T 12) x12 : ℝ) + 327680000000000 * (d * (s - (((q2 + q3) : ℕ) : ℝ) / 32768)) - 10 * (mchg v12 (bitOf T 12) (l2 + l3) (u2 + u3) (q2 + q3) x12 eu12 ed12 : ℝ) ≤ 327680000000000 * wfun s)
    (H13 : rtok v13 (bitOf T 13) (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4) x13 eu13 ed13 = true → ∀ s : ℝ, (((l2 + l3 + l4) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u2 + u3 + u4) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 13) x13 : ℝ) - (tK (bitOf T 13) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 13) : ℝ) - (tM (bitOf T 13) x13 : ℝ) ∧ 32768 * (tval (bitOf T 13) x13 : ℝ) + 327680000000000 * (d * (s - (((q2 + q3 + q4) : ℕ) : ℝ) / 32768)) - 10 * (mchg v13 (bitOf T 13) (l2 + l3 + l4) (u2 + u3 + u4) (q2 + q3 + q4) x13 eu13 ed13 : ℝ) ≤ 327680000000000 * wfun s)
    (H14 : rtok v14 (bitOf T 14) (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5) x14 eu14 ed14 = true → ∀ s : ℝ, (((l2 + l3 + l4 + l5) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u2 + u3 + u4 + u5) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 14) x14 : ℝ) - (tK (bitOf T 14) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 14) : ℝ) - (tM (bitOf T 14) x14 : ℝ) ∧ 32768 * (tval (bitOf T 14) x14 : ℝ) + 327680000000000 * (d * (s - (((q2 + q3 + q4 + q5) : ℕ) : ℝ) / 32768)) - 10 * (mchg v14 (bitOf T 14) (l2 + l3 + l4 + l5) (u2 + u3 + u4 + u5) (q2 + q3 + q4 + q5) x14 eu14 ed14 : ℝ) ≤ 327680000000000 * wfun s)
    (H15 : rtok v15 (bitOf T 15) (l3) (u3) (q3) x15 eu15 ed15 = true → ∀ s : ℝ, (((l3) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u3) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 15) x15 : ℝ) - (tK (bitOf T 15) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 15) : ℝ) - (tM (bitOf T 15) x15 : ℝ) ∧ 32768 * (tval (bitOf T 15) x15 : ℝ) + 327680000000000 * (d * (s - (((q3) : ℕ) : ℝ) / 32768)) - 10 * (mchg v15 (bitOf T 15) (l3) (u3) (q3) x15 eu15 ed15 : ℝ) ≤ 327680000000000 * wfun s)
    (H16 : rtok v16 (bitOf T 16) (l3 + l4) (u3 + u4) (q3 + q4) x16 eu16 ed16 = true → ∀ s : ℝ, (((l3 + l4) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u3 + u4) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 16) x16 : ℝ) - (tK (bitOf T 16) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 16) : ℝ) - (tM (bitOf T 16) x16 : ℝ) ∧ 32768 * (tval (bitOf T 16) x16 : ℝ) + 327680000000000 * (d * (s - (((q3 + q4) : ℕ) : ℝ) / 32768)) - 10 * (mchg v16 (bitOf T 16) (l3 + l4) (u3 + u4) (q3 + q4) x16 eu16 ed16 : ℝ) ≤ 327680000000000 * wfun s)
    (H17 : rtok v17 (bitOf T 17) (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5) x17 eu17 ed17 = true → ∀ s : ℝ, (((l3 + l4 + l5) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u3 + u4 + u5) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 17) x17 : ℝ) - (tK (bitOf T 17) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 17) : ℝ) - (tM (bitOf T 17) x17 : ℝ) ∧ 32768 * (tval (bitOf T 17) x17 : ℝ) + 327680000000000 * (d * (s - (((q3 + q4 + q5) : ℕ) : ℝ) / 32768)) - 10 * (mchg v17 (bitOf T 17) (l3 + l4 + l5) (u3 + u4 + u5) (q3 + q4 + q5) x17 eu17 ed17 : ℝ) ≤ 327680000000000 * wfun s)
    (H18 : rtok v18 (bitOf T 18) (l4) (u4) (q4) x18 eu18 ed18 = true → ∀ s : ℝ, (((l4) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u4) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 18) x18 : ℝ) - (tK (bitOf T 18) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 18) : ℝ) - (tM (bitOf T 18) x18 : ℝ) ∧ 32768 * (tval (bitOf T 18) x18 : ℝ) + 327680000000000 * (d * (s - (((q4) : ℕ) : ℝ) / 32768)) - 10 * (mchg v18 (bitOf T 18) (l4) (u4) (q4) x18 eu18 ed18 : ℝ) ≤ 327680000000000 * wfun s)
    (H19 : rtok v19 (bitOf T 19) (l4 + l5) (u4 + u5) (q4 + q5) x19 eu19 ed19 = true → ∀ s : ℝ, (((l4 + l5) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u4 + u5) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 19) x19 : ℝ) - (tK (bitOf T 19) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 19) : ℝ) - (tM (bitOf T 19) x19 : ℝ) ∧ 32768 * (tval (bitOf T 19) x19 : ℝ) + 327680000000000 * (d * (s - (((q4 + q5) : ℕ) : ℝ) / 32768)) - 10 * (mchg v19 (bitOf T 19) (l4 + l5) (u4 + u5) (q4 + q5) x19 eu19 ed19 : ℝ) ≤ 327680000000000 * wfun s)
    (H20 : rtok v20 (bitOf T 20) (l5) (u5) (q5) x20 eu20 ed20 = true → ∀ s : ℝ, (((l5) : ℕ) : ℝ) / SC ≤ s → s ≤ (((u5) : ℕ) : ℝ) / SC → ∃ d : ℝ, (tP (bitOf T 20) x20 : ℝ) - (tK (bitOf T 20) : ℝ) ≤ 1000000000 * d ∧ 1000000000 * d ≤ (tK (bitOf T 20) : ℝ) - (tM (bitOf T 20) x20 : ℝ) ∧ 32768 * (tval (bitOf T 20) x20 : ℝ) + 327680000000000 * (d * (s - (((q5) : ℕ) : ℝ) / 32768)) - 10 * (mchg v20 (bitOf T 20) (l5) (u5) (q5) x20 eu20 ed20 : ℝ) ≤ 327680000000000 * wfun s) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  have h' := h
  unfold cscheck at h'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hq01, hq02⟩, hq11⟩, hq12⟩, hq21⟩, hq22⟩, hq31⟩, hq32⟩, hq41⟩, hq42⟩, hq51⟩, hq52⟩, hok0⟩, hok1⟩, hok2⟩, hok3⟩, hok4⟩, hok5⟩, hok6⟩, hok7⟩, hok8⟩, hok9⟩, hok10⟩, hok11⟩, hok12⟩, hok13⟩, hok14⟩, hok15⟩, hok16⟩, hok17⟩, hok18⟩, hok19⟩, hok20⟩, hmain⟩ := h'
  have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
  obtain ⟨d0, hdl0, hdu0, hb0⟩ := H0 hok0
    (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  push_cast at hb0
  obtain ⟨d1, hdl1, hdu1, hb1⟩ := H1 hok1
    (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  push_cast at hb1
  obtain ⟨d2, hdl2, hdu2, hb2⟩ := H2 hok2
    (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  push_cast at hb2
  obtain ⟨d3, hdl3, hdu3, hb3⟩ := H3 hok3
    (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  push_cast at hb3
  obtain ⟨d4, hdl4, hdu4, hb4⟩ := H4 hok4
    (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  push_cast at hb4
  obtain ⟨d5, hdl5, hdu5, hb5⟩ := H5 hok5
    (g0 + g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42, h52])
  push_cast at hb5
  obtain ⟨d6, hdl6, hdu6, hb6⟩ := H6 hok6
    (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  push_cast at hb6
  obtain ⟨d7, hdl7, hdu7, hb7⟩ := H7 hok7
    (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  push_cast at hb7
  obtain ⟨d8, hdl8, hdu8, hb8⟩ := H8 hok8
    (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  push_cast at hb8
  obtain ⟨d9, hdl9, hdu9, hb9⟩ := H9 hok9
    (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  push_cast at hb9
  obtain ⟨d10, hdl10, hdu10, hb10⟩ := H10 hok10
    (g1 + g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42, h52])
  push_cast at hb10
  obtain ⟨d11, hdl11, hdu11, hb11⟩ := H11 hok11
    (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  push_cast at hb11
  obtain ⟨d12, hdl12, hdu12, hb12⟩ := H12 hok12
    (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  push_cast at hb12
  obtain ⟨d13, hdl13, hdu13, hb13⟩ := H13 hok13
    (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  push_cast at hb13
  obtain ⟨d14, hdl14, hdu14, hb14⟩ := H14 hok14
    (g2 + g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42, h52])
  push_cast at hb14
  obtain ⟨d15, hdl15, hdu15, hb15⟩ := H15 hok15
    (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  push_cast at hb15
  obtain ⟨d16, hdl16, hdu16, hb16⟩ := H16 hok16
    (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  push_cast at hb16
  obtain ⟨d17, hdl17, hdu17, hb17⟩ := H17 hok17
    (g3 + g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h31, h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h32, h42, h52])
  push_cast at hb17
  obtain ⟨d18, hdl18, hdu18, hb18⟩ := H18 hok18
    (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  push_cast at hb18
  obtain ⟨d19, hdl19, hdu19, hb19⟩ := H19 hok19
    (g4 + g5) (by push_cast; (try simp only [add_div]); linarith [h41, h51]) (by push_cast; (try simp only [add_div]); linarith [h42, h52])
  push_cast at hb19
  obtain ⟨d20, hdl20, hdu20, hb20⟩ := H20 hok20
    (g5) (by push_cast; (try simp only [add_div]); linarith [h51]) (by push_cast; (try simp only [add_div]); linarith [h52])
  push_cast at hb20
  rw [hSCe] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  have hl0 : (l0 : ℝ) ≤ q0 := by exact_mod_cast hq01
  have hu0 : (q0 : ℝ) ≤ u0 := by exact_mod_cast hq02
  have hl1 : (l1 : ℝ) ≤ q1 := by exact_mod_cast hq11
  have hu1 : (q1 : ℝ) ≤ u1 := by exact_mod_cast hq12
  have hl2 : (l2 : ℝ) ≤ q2 := by exact_mod_cast hq21
  have hu2 : (q2 : ℝ) ≤ u2 := by exact_mod_cast hq22
  have hl3 : (l3 : ℝ) ≤ q3 := by exact_mod_cast hq31
  have hu3 : (q3 : ℝ) ≤ u3 := by exact_mod_cast hq32
  have hl4 : (l4 : ℝ) ≤ q4 := by exact_mod_cast hq41
  have hu4 : (q4 : ℝ) ≤ u4 := by exact_mod_cast hq42
  have hl5 : (l5 : ℝ) ≤ q5 := by exact_mod_cast hq51
  have hu5 : (q5 : ℝ) ≤ u5 := by exact_mod_cast hq52
  have hP0 : (1000000000 : ℝ) * ((48468 : ℝ) + 24136977 * d0 + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5) ≤ (((48468000000000 + 24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) - (24136977 * tM (bitOf T 0) x0 + 0 * tM (bitOf T 1) x1 + 23349596 * tM (bitOf T 2) x2 + 100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5) : ℕ) : ℝ) := by
    have := natsub_ge (48468000000000 + 24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) (24136977 * tM (bitOf T 0) x0 + 0 * tM (bitOf T 1) x1 + 23349596 * tM (bitOf T 2) x2 + 100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5)
    push_cast at this
    linarith [hdu0, hdu1, hdu2, hdu3, hdu4, hdu5]
  have hN0 : -((1000000000 : ℝ) * ((48468 : ℝ) + 24136977 * d0 + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5)) ≤ (((24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) - (48468000000000 + 24136977 * tP (bitOf T 0) x0 + 0 * tP (bitOf T 1) x1 + 23349596 * tP (bitOf T 2) x2 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5) : ℕ) : ℝ) := by
    have := natsub_ge (24136977 * tK (bitOf T 0) + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5)) (48468000000000 + 24136977 * tP (bitOf T 0) x0 + 0 * tP (bitOf T 1) x1 + 23349596 * tP (bitOf T 2) x2 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5)
    push_cast at this
    linarith [hdl0, hdl1, hdl2, hdl3, hdl4, hdl5]
  have hml0 : ((q0 - l0 : ℕ) : ℝ) = (q0 : ℝ) - l0 := Nat.cast_sub hq01
  have hum0 : ((u0 - q0 : ℕ) : ℝ) = (u0 : ℝ) - q0 := Nat.cast_sub hq02
  have ht0 := mterm (e := g0 - (q0 : ℝ) / 32768) (E := ((48468 : ℝ) + 24136977 * d0 + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5)) (lo := ((q0 - l0 : ℕ) : ℝ) / 32768)
    (hi := ((u0 - q0 : ℕ) : ℝ) / 32768) (by rw [hml0]; linarith [h01]) (by rw [hum0]; linarith [h02])
    (by positivity) (by positivity) hP0 hN0 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP1 : (1000000000 : ℝ) * ((71367 : ℝ) + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 33894225 * d6 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10) ≤ (((71367000000000 + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) - (0 * tM (bitOf T 1) x1 + 23349596 * tM (bitOf T 2) x2 + 100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 33894225 * tM (bitOf T 6) x6 + 44051410 * tM (bitOf T 7) x7 + 76650404 * tM (bitOf T 8) x8 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10) : ℕ) : ℝ) := by
    have := natsub_ge (71367000000000 + 0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) (0 * tM (bitOf T 1) x1 + 23349596 * tM (bitOf T 2) x2 + 100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 33894225 * tM (bitOf T 6) x6 + 44051410 * tM (bitOf T 7) x7 + 76650404 * tM (bitOf T 8) x8 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10)
    push_cast at this
    linarith [hdu1, hdu2, hdu3, hdu4, hdu5, hdu6, hdu7, hdu8, hdu9, hdu10]
  have hN1 : -((1000000000 : ℝ) * ((71367 : ℝ) + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 33894225 * d6 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10)) ≤ (((0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) - (71367000000000 + 0 * tP (bitOf T 1) x1 + 23349596 * tP (bitOf T 2) x2 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 33894225 * tP (bitOf T 6) x6 + 44051410 * tP (bitOf T 7) x7 + 76650404 * tP (bitOf T 8) x8 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10) : ℕ) : ℝ) := by
    have := natsub_ge (0 * tK (bitOf T 1) + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 33894225 * tK (bitOf T 6) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10)) (71367000000000 + 0 * tP (bitOf T 1) x1 + 23349596 * tP (bitOf T 2) x2 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 33894225 * tP (bitOf T 6) x6 + 44051410 * tP (bitOf T 7) x7 + 76650404 * tP (bitOf T 8) x8 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10)
    push_cast at this
    linarith [hdl1, hdl2, hdl3, hdl4, hdl5, hdl6, hdl7, hdl8, hdl9, hdl10]
  have hml1 : ((q1 - l1 : ℕ) : ℝ) = (q1 : ℝ) - l1 := Nat.cast_sub hq11
  have hum1 : ((u1 - q1 : ℕ) : ℝ) = (u1 : ℝ) - q1 := Nat.cast_sub hq12
  have ht1 := mterm (e := g1 - (q1 : ℝ) / 32768) (E := ((71367 : ℝ) + 0 * d1 + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 33894225 * d6 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10)) (lo := ((q1 - l1 : ℕ) : ℝ) / 32768)
    (hi := ((u1 - q1 : ℕ) : ℝ) / 32768) (by rw [hml1]; linarith [h11]) (by rw [hum1]; linarith [h12])
    (by positivity) (by positivity) hP1 hN1 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP2 : (1000000000 : ℝ) * ((82339 : ℝ) + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 41968798 * d11 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14) ≤ (((82339000000000 + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) - (23349596 * tM (bitOf T 2) x2 + 100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 44051410 * tM (bitOf T 7) x7 + 76650404 * tM (bitOf T 8) x8 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10 + 41968798 * tM (bitOf T 11) x11 + 111897180 * tM (bitOf T 12) x12 + 76650404 * tM (bitOf T 13) x13 + 100000000 * tM (bitOf T 14) x14) : ℕ) : ℝ) := by
    have := natsub_ge (82339000000000 + 23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) (23349596 * tM (bitOf T 2) x2 + 100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 44051410 * tM (bitOf T 7) x7 + 76650404 * tM (bitOf T 8) x8 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10 + 41968798 * tM (bitOf T 11) x11 + 111897180 * tM (bitOf T 12) x12 + 76650404 * tM (bitOf T 13) x13 + 100000000 * tM (bitOf T 14) x14)
    push_cast at this
    linarith [hdu2, hdu3, hdu4, hdu5, hdu7, hdu8, hdu9, hdu10, hdu11, hdu12, hdu13, hdu14]
  have hN2 : -((1000000000 : ℝ) * ((82339 : ℝ) + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 41968798 * d11 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14)) ≤ (((23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) - (82339000000000 + 23349596 * tP (bitOf T 2) x2 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 44051410 * tP (bitOf T 7) x7 + 76650404 * tP (bitOf T 8) x8 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10 + 41968798 * tP (bitOf T 11) x11 + 111897180 * tP (bitOf T 12) x12 + 76650404 * tP (bitOf T 13) x13 + 100000000 * tP (bitOf T 14) x14) : ℕ) : ℝ) := by
    have := natsub_ge (23349596 * tK (bitOf T 2) + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 44051410 * tK (bitOf T 7) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 41968798 * tK (bitOf T 11) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14)) (82339000000000 + 23349596 * tP (bitOf T 2) x2 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 44051410 * tP (bitOf T 7) x7 + 76650404 * tP (bitOf T 8) x8 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10 + 41968798 * tP (bitOf T 11) x11 + 111897180 * tP (bitOf T 12) x12 + 76650404 * tP (bitOf T 13) x13 + 100000000 * tP (bitOf T 14) x14)
    push_cast at this
    linarith [hdl2, hdl3, hdl4, hdl5, hdl7, hdl8, hdl9, hdl10, hdl11, hdl12, hdl13, hdl14]
  have hml2 : ((q2 - l2 : ℕ) : ℝ) = (q2 : ℝ) - l2 := Nat.cast_sub hq21
  have hum2 : ((u2 - q2 : ℕ) : ℝ) = (u2 : ℝ) - q2 := Nat.cast_sub hq22
  have ht2 := mterm (e := g2 - (q2 : ℝ) / 32768) (E := ((82339 : ℝ) + 23349596 * d2 + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 44051410 * d7 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 41968798 * d11 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14)) (lo := ((q2 - l2 : ℕ) : ℝ) / 32768)
    (hi := ((u2 - q2 : ℕ) : ℝ) / 32768) (by rw [hml2]; linarith [h21]) (by rw [hum2]; linarith [h22])
    (by positivity) (by positivity) hP2 hN2 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP3 : (1000000000 : ℝ) * ((82339 : ℝ) + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14 + 41968798 * d15 + 44051410 * d16 + 23349596 * d17) ≤ (((82339000000000 + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) - (100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 76650404 * tM (bitOf T 8) x8 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10 + 111897180 * tM (bitOf T 12) x12 + 76650404 * tM (bitOf T 13) x13 + 100000000 * tM (bitOf T 14) x14 + 41968798 * tM (bitOf T 15) x15 + 44051410 * tM (bitOf T 16) x16 + 23349596 * tM (bitOf T 17) x17) : ℕ) : ℝ) := by
    have := natsub_ge (82339000000000 + 100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) (100000000 * tM (bitOf T 3) x3 + 100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 76650404 * tM (bitOf T 8) x8 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10 + 111897180 * tM (bitOf T 12) x12 + 76650404 * tM (bitOf T 13) x13 + 100000000 * tM (bitOf T 14) x14 + 41968798 * tM (bitOf T 15) x15 + 44051410 * tM (bitOf T 16) x16 + 23349596 * tM (bitOf T 17) x17)
    push_cast at this
    linarith [hdu3, hdu4, hdu5, hdu8, hdu9, hdu10, hdu12, hdu13, hdu14, hdu15, hdu16, hdu17]
  have hN3 : -((1000000000 : ℝ) * ((82339 : ℝ) + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14 + 41968798 * d15 + 44051410 * d16 + 23349596 * d17)) ≤ (((100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) - (82339000000000 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 76650404 * tP (bitOf T 8) x8 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10 + 111897180 * tP (bitOf T 12) x12 + 76650404 * tP (bitOf T 13) x13 + 100000000 * tP (bitOf T 14) x14 + 41968798 * tP (bitOf T 15) x15 + 44051410 * tP (bitOf T 16) x16 + 23349596 * tP (bitOf T 17) x17) : ℕ) : ℝ) := by
    have := natsub_ge (100000000 * tK (bitOf T 3) + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 76650404 * tK (bitOf T 8) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 111897180 * tK (bitOf T 12) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 41968798 * tK (bitOf T 15) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17)) (82339000000000 + 100000000 * tP (bitOf T 3) x3 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 76650404 * tP (bitOf T 8) x8 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10 + 111897180 * tP (bitOf T 12) x12 + 76650404 * tP (bitOf T 13) x13 + 100000000 * tP (bitOf T 14) x14 + 41968798 * tP (bitOf T 15) x15 + 44051410 * tP (bitOf T 16) x16 + 23349596 * tP (bitOf T 17) x17)
    push_cast at this
    linarith [hdl3, hdl4, hdl5, hdl8, hdl9, hdl10, hdl12, hdl13, hdl14, hdl15, hdl16, hdl17]
  have hml3 : ((q3 - l3 : ℕ) : ℝ) = (q3 : ℝ) - l3 := Nat.cast_sub hq31
  have hum3 : ((u3 - q3 : ℕ) : ℝ) = (u3 : ℝ) - q3 := Nat.cast_sub hq32
  have ht3 := mterm (e := g3 - (q3 : ℝ) / 32768) (E := ((82339 : ℝ) + 100000000 * d3 + 100000000 * d4 + 200000000 * d5 + 76650404 * d8 + 0 * d9 + 100000000 * d10 + 111897180 * d12 + 76650404 * d13 + 100000000 * d14 + 41968798 * d15 + 44051410 * d16 + 23349596 * d17)) (lo := ((q3 - l3 : ℕ) : ℝ) / 32768)
    (hi := ((u3 - q3 : ℕ) : ℝ) / 32768) (by rw [hml3]; linarith [h31]) (by rw [hum3]; linarith [h32])
    (by positivity) (by positivity) hP3 hN3 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP4 : (1000000000 : ℝ) * ((71367 : ℝ) + 100000000 * d4 + 200000000 * d5 + 0 * d9 + 100000000 * d10 + 76650404 * d13 + 100000000 * d14 + 44051410 * d16 + 23349596 * d17 + 33894225 * d18 + 0 * d19) ≤ (((71367000000000 + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) - (100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10 + 76650404 * tM (bitOf T 13) x13 + 100000000 * tM (bitOf T 14) x14 + 44051410 * tM (bitOf T 16) x16 + 23349596 * tM (bitOf T 17) x17 + 33894225 * tM (bitOf T 18) x18 + 0 * tM (bitOf T 19) x19) : ℕ) : ℝ) := by
    have := natsub_ge (71367000000000 + 100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) (100000000 * tM (bitOf T 4) x4 + 200000000 * tM (bitOf T 5) x5 + 0 * tM (bitOf T 9) x9 + 100000000 * tM (bitOf T 10) x10 + 76650404 * tM (bitOf T 13) x13 + 100000000 * tM (bitOf T 14) x14 + 44051410 * tM (bitOf T 16) x16 + 23349596 * tM (bitOf T 17) x17 + 33894225 * tM (bitOf T 18) x18 + 0 * tM (bitOf T 19) x19)
    push_cast at this
    linarith [hdu4, hdu5, hdu9, hdu10, hdu13, hdu14, hdu16, hdu17, hdu18, hdu19]
  have hN4 : -((1000000000 : ℝ) * ((71367 : ℝ) + 100000000 * d4 + 200000000 * d5 + 0 * d9 + 100000000 * d10 + 76650404 * d13 + 100000000 * d14 + 44051410 * d16 + 23349596 * d17 + 33894225 * d18 + 0 * d19)) ≤ (((100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) - (71367000000000 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10 + 76650404 * tP (bitOf T 13) x13 + 100000000 * tP (bitOf T 14) x14 + 44051410 * tP (bitOf T 16) x16 + 23349596 * tP (bitOf T 17) x17 + 33894225 * tP (bitOf T 18) x18 + 0 * tP (bitOf T 19) x19) : ℕ) : ℝ) := by
    have := natsub_ge (100000000 * tK (bitOf T 4) + 200000000 * tK (bitOf T 5) + 0 * tK (bitOf T 9) + 100000000 * tK (bitOf T 10) + 76650404 * tK (bitOf T 13) + 100000000 * tK (bitOf T 14) + 44051410 * tK (bitOf T 16) + 23349596 * tK (bitOf T 17) + 33894225 * tK (bitOf T 18) + 0 * tK (bitOf T 19)) (71367000000000 + 100000000 * tP (bitOf T 4) x4 + 200000000 * tP (bitOf T 5) x5 + 0 * tP (bitOf T 9) x9 + 100000000 * tP (bitOf T 10) x10 + 76650404 * tP (bitOf T 13) x13 + 100000000 * tP (bitOf T 14) x14 + 44051410 * tP (bitOf T 16) x16 + 23349596 * tP (bitOf T 17) x17 + 33894225 * tP (bitOf T 18) x18 + 0 * tP (bitOf T 19) x19)
    push_cast at this
    linarith [hdl4, hdl5, hdl9, hdl10, hdl13, hdl14, hdl16, hdl17, hdl18, hdl19]
  have hml4 : ((q4 - l4 : ℕ) : ℝ) = (q4 : ℝ) - l4 := Nat.cast_sub hq41
  have hum4 : ((u4 - q4 : ℕ) : ℝ) = (u4 : ℝ) - q4 := Nat.cast_sub hq42
  have ht4 := mterm (e := g4 - (q4 : ℝ) / 32768) (E := ((71367 : ℝ) + 100000000 * d4 + 200000000 * d5 + 0 * d9 + 100000000 * d10 + 76650404 * d13 + 100000000 * d14 + 44051410 * d16 + 23349596 * d17 + 33894225 * d18 + 0 * d19)) (lo := ((q4 - l4 : ℕ) : ℝ) / 32768)
    (hi := ((u4 - q4 : ℕ) : ℝ) / 32768) (by rw [hml4]; linarith [h41]) (by rw [hum4]; linarith [h42])
    (by positivity) (by positivity) hP4 hN4 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hP5 : (1000000000 : ℝ) * ((48468 : ℝ) + 200000000 * d5 + 100000000 * d10 + 100000000 * d14 + 23349596 * d17 + 0 * d19 + 24136977 * d20) ≤ (((48468000000000 + 200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) - (200000000 * tM (bitOf T 5) x5 + 100000000 * tM (bitOf T 10) x10 + 100000000 * tM (bitOf T 14) x14 + 23349596 * tM (bitOf T 17) x17 + 0 * tM (bitOf T 19) x19 + 24136977 * tM (bitOf T 20) x20) : ℕ) : ℝ) := by
    have := natsub_ge (48468000000000 + 200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) (200000000 * tM (bitOf T 5) x5 + 100000000 * tM (bitOf T 10) x10 + 100000000 * tM (bitOf T 14) x14 + 23349596 * tM (bitOf T 17) x17 + 0 * tM (bitOf T 19) x19 + 24136977 * tM (bitOf T 20) x20)
    push_cast at this
    linarith [hdu5, hdu10, hdu14, hdu17, hdu19, hdu20]
  have hN5 : -((1000000000 : ℝ) * ((48468 : ℝ) + 200000000 * d5 + 100000000 * d10 + 100000000 * d14 + 23349596 * d17 + 0 * d19 + 24136977 * d20)) ≤ (((200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) - (48468000000000 + 200000000 * tP (bitOf T 5) x5 + 100000000 * tP (bitOf T 10) x10 + 100000000 * tP (bitOf T 14) x14 + 23349596 * tP (bitOf T 17) x17 + 0 * tP (bitOf T 19) x19 + 24136977 * tP (bitOf T 20) x20) : ℕ) : ℝ) := by
    have := natsub_ge (200000000 * tK (bitOf T 5) + 100000000 * tK (bitOf T 10) + 100000000 * tK (bitOf T 14) + 23349596 * tK (bitOf T 17) + 0 * tK (bitOf T 19) + 24136977 * tK (bitOf T 20)) (48468000000000 + 200000000 * tP (bitOf T 5) x5 + 100000000 * tP (bitOf T 10) x10 + 100000000 * tP (bitOf T 14) x14 + 23349596 * tP (bitOf T 17) x17 + 0 * tP (bitOf T 19) x19 + 24136977 * tP (bitOf T 20) x20)
    push_cast at this
    linarith [hdl5, hdl10, hdl14, hdl17, hdl19, hdl20]
  have hml5 : ((q5 - l5 : ℕ) : ℝ) = (q5 : ℝ) - l5 := Nat.cast_sub hq51
  have hum5 : ((u5 - q5 : ℕ) : ℝ) = (u5 : ℝ) - q5 := Nat.cast_sub hq52
  have ht5 := mterm (e := g5 - (q5 : ℝ) / 32768) (E := ((48468 : ℝ) + 200000000 * d5 + 100000000 * d10 + 100000000 * d14 + 23349596 * d17 + 0 * d19 + 24136977 * d20)) (lo := ((q5 - l5 : ℕ) : ℝ) / 32768)
    (hi := ((u5 - q5 : ℕ) : ℝ) / 32768) (by rw [hml5]; linarith [h51]) (by rw [hum5]; linarith [h52])
    (by positivity) (by positivity) hP5 hN5 (natsub_nonneg _ _) (natsub_nonneg _ _)
  have hq := (Nat.cast_le (α := ℝ)).mpr hmain
  push_cast at hq
  try simp only [hml0, hum0, hml1, hum1, hml2, hum2, hml3, hum3, hml4, hum4, hml5, hum5] at hq
  simp only [hml0, hum0, hml1, hum1, hml2, hum2, hml3, hum3, hml4, hum4, hml5, hum5] at ht0 ht1 ht2 ht3 ht4 ht5
  unfold G
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  rw [div_le_iff₀ hSA]
  have eG : ((48468 / (SA:ℝ)) * g0 + (71367 / (SA:ℝ)) * g1 + (82339 / (SA:ℝ)) * g2 + (82339 / (SA:ℝ)) * g3 + (71367 / (SA:ℝ)) * g4 + (48468 / (SA:ℝ)) * g5
      + (24136977 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (23349596 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g1) + (44051410 / (SA:ℝ)) * wfun (g1 + g2) + (76650404 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (0 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g2) + (111897180 / (SA:ℝ)) * wfun (g2 + g3) + (76650404 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (100000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (41968798 / (SA:ℝ)) * wfun (g3) + (44051410 / (SA:ℝ)) * wfun (g3 + g4) + (23349596 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (33894225 / (SA:ℝ)) * wfun (g4) + (0 / (SA:ℝ)) * wfun (g4 + g5) + (24136977 / (SA:ℝ)) * wfun (g5)) * SA
      = 48468 * g0 + 71367 * g1 + 82339 * g2 + 82339 * g3 + 71367 * g4 + 48468 * g5 + 24136977 * wfun (g0) + 0 * wfun (g0 + g1) + 23349596 * wfun (g0 + g1 + g2) + 100000000 * wfun (g0 + g1 + g2 + g3) + 100000000 * wfun (g0 + g1 + g2 + g3 + g4) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4 + g5) + 33894225 * wfun (g1) + 44051410 * wfun (g1 + g2) + 76650404 * wfun (g1 + g2 + g3) + 0 * wfun (g1 + g2 + g3 + g4) + 100000000 * wfun (g1 + g2 + g3 + g4 + g5) + 41968798 * wfun (g2) + 111897180 * wfun (g2 + g3) + 76650404 * wfun (g2 + g3 + g4) + 100000000 * wfun (g2 + g3 + g4 + g5) + 41968798 * wfun (g3) + 44051410 * wfun (g3 + g4) + 23349596 * wfun (g3 + g4 + g5) + 33894225 * wfun (g4) + 0 * wfun (g4 + g5) + 24136977 * wfun (g5) := by
    field_simp; try ring
  rw [eG]
  have hcN : ((cN : ℕ) : ℝ) = 789487 := by norm_num [cN]
  rw [hcN]
  linarith [hq, ht0, ht1, ht2, ht3, ht4, ht5, mul_le_mul_of_nonneg_left hb0 (by norm_num : (0:ℝ) ≤ 24136977), mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb2 (by norm_num : (0:ℝ) ≤ 23349596), mul_le_mul_of_nonneg_left hb3 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb4 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb5 (by norm_num : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left hb6 (by norm_num : (0:ℝ) ≤ 33894225), mul_le_mul_of_nonneg_left hb7 (by norm_num : (0:ℝ) ≤ 44051410), mul_le_mul_of_nonneg_left hb8 (by norm_num : (0:ℝ) ≤ 76650404), mul_le_mul_of_nonneg_left hb9 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb10 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb11 (by norm_num : (0:ℝ) ≤ 41968798), mul_le_mul_of_nonneg_left hb12 (by norm_num : (0:ℝ) ≤ 111897180), mul_le_mul_of_nonneg_left hb13 (by norm_num : (0:ℝ) ≤ 76650404), mul_le_mul_of_nonneg_left hb14 (by norm_num : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left hb15 (by norm_num : (0:ℝ) ≤ 41968798), mul_le_mul_of_nonneg_left hb16 (by norm_num : (0:ℝ) ≤ 44051410), mul_le_mul_of_nonneg_left hb17 (by norm_num : (0:ℝ) ≤ 23349596), mul_le_mul_of_nonneg_left hb18 (by norm_num : (0:ℝ) ≤ 33894225), mul_le_mul_of_nonneg_left hb19 (by norm_num : (0:ℝ) ≤ 0), mul_le_mul_of_nonneg_left hb20 (by norm_num : (0:ℝ) ≤ 24136977)]

/-- the minorant slope test at the point `q` with expansion set `T` and term data `E` -/
def ctestM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T E : ℕ) : Bool :=
  forceB E fun e0 =>
  bforce (bitOf T 0) fun v0 =>
  forceB (lmMX v0 e0 top bk pb tD bD R l0 u0 q0) fun x0 =>
  forceB (mNext v0 e0) fun e1 =>
  bforce (bitOf T 1) fun v1 =>
  forceB (lmMX v1 e1 top bk pb tD bD R (Nat.add l0 l1) (Nat.add u0 u1) (Nat.add q0 q1)) fun x1 =>
  forceB (mNext v1 e1) fun e2 =>
  bforce (bitOf T 2) fun v2 =>
  forceB (lmMX v2 e2 top bk pb tD bD R (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2) (Nat.add (Nat.add q0 q1) q2)) fun x2 =>
  forceB (mNext v2 e2) fun e3 =>
  bforce (bitOf T 3) fun v3 =>
  forceB (lmMX v3 e3 top bk pb tD bD R (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) (Nat.add (Nat.add (Nat.add q0 q1) q2) q3)) fun x3 =>
  forceB (mNext v3 e3) fun e4 =>
  bforce (bitOf T 4) fun v4 =>
  forceB (lmMX v4 e4 top bk pb tD bD R (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4)) fun x4 =>
  forceB (mNext v4 e4) fun e5 =>
  bforce (bitOf T 5) fun v5 =>
  forceB (lmMX v5 e5 top bk pb tD bD R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q0 q1) q2) q3) q4) q5)) fun x5 =>
  forceB (mNext v5 e5) fun e6 =>
  bforce (bitOf T 6) fun v6 =>
  forceB (lmMX v6 e6 top bk pb tD bD R l1 u1 q1) fun x6 =>
  forceB (mNext v6 e6) fun e7 =>
  bforce (bitOf T 7) fun v7 =>
  forceB (lmMX v7 e7 top bk pb tD bD R (Nat.add l1 l2) (Nat.add u1 u2) (Nat.add q1 q2)) fun x7 =>
  forceB (mNext v7 e7) fun e8 =>
  bforce (bitOf T 8) fun v8 =>
  forceB (lmMX v8 e8 top bk pb tD bD R (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3) (Nat.add (Nat.add q1 q2) q3)) fun x8 =>
  forceB (mNext v8 e8) fun e9 =>
  bforce (bitOf T 9) fun v9 =>
  forceB (lmMX v9 e9 top bk pb tD bD R (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) (Nat.add (Nat.add (Nat.add q1 q2) q3) q4)) fun x9 =>
  forceB (mNext v9 e9) fun e10 =>
  bforce (bitOf T 10) fun v10 =>
  forceB (lmMX v10 e10 top bk pb tD bD R (Nat.add (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) l5) (Nat.add (Nat.add (Nat.add (Nat.add u1 u2) u3) u4) u5) (Nat.add (Nat.add (Nat.add (Nat.add q1 q2) q3) q4) q5)) fun x10 =>
  forceB (mNext v10 e10) fun e11 =>
  bforce (bitOf T 11) fun v11 =>
  forceB (lmMX v11 e11 top bk pb tD bD R l2 u2 q2) fun x11 =>
  forceB (mNext v11 e11) fun e12 =>
  bforce (bitOf T 12) fun v12 =>
  forceB (lmMX v12 e12 top bk pb tD bD R (Nat.add l2 l3) (Nat.add u2 u3) (Nat.add q2 q3)) fun x12 =>
  forceB (mNext v12 e12) fun e13 =>
  bforce (bitOf T 13) fun v13 =>
  forceB (lmMX v13 e13 top bk pb tD bD R (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4) (Nat.add (Nat.add q2 q3) q4)) fun x13 =>
  forceB (mNext v13 e13) fun e14 =>
  bforce (bitOf T 14) fun v14 =>
  forceB (lmMX v14 e14 top bk pb tD bD R (Nat.add (Nat.add (Nat.add l2 l3) l4) l5) (Nat.add (Nat.add (Nat.add u2 u3) u4) u5) (Nat.add (Nat.add (Nat.add q2 q3) q4) q5)) fun x14 =>
  forceB (mNext v14 e14) fun e15 =>
  bforce (bitOf T 15) fun v15 =>
  forceB (lmMX v15 e15 top bk pb tD bD R l3 u3 q3) fun x15 =>
  forceB (mNext v15 e15) fun e16 =>
  bforce (bitOf T 16) fun v16 =>
  forceB (lmMX v16 e16 top bk pb tD bD R (Nat.add l3 l4) (Nat.add u3 u4) (Nat.add q3 q4)) fun x16 =>
  forceB (mNext v16 e16) fun e17 =>
  bforce (bitOf T 17) fun v17 =>
  forceB (lmMX v17 e17 top bk pb tD bD R (Nat.add (Nat.add l3 l4) l5) (Nat.add (Nat.add u3 u4) u5) (Nat.add (Nat.add q3 q4) q5)) fun x17 =>
  forceB (mNext v17 e17) fun e18 =>
  bforce (bitOf T 18) fun v18 =>
  forceB (lmMX v18 e18 top bk pb tD bD R l4 u4 q4) fun x18 =>
  forceB (mNext v18 e18) fun e19 =>
  bforce (bitOf T 19) fun v19 =>
  forceB (lmMX v19 e19 top bk pb tD bD R (Nat.add l4 l5) (Nat.add u4 u5) (Nat.add q4 q5)) fun x19 =>
  forceB (mNext v19 e19) fun e20 =>
  bforce (bitOf T 20) fun v20 =>
  forceB (lmMX v20 e20 top bk pb tD bD R l5 u5 q5) fun x20 =>
  cscheck l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T x0 0 0 v0 x1 0 0 v1 x2 0 0 v2 x3 0 0 v3 x4 0 0 v4 x5 0 0 v5 x6 0 0 v6 x7 0 0 v7 x8 0 0 v8 x9 0 0 v9 x10 0 0 v10 x11 0 0 v11 x12 0 0 v12 x13 0 0 v13 x14 0 0 v14 x15 0 0 v15 x16 0 0 v16 x17 0 0 v17 x18 0 0 v18 x19 0 0 v19 x20 0 0 v20

theorem ctestM_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T E : ℕ) (h : ctestM top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T E = true) :
    ∀ g0 g1 g2 g3 g4 g5 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (l5 : ℝ) / SC ≤ g5 → g5 ≤ (u5 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 g5 := by
  unfold ctestM at h
  simp only [forceB_eq, bforce_eq] at h
  exact cscheck_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2) (fun hok s h1 h2 => minterm_bound hlb hD hpt hR _ _ _ _ _ _ _ hok s h1 h2)

theorem covered_of_ctestM {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true)
    (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (q0 q1 q2 q3 q4 q5 : ℕ) (T E : ℕ) (h : ctestM top bk tD bD pb R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T E = true) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
  exact Or.inl (ctestM_sound hlb hD hpt hR l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T E h g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)

/-- a minorant leaf: `dec` modes (bits 3..14), the all-expanded flag (bit 15) or the expansion set (bits 16..36),
then the term data `E` (from bit 16 when the flag is set, else from bit 37) -/
def sleafM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : Bool :=
  forceB (dec (Nat.land (Nat.shiftRight w 3) 3) l0 u0) fun q0 =>
  forceB (dec (Nat.land (Nat.shiftRight w 5) 3) l1 u1) fun q1 =>
  forceB (dec (Nat.land (Nat.shiftRight w 7) 3) l2 u2) fun q2 =>
  forceB (dec (Nat.land (Nat.shiftRight w 9) 3) l3 u3) fun q3 =>
  forceB (dec (Nat.land (Nat.shiftRight w 11) 3) l4 u4) fun q4 =>
  forceB (dec (Nat.land (Nat.shiftRight w 13) 3) l5 u5) fun q5 =>
  forceB (Nat.land (Nat.shiftRight w 15) 1) fun F =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight w 16) 2097151) 2097151 (Nat.beq F 1)) fun T =>
  forceB (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight w 37) (Nat.shiftRight w 16) (Nat.beq F 1)) fun E =>
  ctestM top bk tD bD (pt3 pb) R l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 q0 q1 q2 q3 q4 q5 T E

theorem covered_of_sleafM {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true)
    (w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) (h : sleafM top bk tD bD pb R w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = true) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold sleafM at h
  simp only [forceB_eq] at h
  exact covered_of_ctestM (pb := pt3 pb) hlb hD hpt hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-! ### the walk with minorant leaves

A leaf record (bit 0 clear): bits 1..2 the kind.  Kind 0: zero order (length 3).  Kind 1: slope (`sleaf`, length 16 or
37).  Kind 3: centre (`cleaf`, length 12 or 33).  Kind 2: bit 3 clear, a basin (length 4); bit 3 set, a minorant leaf
whose record length is bits 4..12 and whose `sleafM` word is the record shifted by 10 (its `dec` modes at bits 13..24,
flag at bit 25, then `T` unless flagged, then the term data). -/

/-- a leaf of the walk with minorant leaves: the next position, or `0` -/
def leafStepM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) 0
            (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 33) (Nat.add pos 12) (Nat.beq (Nat.land (Nat.shiftRight w 11) 1) 1))
            (cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5))
          (Bool.rec (motive := fun _ => ℕ)
            (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add pos 4) (inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5))
            (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add pos (Nat.land (Nat.shiftRight w 4) 511))
              (sleafM top bk tD bD pb R (Nat.shiftRight w 10) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5))
            (Nat.beq (Nat.land (Nat.shiftRight w 3) 1) 1))
          (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 2))
        (Bool.rec (motive := fun _ => ℕ) 0
          (Bool.rec (motive := fun _ => ℕ) (Nat.add pos 37) (Nat.add pos 16) (Nat.beq (Nat.land (Nat.shiftRight w 15) 1) 1))
          (sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5))
        (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 1))
      (Bool.rec (motive := fun _ => ℕ) 0 (Nat.add pos 3) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5))
      (Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 0))
    (Nat.add pos 3) (Nat.ble (Nat.add u5 1) l0)

/-- the bisection walk with minorant leaves (`Nat.rec` on the fuel): the node word is `bits >>> pos` -/
def walkM (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (C : ℕ) (bas : List Bx) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 =>
      let w := Nat.shiftRight bits pos
      Bool.rec (motive := fun _ => ℕ) (leafStepM top bk tD bD pb R C bas pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (splitAx ih pos (Nat.land (Nat.shiftRight w 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5) (Nat.beq (Nat.land w 1) 1))
    fuel

theorem leafStepM_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 : ℕ)
    (h : leafStepM top bk tD bD pb R C bas pos w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 := by
  unfold leafStepM at h
  cases hs : Nat.ble (Nat.add u5 1) l0
  · rw [hs] at h
    cases hk0 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 0
    · rw [hk0] at h
      cases hk1 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 1
      · rw [hk1] at h
        cases hk2 : Nat.beq (Nat.land (Nat.shiftRight w 1) 3) 2
        · rw [hk2] at h
          cases hl : cleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
          · rw [hl] at h; exact absurd rfl h
          · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
            exact Or.inl (cleaf_sound hlb hD hpt hR w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
        · rw [hk2] at h
          cases hm : Nat.beq (Nat.land (Nat.shiftRight w 3) 1) 1
          · rw [hm] at h
            cases hl : inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
            · rw [hl] at h; exact absurd rfl h
            · exact inBas_sound hbas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl
          · rw [hm] at h
            cases hl : sleafM top bk tD bD pb R (Nat.shiftRight w 10) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
            · rw [hl] at h; exact absurd rfl h
            · exact covered_of_sleafM hlb hD hpt hR _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl
      · rw [hk1] at h
        cases hl : sleaf top bk tD bD pb R C w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
        · rw [hl] at h; exact absurd rfl h
        · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
          exact Or.inl (sleaf_sound hlb hD hpt hR w l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
    · rw [hk0] at h
      cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5
      · rw [hl] at h; exact absurd rfl h
      · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
        exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 hl g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52)
  · intro g0 g1 g2 g3 g4 g5 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42 h51 h52
    right
    have hsk : u5 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u5 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walkM_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (bits : ℕ) :
    ∀ fuel, WalkOK (walkM top bk tD bD pb R C bas bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStepM top bk tD bD pb R C bas pos (Nat.shiftRight bits pos) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (splitAx (walkM top bk tD bD pb R C bas bits fuel) pos (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 7) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5)
        (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1
    · rw [hb] at h'; exact leafStepM_sound hlb hD hpt hR hbas pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 h'

/-- **a box is covered when the walk with minorant leaves reaches its end** -/
theorem covered_of_walkM {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} {C : ℕ} (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PT3Sound pb) (hR : rgOk R = true) {bas : List Bx} (hbas : BasOK bas) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 e : ℕ)
    (h : walkM top bk tD bD pb R C bas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 :=
  walkM_sound hlb hD hpt hR hbas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 (h ▸ he)

end AMW.Cert.AMS02

end
