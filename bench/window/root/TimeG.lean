import TimeLever
open AMW.Min AMW.G
-- 21 point cells (K0 and K1)
set_option maxRecDepth 100000 in
example : (List.range 21).all (fun t => d1OkA (1 + (t : ℚ) / 32768) (-100) 100) = true := by decide +kernel
