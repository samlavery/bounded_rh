import TimeLever
open AMW.Min AMW.G
-- 21 point cells (K0 only)
set_option maxRecDepth 100000 in
example : (List.range 21).all (fun t => valOkA (1 + (t : ℚ) / 32768) (-1)) = true := by decide +kernel
