import AMW.PSDBasin
open AMW.Min
example : psdN 6 (pairMatQ 7 (fun i j => ((i + 2 * j + 1 : ℕ) : ℚ) / 7)) = true := by decide +kernel
