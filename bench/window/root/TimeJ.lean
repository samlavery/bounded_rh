import TimeLever
open AMW.Min AMW.G
set_option maxRecDepth 100000 in
example : (List.range 6).all (fun r => (List.range 6).all (fun r' => decide (0 ≤ pairMatQ 7 aQ r r'))) = true := by decide +kernel
