import TimeLever
open AMW.Min AMW.G
set_option maxRecDepth 100000 in
example : minCheck 7 aQ (fun _ _ => -1) (fun _ _ => 0) bQ loQ hiQ (-1000) (fun _ _ _ _ => true) = true := by decide +kernel
