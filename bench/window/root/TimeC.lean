import TimeLever
open AMW.Min AMW.G
-- one minorant leaf, constant lines (K0 chain only)
set_option maxRecDepth 100000 in
example : minCheck 7 aQ (fun _ _ => -1) (fun _ _ => 0) bQ loQ hiQ (-1000) (lineOkA 512) = true := by decide +kernel
