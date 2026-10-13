import TimeLever
open AMW.Min AMW.G
-- one minorant leaf, slope lines through the left end (valOk at the left end + w′ chain)
set_option maxRecDepth 100000 in
example : minCheck 7 aQ (fun i j => -1 + 100 * boxSumQ 6 loQ i j) (fun _ _ => -100) bQ loQ hiQ (-1000)
    (lineOkA 512) = true := by decide +kernel
