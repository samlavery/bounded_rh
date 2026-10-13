import TimeLever
open AMW.Min AMW.G
set_option maxRecDepth 100000 in
example : basinCheck 7 aQ (fun _ _ => -1000) (fun _ _ => -1) (fun _ _ => -100) (fun _ _ => 100) bQ loQ hiQ qQ (-1000)
    (w2OkA 512) valOkA d1OkA (psdN 6) = false := by decide +kernel
