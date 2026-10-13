import TimeLever
open AMW.Min AMW.G
set_option maxRecDepth 100000 in
example : basinCheck 7 aQ (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => -100) (fun _ _ => 100) bQ loQ hiQ qQ (-1000)
    (fun _ _ _ => true) (fun _ _ => true) (fun _ _ _ => true) (psdN 6) = true := by decide +kernel
