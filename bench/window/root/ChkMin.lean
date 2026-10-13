import AMW.PSDBasin
open AMW.Min
#print axioms minCheck_sound
#print axioms basinCheck_sound
#check @minCheck_sound
#check @basinCheck_sound
-- kernel evaluation speed, n = 7, dummy oracles
def aT : ℕ → ℕ → ℚ := fun i j => ((i + 2 * j + 1 : ℕ) : ℚ) / 10
set_option maxRecDepth 10000 in
example : minCheck 7 aT (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1/100) (fun _ => 1) (fun _ => 2) (-100)
    (fun _ _ _ _ => true) = true := by decide +kernel
set_option maxRecDepth 10000 in
example : basinCheck 7 aT (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 1) (fun _ => 1/100)
    (fun _ => 1) (fun _ => 2) (fun _ => 3/2) (-1000) (fun _ _ _ => true) (fun _ _ => true) (fun _ _ _ => true) = true := by
  decide +kernel
