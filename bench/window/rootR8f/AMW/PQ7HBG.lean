import AMW.PQ7HBInst

/-! mvt-engine's golden boundary cuts (DATA_try2cb_0.00005.json, walk 0) and edge cases, on PQ7HB's `BND` -/

open AMW.Cert.PCell AMW.Cert.PQ7HB

example : bcutL BND 64 88576 130560 = 106176 := by decide
example : bcutL BND 64 118272 149184 = 138560 := by decide
example : bcutL BND 64 147456 183104 = 171456 := by decide
example : bcutL BND 64 145408 1056064 = 524288 := by decide
example : bcutL BND 64 115712 312832 = 220224 := by decide
example : bcutL BND 64 174592 1088960 = 524288 := by decide
example : bcutL BND 64 201728 655936 = 434048 := by decide
example : bcutL BND 64 145408 377728 = 269440 := by decide
example : bcutL BND 64 40000 40500 = 40384 := by decide
example : bcutL BND 64 40320 40448 = 40384 := by decide
example : bcutL BND 64 40320 40447 = 40383 := by decide
example : bcutL BND 64 30000 60000 = 40384 := by decide
example : bcutL BND 64 56700 74000 = 73664 := by decide
