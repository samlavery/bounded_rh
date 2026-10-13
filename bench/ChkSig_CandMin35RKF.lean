-- statement probe for module CandMin35RKF (lean_minify.py validation)
import CandMin35RKF
#check @candidate_strict_improvement
set_option pp.all true in
#check @candidate_strict_improvement
#check @candidate_critical_line_bound
set_option pp.all true in
#check @candidate_critical_line_bound
#check @candidate_critical_line_bound_cumulative
set_option pp.all true in
#check @candidate_critical_line_bound_cumulative
#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
