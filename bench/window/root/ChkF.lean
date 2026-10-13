import AMW.BrC
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
example : wfun = AMW.wfunAM := rfl
example : kfun = AMW.kfunAM := rfl
#print axioms tail_passage
#print axioms kernel_limit
#print axioms deleted_strips
#print axioms endgame_defect
#print axioms gram_close_of
#print axioms n_point_bound_w'
#check @n_point_bound_w'
#check @Phi_w'
