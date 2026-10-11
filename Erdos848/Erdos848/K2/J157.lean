import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv157_c0 : below iv157.lo (caseIbQ (lookDT treeK) strsAll iv157.hi (iv157.p.getD 0 dPrm) (iv157.d.getD 0 [])) = true := by
  decide +kernel

theorem iv157_c1 : below iv157.lo (caseIIQ (lookDT treeK) admPre strsAll iv157.hi (iv157.p.getD 1 dPrm) (iv157.d.getD 1 [])) = true := by
  decide +kernel

theorem iv157_c2 : below iv157.lo (caseIII1Q (lookDT treeK) admPre strsAll iv157.hi (iv157.p.getD 2 dPrm) (iv157.d.getD 2 [])) = true := by
  decide +kernel

theorem iv157_c3 : below iv157.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv157.hi (iv157.p.getD 3 dPrm) (iv157.d.getD 3 [])) = true := by
  decide +kernel

theorem iv157_c4 : below iv157.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv157.hi (iv157.p.getD 4 dPrm) (iv157.d.getD 4 []) (iv157.d.getD 5 [])) = true := by
  decide +kernel

theorem iv157_ok : checkIv2 (lookDT treeK) admPre strsAll iv157 = true :=
  checkIv2_of_cases _ _ _ iv157 rfl rfl (by decide +kernel) iv157_c0 iv157_c1 iv157_c2 iv157_c3 iv157_c4

end ErdosComp
