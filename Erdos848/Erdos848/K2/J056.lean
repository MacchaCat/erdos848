import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv56_c0 : below iv56.lo (caseIbQ (lookDT treeK) strsAll iv56.hi (iv56.p.getD 0 dPrm) (iv56.d.getD 0 [])) = true := by
  decide +kernel

theorem iv56_c1 : below iv56.lo (caseIIQ (lookDT treeK) admPre strsAll iv56.hi (iv56.p.getD 1 dPrm) (iv56.d.getD 1 [])) = true := by
  decide +kernel

theorem iv56_c2 : below iv56.lo (caseIII1Q (lookDT treeK) admPre strsAll iv56.hi (iv56.p.getD 2 dPrm) (iv56.d.getD 2 [])) = true := by
  decide +kernel

theorem iv56_c3 : below iv56.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv56.hi (iv56.p.getD 3 dPrm) (iv56.d.getD 3 [])) = true := by
  decide +kernel

theorem iv56_c4 : below iv56.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv56.hi (iv56.p.getD 4 dPrm) (iv56.d.getD 4 []) (iv56.d.getD 5 [])) = true := by
  decide +kernel

theorem iv56_ok : checkIv2 (lookDT treeK) admPre strsAll iv56 = true :=
  checkIv2_of_cases _ _ _ iv56 rfl rfl (by decide +kernel) iv56_c0 iv56_c1 iv56_c2 iv56_c3 iv56_c4

end ErdosComp
