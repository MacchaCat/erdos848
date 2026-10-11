import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv336_c0 : below iv336.lo (caseIbQ (lookDT treeK) strsAll iv336.hi (iv336.p.getD 0 dPrm) (iv336.d.getD 0 [])) = true := by
  decide +kernel

theorem iv336_c1 : below iv336.lo (caseIIQ (lookDT treeK) admPre strsAll iv336.hi (iv336.p.getD 1 dPrm) (iv336.d.getD 1 [])) = true := by
  decide +kernel

theorem iv336_c2 : below iv336.lo (caseIII1Q (lookDT treeK) admPre strsAll iv336.hi (iv336.p.getD 2 dPrm) (iv336.d.getD 2 [])) = true := by
  decide +kernel

theorem iv336_c3 : below iv336.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv336.hi (iv336.p.getD 3 dPrm) (iv336.d.getD 3 [])) = true := by
  decide +kernel

theorem iv336_c4 : below iv336.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv336.hi (iv336.p.getD 4 dPrm) (iv336.d.getD 4 []) (iv336.d.getD 5 [])) = true := by
  decide +kernel

theorem iv336_ok : checkIv2 (lookDT treeK) admPre strsAll iv336 = true :=
  checkIv2_of_cases _ _ _ iv336 rfl rfl (by decide +kernel) iv336_c0 iv336_c1 iv336_c2 iv336_c3 iv336_c4

end ErdosComp
