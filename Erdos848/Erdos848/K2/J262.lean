import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv262_c0 : below iv262.lo (caseIbQ (lookDT treeK) strsAll iv262.hi (iv262.p.getD 0 dPrm) (iv262.d.getD 0 [])) = true := by
  decide +kernel

theorem iv262_c1 : below iv262.lo (caseIIQ (lookDT treeK) admPre strsAll iv262.hi (iv262.p.getD 1 dPrm) (iv262.d.getD 1 [])) = true := by
  decide +kernel

theorem iv262_c2 : below iv262.lo (caseIII1Q (lookDT treeK) admPre strsAll iv262.hi (iv262.p.getD 2 dPrm) (iv262.d.getD 2 [])) = true := by
  decide +kernel

theorem iv262_c3 : below iv262.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv262.hi (iv262.p.getD 3 dPrm) (iv262.d.getD 3 [])) = true := by
  decide +kernel

theorem iv262_c4 : below iv262.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv262.hi (iv262.p.getD 4 dPrm) (iv262.d.getD 4 []) (iv262.d.getD 5 [])) = true := by
  decide +kernel

theorem iv262_ok : checkIv2 (lookDT treeK) admPre strsAll iv262 = true :=
  checkIv2_of_cases _ _ _ iv262 rfl rfl (by decide +kernel) iv262_c0 iv262_c1 iv262_c2 iv262_c3 iv262_c4

end ErdosComp
