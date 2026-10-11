import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv121_c0 : below iv121.lo (caseIbQ (lookDT treeK) strsAll iv121.hi (iv121.p.getD 0 dPrm) (iv121.d.getD 0 [])) = true := by
  decide +kernel

theorem iv121_c1 : below iv121.lo (caseIIQ (lookDT treeK) admPre strsAll iv121.hi (iv121.p.getD 1 dPrm) (iv121.d.getD 1 [])) = true := by
  decide +kernel

theorem iv121_c2 : below iv121.lo (caseIII1Q (lookDT treeK) admPre strsAll iv121.hi (iv121.p.getD 2 dPrm) (iv121.d.getD 2 [])) = true := by
  decide +kernel

theorem iv121_c3 : below iv121.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv121.hi (iv121.p.getD 3 dPrm) (iv121.d.getD 3 [])) = true := by
  decide +kernel

theorem iv121_c4 : below iv121.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv121.hi (iv121.p.getD 4 dPrm) (iv121.d.getD 4 []) (iv121.d.getD 5 [])) = true := by
  decide +kernel

theorem iv121_ok : checkIv2 (lookDT treeK) admPre strsAll iv121 = true :=
  checkIv2_of_cases _ _ _ iv121 rfl rfl (by decide +kernel) iv121_c0 iv121_c1 iv121_c2 iv121_c3 iv121_c4

end ErdosComp
