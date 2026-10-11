import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv4_c0 : below iv4.lo (caseIbQ (lookDT treeK) strsAll iv4.hi (iv4.p.getD 0 dPrm) (iv4.d.getD 0 [])) = true := by
  decide +kernel

theorem iv4_c1 : below iv4.lo (caseIIQ (lookDT treeK) admPre strsAll iv4.hi (iv4.p.getD 1 dPrm) (iv4.d.getD 1 [])) = true := by
  decide +kernel

theorem iv4_c2 : below iv4.lo (caseIII1Q (lookDT treeK) admPre strsAll iv4.hi (iv4.p.getD 2 dPrm) (iv4.d.getD 2 [])) = true := by
  decide +kernel

theorem iv4_c3 : below iv4.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv4.hi (iv4.p.getD 3 dPrm) (iv4.d.getD 3 [])) = true := by
  decide +kernel

theorem iv4_c4 : below iv4.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv4.hi (iv4.p.getD 4 dPrm) (iv4.d.getD 4 []) (iv4.d.getD 5 [])) = true := by
  decide +kernel

theorem iv4_ok : checkIv2 (lookDT treeK) admPre strsAll iv4 = true :=
  checkIv2_of_cases _ _ _ iv4 rfl rfl (by decide +kernel) iv4_c0 iv4_c1 iv4_c2 iv4_c3 iv4_c4

end ErdosComp
