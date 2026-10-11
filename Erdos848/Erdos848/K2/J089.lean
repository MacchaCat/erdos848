import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv89_c0 : below iv89.lo (caseIbQ (lookDT treeK) strsAll iv89.hi (iv89.p.getD 0 dPrm) (iv89.d.getD 0 [])) = true := by
  decide +kernel

theorem iv89_c1 : below iv89.lo (caseIIQ (lookDT treeK) admPre strsAll iv89.hi (iv89.p.getD 1 dPrm) (iv89.d.getD 1 [])) = true := by
  decide +kernel

theorem iv89_c2 : below iv89.lo (caseIII1Q (lookDT treeK) admPre strsAll iv89.hi (iv89.p.getD 2 dPrm) (iv89.d.getD 2 [])) = true := by
  decide +kernel

theorem iv89_c3 : below iv89.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv89.hi (iv89.p.getD 3 dPrm) (iv89.d.getD 3 [])) = true := by
  decide +kernel

theorem iv89_c4 : below iv89.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv89.hi (iv89.p.getD 4 dPrm) (iv89.d.getD 4 []) (iv89.d.getD 5 [])) = true := by
  decide +kernel

theorem iv89_ok : checkIv2 (lookDT treeK) admPre strsAll iv89 = true :=
  checkIv2_of_cases _ _ _ iv89 rfl rfl (by decide +kernel) iv89_c0 iv89_c1 iv89_c2 iv89_c3 iv89_c4

end ErdosComp
