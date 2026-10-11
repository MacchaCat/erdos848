import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv11_c0 : below iv11.lo (caseIbQ (lookDT treeK) strsAll iv11.hi (iv11.p.getD 0 dPrm) (iv11.d.getD 0 [])) = true := by
  decide +kernel

theorem iv11_c1 : below iv11.lo (caseIIQ (lookDT treeK) admPre strsAll iv11.hi (iv11.p.getD 1 dPrm) (iv11.d.getD 1 [])) = true := by
  decide +kernel

theorem iv11_c2 : below iv11.lo (caseIII1Q (lookDT treeK) admPre strsAll iv11.hi (iv11.p.getD 2 dPrm) (iv11.d.getD 2 [])) = true := by
  decide +kernel

theorem iv11_c3 : below iv11.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv11.hi (iv11.p.getD 3 dPrm) (iv11.d.getD 3 [])) = true := by
  decide +kernel

theorem iv11_c4 : below iv11.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv11.hi (iv11.p.getD 4 dPrm) (iv11.d.getD 4 []) (iv11.d.getD 5 [])) = true := by
  decide +kernel

theorem iv11_ok : checkIv2 (lookDT treeK) admPre strsAll iv11 = true :=
  checkIv2_of_cases _ _ _ iv11 rfl rfl (by decide +kernel) iv11_c0 iv11_c1 iv11_c2 iv11_c3 iv11_c4

end ErdosComp
