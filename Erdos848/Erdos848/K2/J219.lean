import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv219_c0 : below iv219.lo (caseIbQ (lookDT treeK) strsAll iv219.hi (iv219.p.getD 0 dPrm) (iv219.d.getD 0 [])) = true := by
  decide +kernel

theorem iv219_c1 : below iv219.lo (caseIIQ (lookDT treeK) admPre strsAll iv219.hi (iv219.p.getD 1 dPrm) (iv219.d.getD 1 [])) = true := by
  decide +kernel

theorem iv219_c2 : below iv219.lo (caseIII1Q (lookDT treeK) admPre strsAll iv219.hi (iv219.p.getD 2 dPrm) (iv219.d.getD 2 [])) = true := by
  decide +kernel

theorem iv219_c3 : below iv219.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv219.hi (iv219.p.getD 3 dPrm) (iv219.d.getD 3 [])) = true := by
  decide +kernel

theorem iv219_c4 : below iv219.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv219.hi (iv219.p.getD 4 dPrm) (iv219.d.getD 4 []) (iv219.d.getD 5 [])) = true := by
  decide +kernel

theorem iv219_ok : checkIv2 (lookDT treeK) admPre strsAll iv219 = true :=
  checkIv2_of_cases _ _ _ iv219 rfl rfl (by decide +kernel) iv219_c0 iv219_c1 iv219_c2 iv219_c3 iv219_c4

end ErdosComp
