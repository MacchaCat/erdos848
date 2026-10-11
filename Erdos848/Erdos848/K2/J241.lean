import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv241_c0 : below iv241.lo (caseIbQ (lookDT treeK) strsAll iv241.hi (iv241.p.getD 0 dPrm) (iv241.d.getD 0 [])) = true := by
  decide +kernel

theorem iv241_c1 : below iv241.lo (caseIIQ (lookDT treeK) admPre strsAll iv241.hi (iv241.p.getD 1 dPrm) (iv241.d.getD 1 [])) = true := by
  decide +kernel

theorem iv241_c2 : below iv241.lo (caseIII1Q (lookDT treeK) admPre strsAll iv241.hi (iv241.p.getD 2 dPrm) (iv241.d.getD 2 [])) = true := by
  decide +kernel

theorem iv241_c3 : below iv241.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv241.hi (iv241.p.getD 3 dPrm) (iv241.d.getD 3 [])) = true := by
  decide +kernel

theorem iv241_c4 : below iv241.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv241.hi (iv241.p.getD 4 dPrm) (iv241.d.getD 4 []) (iv241.d.getD 5 [])) = true := by
  decide +kernel

theorem iv241_ok : checkIv2 (lookDT treeK) admPre strsAll iv241 = true :=
  checkIv2_of_cases _ _ _ iv241 rfl rfl (by decide +kernel) iv241_c0 iv241_c1 iv241_c2 iv241_c3 iv241_c4

end ErdosComp
