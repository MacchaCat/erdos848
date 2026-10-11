import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv333_c0 : below iv333.lo (caseIbQ (lookDT treeK) strsAll iv333.hi (iv333.p.getD 0 dPrm) (iv333.d.getD 0 [])) = true := by
  decide +kernel

theorem iv333_c1 : below iv333.lo (caseIIQ (lookDT treeK) admPre strsAll iv333.hi (iv333.p.getD 1 dPrm) (iv333.d.getD 1 [])) = true := by
  decide +kernel

theorem iv333_c2 : below iv333.lo (caseIII1Q (lookDT treeK) admPre strsAll iv333.hi (iv333.p.getD 2 dPrm) (iv333.d.getD 2 [])) = true := by
  decide +kernel

theorem iv333_c3 : below iv333.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv333.hi (iv333.p.getD 3 dPrm) (iv333.d.getD 3 [])) = true := by
  decide +kernel

theorem iv333_c4 : below iv333.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv333.hi (iv333.p.getD 4 dPrm) (iv333.d.getD 4 []) (iv333.d.getD 5 [])) = true := by
  decide +kernel

theorem iv333_ok : checkIv2 (lookDT treeK) admPre strsAll iv333 = true :=
  checkIv2_of_cases _ _ _ iv333 rfl rfl (by decide +kernel) iv333_c0 iv333_c1 iv333_c2 iv333_c3 iv333_c4

end ErdosComp
