import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv74_c0 : below iv74.lo (caseIbQ (lookDT treeK) strsAll iv74.hi (iv74.p.getD 0 dPrm) (iv74.d.getD 0 [])) = true := by
  decide +kernel

theorem iv74_c1 : below iv74.lo (caseIIQ (lookDT treeK) admPre strsAll iv74.hi (iv74.p.getD 1 dPrm) (iv74.d.getD 1 [])) = true := by
  decide +kernel

theorem iv74_c2 : below iv74.lo (caseIII1Q (lookDT treeK) admPre strsAll iv74.hi (iv74.p.getD 2 dPrm) (iv74.d.getD 2 [])) = true := by
  decide +kernel

theorem iv74_c3 : below iv74.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv74.hi (iv74.p.getD 3 dPrm) (iv74.d.getD 3 [])) = true := by
  decide +kernel

theorem iv74_c4 : below iv74.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv74.hi (iv74.p.getD 4 dPrm) (iv74.d.getD 4 []) (iv74.d.getD 5 [])) = true := by
  decide +kernel

theorem iv74_ok : checkIv2 (lookDT treeK) admPre strsAll iv74 = true :=
  checkIv2_of_cases _ _ _ iv74 rfl rfl (by decide +kernel) iv74_c0 iv74_c1 iv74_c2 iv74_c3 iv74_c4

end ErdosComp
