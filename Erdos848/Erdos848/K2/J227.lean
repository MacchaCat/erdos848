import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv227_c0 : below iv227.lo (caseIbQ (lookDT treeK) strsAll iv227.hi (iv227.p.getD 0 dPrm) (iv227.d.getD 0 [])) = true := by
  decide +kernel

theorem iv227_c1 : below iv227.lo (caseIIQ (lookDT treeK) admPre strsAll iv227.hi (iv227.p.getD 1 dPrm) (iv227.d.getD 1 [])) = true := by
  decide +kernel

theorem iv227_c2 : below iv227.lo (caseIII1Q (lookDT treeK) admPre strsAll iv227.hi (iv227.p.getD 2 dPrm) (iv227.d.getD 2 [])) = true := by
  decide +kernel

theorem iv227_c3 : below iv227.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv227.hi (iv227.p.getD 3 dPrm) (iv227.d.getD 3 [])) = true := by
  decide +kernel

theorem iv227_c4 : below iv227.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv227.hi (iv227.p.getD 4 dPrm) (iv227.d.getD 4 []) (iv227.d.getD 5 [])) = true := by
  decide +kernel

theorem iv227_ok : checkIv2 (lookDT treeK) admPre strsAll iv227 = true :=
  checkIv2_of_cases _ _ _ iv227 rfl rfl (by decide +kernel) iv227_c0 iv227_c1 iv227_c2 iv227_c3 iv227_c4

end ErdosComp
