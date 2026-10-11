import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv148_c0 : below iv148.lo (caseIbQ (lookDT treeK) strsAll iv148.hi (iv148.p.getD 0 dPrm) (iv148.d.getD 0 [])) = true := by
  decide +kernel

theorem iv148_c1 : below iv148.lo (caseIIQ (lookDT treeK) admPre strsAll iv148.hi (iv148.p.getD 1 dPrm) (iv148.d.getD 1 [])) = true := by
  decide +kernel

theorem iv148_c2 : below iv148.lo (caseIII1Q (lookDT treeK) admPre strsAll iv148.hi (iv148.p.getD 2 dPrm) (iv148.d.getD 2 [])) = true := by
  decide +kernel

theorem iv148_c3 : below iv148.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv148.hi (iv148.p.getD 3 dPrm) (iv148.d.getD 3 [])) = true := by
  decide +kernel

theorem iv148_c4 : below iv148.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv148.hi (iv148.p.getD 4 dPrm) (iv148.d.getD 4 []) (iv148.d.getD 5 [])) = true := by
  decide +kernel

theorem iv148_ok : checkIv2 (lookDT treeK) admPre strsAll iv148 = true :=
  checkIv2_of_cases _ _ _ iv148 rfl rfl (by decide +kernel) iv148_c0 iv148_c1 iv148_c2 iv148_c3 iv148_c4

end ErdosComp
