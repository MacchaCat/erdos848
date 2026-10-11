import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv194_c0 : below iv194.lo (caseIbQ (lookDT treeK) strsAll iv194.hi (iv194.p.getD 0 dPrm) (iv194.d.getD 0 [])) = true := by
  decide +kernel

theorem iv194_c1 : below iv194.lo (caseIIQ (lookDT treeK) admPre strsAll iv194.hi (iv194.p.getD 1 dPrm) (iv194.d.getD 1 [])) = true := by
  decide +kernel

theorem iv194_c2 : below iv194.lo (caseIII1Q (lookDT treeK) admPre strsAll iv194.hi (iv194.p.getD 2 dPrm) (iv194.d.getD 2 [])) = true := by
  decide +kernel

theorem iv194_c3 : below iv194.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv194.hi (iv194.p.getD 3 dPrm) (iv194.d.getD 3 [])) = true := by
  decide +kernel

theorem iv194_c4 : below iv194.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv194.hi (iv194.p.getD 4 dPrm) (iv194.d.getD 4 []) (iv194.d.getD 5 [])) = true := by
  decide +kernel

theorem iv194_ok : checkIv2 (lookDT treeK) admPre strsAll iv194 = true :=
  checkIv2_of_cases _ _ _ iv194 rfl rfl (by decide +kernel) iv194_c0 iv194_c1 iv194_c2 iv194_c3 iv194_c4

end ErdosComp
