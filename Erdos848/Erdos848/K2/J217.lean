import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv217_c0 : below iv217.lo (caseIbQ (lookDT treeK) strsAll iv217.hi (iv217.p.getD 0 dPrm) (iv217.d.getD 0 [])) = true := by
  decide +kernel

theorem iv217_c1 : below iv217.lo (caseIIQ (lookDT treeK) admPre strsAll iv217.hi (iv217.p.getD 1 dPrm) (iv217.d.getD 1 [])) = true := by
  decide +kernel

theorem iv217_c2 : below iv217.lo (caseIII1Q (lookDT treeK) admPre strsAll iv217.hi (iv217.p.getD 2 dPrm) (iv217.d.getD 2 [])) = true := by
  decide +kernel

theorem iv217_c3 : below iv217.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv217.hi (iv217.p.getD 3 dPrm) (iv217.d.getD 3 [])) = true := by
  decide +kernel

theorem iv217_c4 : below iv217.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv217.hi (iv217.p.getD 4 dPrm) (iv217.d.getD 4 []) (iv217.d.getD 5 [])) = true := by
  decide +kernel

theorem iv217_ok : checkIv2 (lookDT treeK) admPre strsAll iv217 = true :=
  checkIv2_of_cases _ _ _ iv217 rfl rfl (by decide +kernel) iv217_c0 iv217_c1 iv217_c2 iv217_c3 iv217_c4

end ErdosComp
