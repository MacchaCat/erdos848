import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv237_c0 : below iv237.lo (caseIbQ (lookDT treeK) strsAll iv237.hi (iv237.p.getD 0 dPrm) (iv237.d.getD 0 [])) = true := by
  decide +kernel

theorem iv237_c1 : below iv237.lo (caseIIQ (lookDT treeK) admPre strsAll iv237.hi (iv237.p.getD 1 dPrm) (iv237.d.getD 1 [])) = true := by
  decide +kernel

theorem iv237_c2 : below iv237.lo (caseIII1Q (lookDT treeK) admPre strsAll iv237.hi (iv237.p.getD 2 dPrm) (iv237.d.getD 2 [])) = true := by
  decide +kernel

theorem iv237_c3 : below iv237.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv237.hi (iv237.p.getD 3 dPrm) (iv237.d.getD 3 [])) = true := by
  decide +kernel

theorem iv237_c4 : below iv237.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv237.hi (iv237.p.getD 4 dPrm) (iv237.d.getD 4 []) (iv237.d.getD 5 [])) = true := by
  decide +kernel

theorem iv237_ok : checkIv2 (lookDT treeK) admPre strsAll iv237 = true :=
  checkIv2_of_cases _ _ _ iv237 rfl rfl (by decide +kernel) iv237_c0 iv237_c1 iv237_c2 iv237_c3 iv237_c4

end ErdosComp
