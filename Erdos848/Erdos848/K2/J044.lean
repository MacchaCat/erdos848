import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv44_c0 : below iv44.lo (caseIbQ (lookDT treeK) strsAll iv44.hi (iv44.p.getD 0 dPrm) (iv44.d.getD 0 [])) = true := by
  decide +kernel

theorem iv44_c1 : below iv44.lo (caseIIQ (lookDT treeK) admPre strsAll iv44.hi (iv44.p.getD 1 dPrm) (iv44.d.getD 1 [])) = true := by
  decide +kernel

theorem iv44_c2 : below iv44.lo (caseIII1Q (lookDT treeK) admPre strsAll iv44.hi (iv44.p.getD 2 dPrm) (iv44.d.getD 2 [])) = true := by
  decide +kernel

theorem iv44_c3 : below iv44.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv44.hi (iv44.p.getD 3 dPrm) (iv44.d.getD 3 [])) = true := by
  decide +kernel

theorem iv44_c4 : below iv44.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv44.hi (iv44.p.getD 4 dPrm) (iv44.d.getD 4 []) (iv44.d.getD 5 [])) = true := by
  decide +kernel

theorem iv44_ok : checkIv2 (lookDT treeK) admPre strsAll iv44 = true :=
  checkIv2_of_cases _ _ _ iv44 rfl rfl (by decide +kernel) iv44_c0 iv44_c1 iv44_c2 iv44_c3 iv44_c4

end ErdosComp
