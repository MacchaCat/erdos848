import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv210_c0 : below iv210.lo (caseIbQ (lookDT treeK) strsAll iv210.hi (iv210.p.getD 0 dPrm) (iv210.d.getD 0 [])) = true := by
  decide +kernel

theorem iv210_c1 : below iv210.lo (caseIIQ (lookDT treeK) admPre strsAll iv210.hi (iv210.p.getD 1 dPrm) (iv210.d.getD 1 [])) = true := by
  decide +kernel

theorem iv210_c2 : below iv210.lo (caseIII1Q (lookDT treeK) admPre strsAll iv210.hi (iv210.p.getD 2 dPrm) (iv210.d.getD 2 [])) = true := by
  decide +kernel

theorem iv210_c3 : below iv210.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv210.hi (iv210.p.getD 3 dPrm) (iv210.d.getD 3 [])) = true := by
  decide +kernel

theorem iv210_c4 : below iv210.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv210.hi (iv210.p.getD 4 dPrm) (iv210.d.getD 4 []) (iv210.d.getD 5 [])) = true := by
  decide +kernel

theorem iv210_ok : checkIv2 (lookDT treeK) admPre strsAll iv210 = true :=
  checkIv2_of_cases _ _ _ iv210 rfl rfl (by decide +kernel) iv210_c0 iv210_c1 iv210_c2 iv210_c3 iv210_c4

end ErdosComp
