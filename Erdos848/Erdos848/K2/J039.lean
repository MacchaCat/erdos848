import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv39_c0 : below iv39.lo (caseIbQ (lookDT treeK) strsAll iv39.hi (iv39.p.getD 0 dPrm) (iv39.d.getD 0 [])) = true := by
  decide +kernel

theorem iv39_c1 : below iv39.lo (caseIIQ (lookDT treeK) admPre strsAll iv39.hi (iv39.p.getD 1 dPrm) (iv39.d.getD 1 [])) = true := by
  decide +kernel

theorem iv39_c2 : below iv39.lo (caseIII1Q (lookDT treeK) admPre strsAll iv39.hi (iv39.p.getD 2 dPrm) (iv39.d.getD 2 [])) = true := by
  decide +kernel

theorem iv39_c3 : below iv39.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv39.hi (iv39.p.getD 3 dPrm) (iv39.d.getD 3 [])) = true := by
  decide +kernel

theorem iv39_c4 : below iv39.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv39.hi (iv39.p.getD 4 dPrm) (iv39.d.getD 4 []) (iv39.d.getD 5 [])) = true := by
  decide +kernel

theorem iv39_ok : checkIv2 (lookDT treeK) admPre strsAll iv39 = true :=
  checkIv2_of_cases _ _ _ iv39 rfl rfl (by decide +kernel) iv39_c0 iv39_c1 iv39_c2 iv39_c3 iv39_c4

end ErdosComp
