import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv270_c0 : below iv270.lo (caseIbQ (lookDT treeK) strsAll iv270.hi (iv270.p.getD 0 dPrm) (iv270.d.getD 0 [])) = true := by
  decide +kernel

theorem iv270_c1 : below iv270.lo (caseIIQ (lookDT treeK) admPre strsAll iv270.hi (iv270.p.getD 1 dPrm) (iv270.d.getD 1 [])) = true := by
  decide +kernel

theorem iv270_c2 : below iv270.lo (caseIII1Q (lookDT treeK) admPre strsAll iv270.hi (iv270.p.getD 2 dPrm) (iv270.d.getD 2 [])) = true := by
  decide +kernel

theorem iv270_c3 : below iv270.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv270.hi (iv270.p.getD 3 dPrm) (iv270.d.getD 3 [])) = true := by
  decide +kernel

theorem iv270_c4 : below iv270.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv270.hi (iv270.p.getD 4 dPrm) (iv270.d.getD 4 []) (iv270.d.getD 5 [])) = true := by
  decide +kernel

theorem iv270_ok : checkIv2 (lookDT treeK) admPre strsAll iv270 = true :=
  checkIv2_of_cases _ _ _ iv270 rfl rfl (by decide +kernel) iv270_c0 iv270_c1 iv270_c2 iv270_c3 iv270_c4

end ErdosComp
