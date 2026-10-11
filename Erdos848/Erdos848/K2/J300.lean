import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv300_c0 : below iv300.lo (caseIbQ (lookDT treeK) strsAll iv300.hi (iv300.p.getD 0 dPrm) (iv300.d.getD 0 [])) = true := by
  decide +kernel

theorem iv300_c1 : below iv300.lo (caseIIQ (lookDT treeK) admPre strsAll iv300.hi (iv300.p.getD 1 dPrm) (iv300.d.getD 1 [])) = true := by
  decide +kernel

theorem iv300_c2 : below iv300.lo (caseIII1Q (lookDT treeK) admPre strsAll iv300.hi (iv300.p.getD 2 dPrm) (iv300.d.getD 2 [])) = true := by
  decide +kernel

theorem iv300_c3 : below iv300.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv300.hi (iv300.p.getD 3 dPrm) (iv300.d.getD 3 [])) = true := by
  decide +kernel

theorem iv300_c4 : below iv300.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv300.hi (iv300.p.getD 4 dPrm) (iv300.d.getD 4 []) (iv300.d.getD 5 [])) = true := by
  decide +kernel

theorem iv300_ok : checkIv2 (lookDT treeK) admPre strsAll iv300 = true :=
  checkIv2_of_cases _ _ _ iv300 rfl rfl (by decide +kernel) iv300_c0 iv300_c1 iv300_c2 iv300_c3 iv300_c4

end ErdosComp
