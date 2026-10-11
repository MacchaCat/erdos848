import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv230_c0 : below iv230.lo (caseIbQ (lookDT treeK) strsAll iv230.hi (iv230.p.getD 0 dPrm) (iv230.d.getD 0 [])) = true := by
  decide +kernel

theorem iv230_c1 : below iv230.lo (caseIIQ (lookDT treeK) admPre strsAll iv230.hi (iv230.p.getD 1 dPrm) (iv230.d.getD 1 [])) = true := by
  decide +kernel

theorem iv230_c2 : below iv230.lo (caseIII1Q (lookDT treeK) admPre strsAll iv230.hi (iv230.p.getD 2 dPrm) (iv230.d.getD 2 [])) = true := by
  decide +kernel

theorem iv230_c3 : below iv230.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv230.hi (iv230.p.getD 3 dPrm) (iv230.d.getD 3 [])) = true := by
  decide +kernel

theorem iv230_c4 : below iv230.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv230.hi (iv230.p.getD 4 dPrm) (iv230.d.getD 4 []) (iv230.d.getD 5 [])) = true := by
  decide +kernel

theorem iv230_ok : checkIv2 (lookDT treeK) admPre strsAll iv230 = true :=
  checkIv2_of_cases _ _ _ iv230 rfl rfl (by decide +kernel) iv230_c0 iv230_c1 iv230_c2 iv230_c3 iv230_c4

end ErdosComp
