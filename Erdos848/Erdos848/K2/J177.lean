import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv177_c0 : below iv177.lo (caseIbQ (lookDT treeK) strsAll iv177.hi (iv177.p.getD 0 dPrm) (iv177.d.getD 0 [])) = true := by
  decide +kernel

theorem iv177_c1 : below iv177.lo (caseIIQ (lookDT treeK) admPre strsAll iv177.hi (iv177.p.getD 1 dPrm) (iv177.d.getD 1 [])) = true := by
  decide +kernel

theorem iv177_c2 : below iv177.lo (caseIII1Q (lookDT treeK) admPre strsAll iv177.hi (iv177.p.getD 2 dPrm) (iv177.d.getD 2 [])) = true := by
  decide +kernel

theorem iv177_c3 : below iv177.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv177.hi (iv177.p.getD 3 dPrm) (iv177.d.getD 3 [])) = true := by
  decide +kernel

theorem iv177_c4 : below iv177.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv177.hi (iv177.p.getD 4 dPrm) (iv177.d.getD 4 []) (iv177.d.getD 5 [])) = true := by
  decide +kernel

theorem iv177_ok : checkIv2 (lookDT treeK) admPre strsAll iv177 = true :=
  checkIv2_of_cases _ _ _ iv177 rfl rfl (by decide +kernel) iv177_c0 iv177_c1 iv177_c2 iv177_c3 iv177_c4

end ErdosComp
