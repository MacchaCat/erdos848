import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv55_c0 : below iv55.lo (caseIbQ (lookDT treeK) strsAll iv55.hi (iv55.p.getD 0 dPrm) (iv55.d.getD 0 [])) = true := by
  decide +kernel

theorem iv55_c1 : below iv55.lo (caseIIQ (lookDT treeK) admPre strsAll iv55.hi (iv55.p.getD 1 dPrm) (iv55.d.getD 1 [])) = true := by
  decide +kernel

theorem iv55_c2 : below iv55.lo (caseIII1Q (lookDT treeK) admPre strsAll iv55.hi (iv55.p.getD 2 dPrm) (iv55.d.getD 2 [])) = true := by
  decide +kernel

theorem iv55_c3 : below iv55.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv55.hi (iv55.p.getD 3 dPrm) (iv55.d.getD 3 [])) = true := by
  decide +kernel

theorem iv55_c4 : below iv55.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv55.hi (iv55.p.getD 4 dPrm) (iv55.d.getD 4 []) (iv55.d.getD 5 [])) = true := by
  decide +kernel

theorem iv55_ok : checkIv2 (lookDT treeK) admPre strsAll iv55 = true :=
  checkIv2_of_cases _ _ _ iv55 rfl rfl (by decide +kernel) iv55_c0 iv55_c1 iv55_c2 iv55_c3 iv55_c4

end ErdosComp
