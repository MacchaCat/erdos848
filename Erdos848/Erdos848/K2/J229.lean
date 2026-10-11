import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv229_c0 : below iv229.lo (caseIbQ (lookDT treeK) strsAll iv229.hi (iv229.p.getD 0 dPrm) (iv229.d.getD 0 [])) = true := by
  decide +kernel

theorem iv229_c1 : below iv229.lo (caseIIQ (lookDT treeK) admPre strsAll iv229.hi (iv229.p.getD 1 dPrm) (iv229.d.getD 1 [])) = true := by
  decide +kernel

theorem iv229_c2 : below iv229.lo (caseIII1Q (lookDT treeK) admPre strsAll iv229.hi (iv229.p.getD 2 dPrm) (iv229.d.getD 2 [])) = true := by
  decide +kernel

theorem iv229_c3 : below iv229.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv229.hi (iv229.p.getD 3 dPrm) (iv229.d.getD 3 [])) = true := by
  decide +kernel

theorem iv229_c4 : below iv229.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv229.hi (iv229.p.getD 4 dPrm) (iv229.d.getD 4 []) (iv229.d.getD 5 [])) = true := by
  decide +kernel

theorem iv229_ok : checkIv2 (lookDT treeK) admPre strsAll iv229 = true :=
  checkIv2_of_cases _ _ _ iv229 rfl rfl (by decide +kernel) iv229_c0 iv229_c1 iv229_c2 iv229_c3 iv229_c4

end ErdosComp
