import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv269_c0 : below iv269.lo (caseIbQ (lookDT treeK) strsAll iv269.hi (iv269.p.getD 0 dPrm) (iv269.d.getD 0 [])) = true := by
  decide +kernel

theorem iv269_c1 : below iv269.lo (caseIIQ (lookDT treeK) admPre strsAll iv269.hi (iv269.p.getD 1 dPrm) (iv269.d.getD 1 [])) = true := by
  decide +kernel

theorem iv269_c2 : below iv269.lo (caseIII1Q (lookDT treeK) admPre strsAll iv269.hi (iv269.p.getD 2 dPrm) (iv269.d.getD 2 [])) = true := by
  decide +kernel

theorem iv269_c3 : below iv269.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv269.hi (iv269.p.getD 3 dPrm) (iv269.d.getD 3 [])) = true := by
  decide +kernel

theorem iv269_c4 : below iv269.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv269.hi (iv269.p.getD 4 dPrm) (iv269.d.getD 4 []) (iv269.d.getD 5 [])) = true := by
  decide +kernel

theorem iv269_ok : checkIv2 (lookDT treeK) admPre strsAll iv269 = true :=
  checkIv2_of_cases _ _ _ iv269 rfl rfl (by decide +kernel) iv269_c0 iv269_c1 iv269_c2 iv269_c3 iv269_c4

end ErdosComp
