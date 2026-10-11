import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv28_c0 : below iv28.lo (caseIbQ (lookDT treeK) strsAll iv28.hi (iv28.p.getD 0 dPrm) (iv28.d.getD 0 [])) = true := by
  decide +kernel

theorem iv28_c1 : below iv28.lo (caseIIQ (lookDT treeK) admPre strsAll iv28.hi (iv28.p.getD 1 dPrm) (iv28.d.getD 1 [])) = true := by
  decide +kernel

theorem iv28_c2 : below iv28.lo (caseIII1Q (lookDT treeK) admPre strsAll iv28.hi (iv28.p.getD 2 dPrm) (iv28.d.getD 2 [])) = true := by
  decide +kernel

theorem iv28_c3 : below iv28.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv28.hi (iv28.p.getD 3 dPrm) (iv28.d.getD 3 [])) = true := by
  decide +kernel

theorem iv28_c4 : below iv28.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv28.hi (iv28.p.getD 4 dPrm) (iv28.d.getD 4 []) (iv28.d.getD 5 [])) = true := by
  decide +kernel

theorem iv28_ok : checkIv2 (lookDT treeK) admPre strsAll iv28 = true :=
  checkIv2_of_cases _ _ _ iv28 rfl rfl (by decide +kernel) iv28_c0 iv28_c1 iv28_c2 iv28_c3 iv28_c4

end ErdosComp
