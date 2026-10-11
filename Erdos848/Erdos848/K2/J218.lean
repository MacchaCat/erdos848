import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv218_c0 : below iv218.lo (caseIbQ (lookDT treeK) strsAll iv218.hi (iv218.p.getD 0 dPrm) (iv218.d.getD 0 [])) = true := by
  decide +kernel

theorem iv218_c1 : below iv218.lo (caseIIQ (lookDT treeK) admPre strsAll iv218.hi (iv218.p.getD 1 dPrm) (iv218.d.getD 1 [])) = true := by
  decide +kernel

theorem iv218_c2 : below iv218.lo (caseIII1Q (lookDT treeK) admPre strsAll iv218.hi (iv218.p.getD 2 dPrm) (iv218.d.getD 2 [])) = true := by
  decide +kernel

theorem iv218_c3 : below iv218.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv218.hi (iv218.p.getD 3 dPrm) (iv218.d.getD 3 [])) = true := by
  decide +kernel

theorem iv218_c4 : below iv218.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv218.hi (iv218.p.getD 4 dPrm) (iv218.d.getD 4 []) (iv218.d.getD 5 [])) = true := by
  decide +kernel

theorem iv218_ok : checkIv2 (lookDT treeK) admPre strsAll iv218 = true :=
  checkIv2_of_cases _ _ _ iv218 rfl rfl (by decide +kernel) iv218_c0 iv218_c1 iv218_c2 iv218_c3 iv218_c4

end ErdosComp
