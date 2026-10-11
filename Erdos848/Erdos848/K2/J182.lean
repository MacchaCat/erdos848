import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv182_c0 : below iv182.lo (caseIbQ (lookDT treeK) strsAll iv182.hi (iv182.p.getD 0 dPrm) (iv182.d.getD 0 [])) = true := by
  decide +kernel

theorem iv182_c1 : below iv182.lo (caseIIQ (lookDT treeK) admPre strsAll iv182.hi (iv182.p.getD 1 dPrm) (iv182.d.getD 1 [])) = true := by
  decide +kernel

theorem iv182_c2 : below iv182.lo (caseIII1Q (lookDT treeK) admPre strsAll iv182.hi (iv182.p.getD 2 dPrm) (iv182.d.getD 2 [])) = true := by
  decide +kernel

theorem iv182_c3 : below iv182.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv182.hi (iv182.p.getD 3 dPrm) (iv182.d.getD 3 [])) = true := by
  decide +kernel

theorem iv182_c4 : below iv182.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv182.hi (iv182.p.getD 4 dPrm) (iv182.d.getD 4 []) (iv182.d.getD 5 [])) = true := by
  decide +kernel

theorem iv182_ok : checkIv2 (lookDT treeK) admPre strsAll iv182 = true :=
  checkIv2_of_cases _ _ _ iv182 rfl rfl (by decide +kernel) iv182_c0 iv182_c1 iv182_c2 iv182_c3 iv182_c4

end ErdosComp
