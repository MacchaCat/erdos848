import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv245_c0 : below iv245.lo (caseIbQ (lookDT treeK) strsAll iv245.hi (iv245.p.getD 0 dPrm) (iv245.d.getD 0 [])) = true := by
  decide +kernel

theorem iv245_c1 : below iv245.lo (caseIIQ (lookDT treeK) admPre strsAll iv245.hi (iv245.p.getD 1 dPrm) (iv245.d.getD 1 [])) = true := by
  decide +kernel

theorem iv245_c2 : below iv245.lo (caseIII1Q (lookDT treeK) admPre strsAll iv245.hi (iv245.p.getD 2 dPrm) (iv245.d.getD 2 [])) = true := by
  decide +kernel

theorem iv245_c3 : below iv245.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv245.hi (iv245.p.getD 3 dPrm) (iv245.d.getD 3 [])) = true := by
  decide +kernel

theorem iv245_c4 : below iv245.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv245.hi (iv245.p.getD 4 dPrm) (iv245.d.getD 4 []) (iv245.d.getD 5 [])) = true := by
  decide +kernel

theorem iv245_ok : checkIv2 (lookDT treeK) admPre strsAll iv245 = true :=
  checkIv2_of_cases _ _ _ iv245 rfl rfl (by decide +kernel) iv245_c0 iv245_c1 iv245_c2 iv245_c3 iv245_c4

end ErdosComp
