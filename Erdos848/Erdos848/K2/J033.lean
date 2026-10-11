import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv33_c0 : below iv33.lo (caseIbQ (lookDT treeK) strsAll iv33.hi (iv33.p.getD 0 dPrm) (iv33.d.getD 0 [])) = true := by
  decide +kernel

theorem iv33_c1 : below iv33.lo (caseIIQ (lookDT treeK) admPre strsAll iv33.hi (iv33.p.getD 1 dPrm) (iv33.d.getD 1 [])) = true := by
  decide +kernel

theorem iv33_c2 : below iv33.lo (caseIII1Q (lookDT treeK) admPre strsAll iv33.hi (iv33.p.getD 2 dPrm) (iv33.d.getD 2 [])) = true := by
  decide +kernel

theorem iv33_c3 : below iv33.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv33.hi (iv33.p.getD 3 dPrm) (iv33.d.getD 3 [])) = true := by
  decide +kernel

theorem iv33_c4 : below iv33.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv33.hi (iv33.p.getD 4 dPrm) (iv33.d.getD 4 []) (iv33.d.getD 5 [])) = true := by
  decide +kernel

theorem iv33_ok : checkIv2 (lookDT treeK) admPre strsAll iv33 = true :=
  checkIv2_of_cases _ _ _ iv33 rfl rfl (by decide +kernel) iv33_c0 iv33_c1 iv33_c2 iv33_c3 iv33_c4

end ErdosComp
