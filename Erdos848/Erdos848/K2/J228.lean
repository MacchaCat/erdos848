import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv228_c0 : below iv228.lo (caseIbQ (lookDT treeK) strsAll iv228.hi (iv228.p.getD 0 dPrm) (iv228.d.getD 0 [])) = true := by
  decide +kernel

theorem iv228_c1 : below iv228.lo (caseIIQ (lookDT treeK) admPre strsAll iv228.hi (iv228.p.getD 1 dPrm) (iv228.d.getD 1 [])) = true := by
  decide +kernel

theorem iv228_c2 : below iv228.lo (caseIII1Q (lookDT treeK) admPre strsAll iv228.hi (iv228.p.getD 2 dPrm) (iv228.d.getD 2 [])) = true := by
  decide +kernel

theorem iv228_c3 : below iv228.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv228.hi (iv228.p.getD 3 dPrm) (iv228.d.getD 3 [])) = true := by
  decide +kernel

theorem iv228_c4 : below iv228.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv228.hi (iv228.p.getD 4 dPrm) (iv228.d.getD 4 []) (iv228.d.getD 5 [])) = true := by
  decide +kernel

theorem iv228_ok : checkIv2 (lookDT treeK) admPre strsAll iv228 = true :=
  checkIv2_of_cases _ _ _ iv228 rfl rfl (by decide +kernel) iv228_c0 iv228_c1 iv228_c2 iv228_c3 iv228_c4

end ErdosComp
