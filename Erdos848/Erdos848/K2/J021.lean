import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv21_c0 : below iv21.lo (caseIbQ (lookDT treeK) strsAll iv21.hi (iv21.p.getD 0 dPrm) (iv21.d.getD 0 [])) = true := by
  decide +kernel

theorem iv21_c1 : below iv21.lo (caseIIQ (lookDT treeK) admPre strsAll iv21.hi (iv21.p.getD 1 dPrm) (iv21.d.getD 1 [])) = true := by
  decide +kernel

theorem iv21_c2 : below iv21.lo (caseIII1Q (lookDT treeK) admPre strsAll iv21.hi (iv21.p.getD 2 dPrm) (iv21.d.getD 2 [])) = true := by
  decide +kernel

theorem iv21_c3 : below iv21.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv21.hi (iv21.p.getD 3 dPrm) (iv21.d.getD 3 [])) = true := by
  decide +kernel

theorem iv21_c4 : below iv21.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv21.hi (iv21.p.getD 4 dPrm) (iv21.d.getD 4 []) (iv21.d.getD 5 [])) = true := by
  decide +kernel

theorem iv21_ok : checkIv2 (lookDT treeK) admPre strsAll iv21 = true :=
  checkIv2_of_cases _ _ _ iv21 rfl rfl (by decide +kernel) iv21_c0 iv21_c1 iv21_c2 iv21_c3 iv21_c4

end ErdosComp
