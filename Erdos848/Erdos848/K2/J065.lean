import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv65_c0 : below iv65.lo (caseIbQ (lookDT treeK) strsAll iv65.hi (iv65.p.getD 0 dPrm) (iv65.d.getD 0 [])) = true := by
  decide +kernel

theorem iv65_c1 : below iv65.lo (caseIIQ (lookDT treeK) admPre strsAll iv65.hi (iv65.p.getD 1 dPrm) (iv65.d.getD 1 [])) = true := by
  decide +kernel

theorem iv65_c2 : below iv65.lo (caseIII1Q (lookDT treeK) admPre strsAll iv65.hi (iv65.p.getD 2 dPrm) (iv65.d.getD 2 [])) = true := by
  decide +kernel

theorem iv65_c3 : below iv65.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv65.hi (iv65.p.getD 3 dPrm) (iv65.d.getD 3 [])) = true := by
  decide +kernel

theorem iv65_c4 : below iv65.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv65.hi (iv65.p.getD 4 dPrm) (iv65.d.getD 4 []) (iv65.d.getD 5 [])) = true := by
  decide +kernel

theorem iv65_ok : checkIv2 (lookDT treeK) admPre strsAll iv65 = true :=
  checkIv2_of_cases _ _ _ iv65 rfl rfl (by decide +kernel) iv65_c0 iv65_c1 iv65_c2 iv65_c3 iv65_c4

end ErdosComp
