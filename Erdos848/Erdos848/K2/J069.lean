import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv69_c0 : below iv69.lo (caseIbQ (lookDT treeK) strsAll iv69.hi (iv69.p.getD 0 dPrm) (iv69.d.getD 0 [])) = true := by
  decide +kernel

theorem iv69_c1 : below iv69.lo (caseIIQ (lookDT treeK) admPre strsAll iv69.hi (iv69.p.getD 1 dPrm) (iv69.d.getD 1 [])) = true := by
  decide +kernel

theorem iv69_c2 : below iv69.lo (caseIII1Q (lookDT treeK) admPre strsAll iv69.hi (iv69.p.getD 2 dPrm) (iv69.d.getD 2 [])) = true := by
  decide +kernel

theorem iv69_c3 : below iv69.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv69.hi (iv69.p.getD 3 dPrm) (iv69.d.getD 3 [])) = true := by
  decide +kernel

theorem iv69_c4 : below iv69.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv69.hi (iv69.p.getD 4 dPrm) (iv69.d.getD 4 []) (iv69.d.getD 5 [])) = true := by
  decide +kernel

theorem iv69_ok : checkIv2 (lookDT treeK) admPre strsAll iv69 = true :=
  checkIv2_of_cases _ _ _ iv69 rfl rfl (by decide +kernel) iv69_c0 iv69_c1 iv69_c2 iv69_c3 iv69_c4

end ErdosComp
