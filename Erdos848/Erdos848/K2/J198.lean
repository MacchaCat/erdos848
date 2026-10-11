import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv198_c0 : below iv198.lo (caseIbQ (lookDT treeK) strsAll iv198.hi (iv198.p.getD 0 dPrm) (iv198.d.getD 0 [])) = true := by
  decide +kernel

theorem iv198_c1 : below iv198.lo (caseIIQ (lookDT treeK) admPre strsAll iv198.hi (iv198.p.getD 1 dPrm) (iv198.d.getD 1 [])) = true := by
  decide +kernel

theorem iv198_c2 : below iv198.lo (caseIII1Q (lookDT treeK) admPre strsAll iv198.hi (iv198.p.getD 2 dPrm) (iv198.d.getD 2 [])) = true := by
  decide +kernel

theorem iv198_c3 : below iv198.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv198.hi (iv198.p.getD 3 dPrm) (iv198.d.getD 3 [])) = true := by
  decide +kernel

theorem iv198_c4 : below iv198.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv198.hi (iv198.p.getD 4 dPrm) (iv198.d.getD 4 []) (iv198.d.getD 5 [])) = true := by
  decide +kernel

theorem iv198_ok : checkIv2 (lookDT treeK) admPre strsAll iv198 = true :=
  checkIv2_of_cases _ _ _ iv198 rfl rfl (by decide +kernel) iv198_c0 iv198_c1 iv198_c2 iv198_c3 iv198_c4

end ErdosComp
