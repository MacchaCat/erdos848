import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv256_c0 : below iv256.lo (caseIbQ (lookDT treeK) strsAll iv256.hi (iv256.p.getD 0 dPrm) (iv256.d.getD 0 [])) = true := by
  decide +kernel

theorem iv256_c1 : below iv256.lo (caseIIQ (lookDT treeK) admPre strsAll iv256.hi (iv256.p.getD 1 dPrm) (iv256.d.getD 1 [])) = true := by
  decide +kernel

theorem iv256_c2 : below iv256.lo (caseIII1Q (lookDT treeK) admPre strsAll iv256.hi (iv256.p.getD 2 dPrm) (iv256.d.getD 2 [])) = true := by
  decide +kernel

theorem iv256_c3 : below iv256.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv256.hi (iv256.p.getD 3 dPrm) (iv256.d.getD 3 [])) = true := by
  decide +kernel

theorem iv256_c4 : below iv256.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv256.hi (iv256.p.getD 4 dPrm) (iv256.d.getD 4 []) (iv256.d.getD 5 [])) = true := by
  decide +kernel

theorem iv256_ok : checkIv2 (lookDT treeK) admPre strsAll iv256 = true :=
  checkIv2_of_cases _ _ _ iv256 rfl rfl (by decide +kernel) iv256_c0 iv256_c1 iv256_c2 iv256_c3 iv256_c4

end ErdosComp
