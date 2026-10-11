import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv25_c0 : below iv25.lo (caseIbQ (lookDT treeK) strsAll iv25.hi (iv25.p.getD 0 dPrm) (iv25.d.getD 0 [])) = true := by
  decide +kernel

theorem iv25_c1 : below iv25.lo (caseIIQ (lookDT treeK) admPre strsAll iv25.hi (iv25.p.getD 1 dPrm) (iv25.d.getD 1 [])) = true := by
  decide +kernel

theorem iv25_c2 : below iv25.lo (caseIII1Q (lookDT treeK) admPre strsAll iv25.hi (iv25.p.getD 2 dPrm) (iv25.d.getD 2 [])) = true := by
  decide +kernel

theorem iv25_c3 : below iv25.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv25.hi (iv25.p.getD 3 dPrm) (iv25.d.getD 3 [])) = true := by
  decide +kernel

theorem iv25_c4 : below iv25.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv25.hi (iv25.p.getD 4 dPrm) (iv25.d.getD 4 []) (iv25.d.getD 5 [])) = true := by
  decide +kernel

theorem iv25_ok : checkIv2 (lookDT treeK) admPre strsAll iv25 = true :=
  checkIv2_of_cases _ _ _ iv25 rfl rfl (by decide +kernel) iv25_c0 iv25_c1 iv25_c2 iv25_c3 iv25_c4

end ErdosComp
