import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv164_c0 : below iv164.lo (caseIbQ (lookDT treeK) strsAll iv164.hi (iv164.p.getD 0 dPrm) (iv164.d.getD 0 [])) = true := by
  decide +kernel

theorem iv164_c1 : below iv164.lo (caseIIQ (lookDT treeK) admPre strsAll iv164.hi (iv164.p.getD 1 dPrm) (iv164.d.getD 1 [])) = true := by
  decide +kernel

theorem iv164_c2 : below iv164.lo (caseIII1Q (lookDT treeK) admPre strsAll iv164.hi (iv164.p.getD 2 dPrm) (iv164.d.getD 2 [])) = true := by
  decide +kernel

theorem iv164_c3 : below iv164.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv164.hi (iv164.p.getD 3 dPrm) (iv164.d.getD 3 [])) = true := by
  decide +kernel

theorem iv164_c4 : below iv164.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv164.hi (iv164.p.getD 4 dPrm) (iv164.d.getD 4 []) (iv164.d.getD 5 [])) = true := by
  decide +kernel

theorem iv164_ok : checkIv2 (lookDT treeK) admPre strsAll iv164 = true :=
  checkIv2_of_cases _ _ _ iv164 rfl rfl (by decide +kernel) iv164_c0 iv164_c1 iv164_c2 iv164_c3 iv164_c4

end ErdosComp
