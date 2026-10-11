import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv212_c0 : below iv212.lo (caseIbQ (lookDT treeK) strsAll iv212.hi (iv212.p.getD 0 dPrm) (iv212.d.getD 0 [])) = true := by
  decide +kernel

theorem iv212_c1 : below iv212.lo (caseIIQ (lookDT treeK) admPre strsAll iv212.hi (iv212.p.getD 1 dPrm) (iv212.d.getD 1 [])) = true := by
  decide +kernel

theorem iv212_c2 : below iv212.lo (caseIII1Q (lookDT treeK) admPre strsAll iv212.hi (iv212.p.getD 2 dPrm) (iv212.d.getD 2 [])) = true := by
  decide +kernel

theorem iv212_c3 : below iv212.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv212.hi (iv212.p.getD 3 dPrm) (iv212.d.getD 3 [])) = true := by
  decide +kernel

theorem iv212_c4 : below iv212.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv212.hi (iv212.p.getD 4 dPrm) (iv212.d.getD 4 []) (iv212.d.getD 5 [])) = true := by
  decide +kernel

theorem iv212_ok : checkIv2 (lookDT treeK) admPre strsAll iv212 = true :=
  checkIv2_of_cases _ _ _ iv212 rfl rfl (by decide +kernel) iv212_c0 iv212_c1 iv212_c2 iv212_c3 iv212_c4

end ErdosComp
