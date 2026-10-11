import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv12_c0 : below iv12.lo (caseIbQ (lookDT treeK) strsAll iv12.hi (iv12.p.getD 0 dPrm) (iv12.d.getD 0 [])) = true := by
  decide +kernel

theorem iv12_c1 : below iv12.lo (caseIIQ (lookDT treeK) admPre strsAll iv12.hi (iv12.p.getD 1 dPrm) (iv12.d.getD 1 [])) = true := by
  decide +kernel

theorem iv12_c2 : below iv12.lo (caseIII1Q (lookDT treeK) admPre strsAll iv12.hi (iv12.p.getD 2 dPrm) (iv12.d.getD 2 [])) = true := by
  decide +kernel

theorem iv12_c3 : below iv12.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv12.hi (iv12.p.getD 3 dPrm) (iv12.d.getD 3 [])) = true := by
  decide +kernel

theorem iv12_c4 : below iv12.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv12.hi (iv12.p.getD 4 dPrm) (iv12.d.getD 4 []) (iv12.d.getD 5 [])) = true := by
  decide +kernel

theorem iv12_ok : checkIv2 (lookDT treeK) admPre strsAll iv12 = true :=
  checkIv2_of_cases _ _ _ iv12 rfl rfl (by decide +kernel) iv12_c0 iv12_c1 iv12_c2 iv12_c3 iv12_c4

end ErdosComp
