import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv87_c0 : below iv87.lo (caseIbQ (lookDT treeK) strsAll iv87.hi (iv87.p.getD 0 dPrm) (iv87.d.getD 0 [])) = true := by
  decide +kernel

theorem iv87_c1 : below iv87.lo (caseIIQ (lookDT treeK) admPre strsAll iv87.hi (iv87.p.getD 1 dPrm) (iv87.d.getD 1 [])) = true := by
  decide +kernel

theorem iv87_c2 : below iv87.lo (caseIII1Q (lookDT treeK) admPre strsAll iv87.hi (iv87.p.getD 2 dPrm) (iv87.d.getD 2 [])) = true := by
  decide +kernel

theorem iv87_c3 : below iv87.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv87.hi (iv87.p.getD 3 dPrm) (iv87.d.getD 3 [])) = true := by
  decide +kernel

theorem iv87_c4 : below iv87.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv87.hi (iv87.p.getD 4 dPrm) (iv87.d.getD 4 []) (iv87.d.getD 5 [])) = true := by
  decide +kernel

theorem iv87_ok : checkIv2 (lookDT treeK) admPre strsAll iv87 = true :=
  checkIv2_of_cases _ _ _ iv87 rfl rfl (by decide +kernel) iv87_c0 iv87_c1 iv87_c2 iv87_c3 iv87_c4

end ErdosComp
