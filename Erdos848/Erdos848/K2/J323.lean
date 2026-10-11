import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv323_c0 : below iv323.lo (caseIbQ (lookDT treeK) strsAll iv323.hi (iv323.p.getD 0 dPrm) (iv323.d.getD 0 [])) = true := by
  decide +kernel

theorem iv323_c1 : below iv323.lo (caseIIQ (lookDT treeK) admPre strsAll iv323.hi (iv323.p.getD 1 dPrm) (iv323.d.getD 1 [])) = true := by
  decide +kernel

theorem iv323_c2 : below iv323.lo (caseIII1Q (lookDT treeK) admPre strsAll iv323.hi (iv323.p.getD 2 dPrm) (iv323.d.getD 2 [])) = true := by
  decide +kernel

theorem iv323_c3 : below iv323.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv323.hi (iv323.p.getD 3 dPrm) (iv323.d.getD 3 [])) = true := by
  decide +kernel

theorem iv323_c4 : below iv323.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv323.hi (iv323.p.getD 4 dPrm) (iv323.d.getD 4 []) (iv323.d.getD 5 [])) = true := by
  decide +kernel

theorem iv323_ok : checkIv2 (lookDT treeK) admPre strsAll iv323 = true :=
  checkIv2_of_cases _ _ _ iv323 rfl rfl (by decide +kernel) iv323_c0 iv323_c1 iv323_c2 iv323_c3 iv323_c4

end ErdosComp
