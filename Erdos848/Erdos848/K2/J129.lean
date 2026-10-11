import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv129_c0 : below iv129.lo (caseIbQ (lookDT treeK) strsAll iv129.hi (iv129.p.getD 0 dPrm) (iv129.d.getD 0 [])) = true := by
  decide +kernel

theorem iv129_c1 : below iv129.lo (caseIIQ (lookDT treeK) admPre strsAll iv129.hi (iv129.p.getD 1 dPrm) (iv129.d.getD 1 [])) = true := by
  decide +kernel

theorem iv129_c2 : below iv129.lo (caseIII1Q (lookDT treeK) admPre strsAll iv129.hi (iv129.p.getD 2 dPrm) (iv129.d.getD 2 [])) = true := by
  decide +kernel

theorem iv129_c3 : below iv129.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv129.hi (iv129.p.getD 3 dPrm) (iv129.d.getD 3 [])) = true := by
  decide +kernel

theorem iv129_c4 : below iv129.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv129.hi (iv129.p.getD 4 dPrm) (iv129.d.getD 4 []) (iv129.d.getD 5 [])) = true := by
  decide +kernel

theorem iv129_ok : checkIv2 (lookDT treeK) admPre strsAll iv129 = true :=
  checkIv2_of_cases _ _ _ iv129 rfl rfl (by decide +kernel) iv129_c0 iv129_c1 iv129_c2 iv129_c3 iv129_c4

end ErdosComp
