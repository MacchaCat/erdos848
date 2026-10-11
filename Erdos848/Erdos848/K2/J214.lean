import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv214_c0 : below iv214.lo (caseIbQ (lookDT treeK) strsAll iv214.hi (iv214.p.getD 0 dPrm) (iv214.d.getD 0 [])) = true := by
  decide +kernel

theorem iv214_c1 : below iv214.lo (caseIIQ (lookDT treeK) admPre strsAll iv214.hi (iv214.p.getD 1 dPrm) (iv214.d.getD 1 [])) = true := by
  decide +kernel

theorem iv214_c2 : below iv214.lo (caseIII1Q (lookDT treeK) admPre strsAll iv214.hi (iv214.p.getD 2 dPrm) (iv214.d.getD 2 [])) = true := by
  decide +kernel

theorem iv214_c3 : below iv214.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv214.hi (iv214.p.getD 3 dPrm) (iv214.d.getD 3 [])) = true := by
  decide +kernel

theorem iv214_c4 : below iv214.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv214.hi (iv214.p.getD 4 dPrm) (iv214.d.getD 4 []) (iv214.d.getD 5 [])) = true := by
  decide +kernel

theorem iv214_ok : checkIv2 (lookDT treeK) admPre strsAll iv214 = true :=
  checkIv2_of_cases _ _ _ iv214 rfl rfl (by decide +kernel) iv214_c0 iv214_c1 iv214_c2 iv214_c3 iv214_c4

end ErdosComp
