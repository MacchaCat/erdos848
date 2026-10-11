import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv312_c0 : below iv312.lo (caseIbQ (lookDT treeK) strsAll iv312.hi (iv312.p.getD 0 dPrm) (iv312.d.getD 0 [])) = true := by
  decide +kernel

theorem iv312_c1 : below iv312.lo (caseIIQ (lookDT treeK) admPre strsAll iv312.hi (iv312.p.getD 1 dPrm) (iv312.d.getD 1 [])) = true := by
  decide +kernel

theorem iv312_c2 : below iv312.lo (caseIII1Q (lookDT treeK) admPre strsAll iv312.hi (iv312.p.getD 2 dPrm) (iv312.d.getD 2 [])) = true := by
  decide +kernel

theorem iv312_c3 : below iv312.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv312.hi (iv312.p.getD 3 dPrm) (iv312.d.getD 3 [])) = true := by
  decide +kernel

theorem iv312_c4 : below iv312.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv312.hi (iv312.p.getD 4 dPrm) (iv312.d.getD 4 []) (iv312.d.getD 5 [])) = true := by
  decide +kernel

theorem iv312_ok : checkIv2 (lookDT treeK) admPre strsAll iv312 = true :=
  checkIv2_of_cases _ _ _ iv312 rfl rfl (by decide +kernel) iv312_c0 iv312_c1 iv312_c2 iv312_c3 iv312_c4

end ErdosComp
