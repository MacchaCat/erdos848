import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv187_c0 : below iv187.lo (caseIbQ (lookDT treeK) strsAll iv187.hi (iv187.p.getD 0 dPrm) (iv187.d.getD 0 [])) = true := by
  decide +kernel

theorem iv187_c1 : below iv187.lo (caseIIQ (lookDT treeK) admPre strsAll iv187.hi (iv187.p.getD 1 dPrm) (iv187.d.getD 1 [])) = true := by
  decide +kernel

theorem iv187_c2 : below iv187.lo (caseIII1Q (lookDT treeK) admPre strsAll iv187.hi (iv187.p.getD 2 dPrm) (iv187.d.getD 2 [])) = true := by
  decide +kernel

theorem iv187_c3 : below iv187.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv187.hi (iv187.p.getD 3 dPrm) (iv187.d.getD 3 [])) = true := by
  decide +kernel

theorem iv187_c4 : below iv187.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv187.hi (iv187.p.getD 4 dPrm) (iv187.d.getD 4 []) (iv187.d.getD 5 [])) = true := by
  decide +kernel

theorem iv187_ok : checkIv2 (lookDT treeK) admPre strsAll iv187 = true :=
  checkIv2_of_cases _ _ _ iv187 rfl rfl (by decide +kernel) iv187_c0 iv187_c1 iv187_c2 iv187_c3 iv187_c4

end ErdosComp
