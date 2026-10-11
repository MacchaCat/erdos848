import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv252_c0 : below iv252.lo (caseIbQ (lookDT treeK) strsAll iv252.hi (iv252.p.getD 0 dPrm) (iv252.d.getD 0 [])) = true := by
  decide +kernel

theorem iv252_c1 : below iv252.lo (caseIIQ (lookDT treeK) admPre strsAll iv252.hi (iv252.p.getD 1 dPrm) (iv252.d.getD 1 [])) = true := by
  decide +kernel

theorem iv252_c2 : below iv252.lo (caseIII1Q (lookDT treeK) admPre strsAll iv252.hi (iv252.p.getD 2 dPrm) (iv252.d.getD 2 [])) = true := by
  decide +kernel

theorem iv252_c3 : below iv252.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv252.hi (iv252.p.getD 3 dPrm) (iv252.d.getD 3 [])) = true := by
  decide +kernel

theorem iv252_c4 : below iv252.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv252.hi (iv252.p.getD 4 dPrm) (iv252.d.getD 4 []) (iv252.d.getD 5 [])) = true := by
  decide +kernel

theorem iv252_ok : checkIv2 (lookDT treeK) admPre strsAll iv252 = true :=
  checkIv2_of_cases _ _ _ iv252 rfl rfl (by decide +kernel) iv252_c0 iv252_c1 iv252_c2 iv252_c3 iv252_c4

end ErdosComp
