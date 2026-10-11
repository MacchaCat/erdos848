import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv226_c0 : below iv226.lo (caseIbQ (lookDT treeK) strsAll iv226.hi (iv226.p.getD 0 dPrm) (iv226.d.getD 0 [])) = true := by
  decide +kernel

theorem iv226_c1 : below iv226.lo (caseIIQ (lookDT treeK) admPre strsAll iv226.hi (iv226.p.getD 1 dPrm) (iv226.d.getD 1 [])) = true := by
  decide +kernel

theorem iv226_c2 : below iv226.lo (caseIII1Q (lookDT treeK) admPre strsAll iv226.hi (iv226.p.getD 2 dPrm) (iv226.d.getD 2 [])) = true := by
  decide +kernel

theorem iv226_c3 : below iv226.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv226.hi (iv226.p.getD 3 dPrm) (iv226.d.getD 3 [])) = true := by
  decide +kernel

theorem iv226_c4 : below iv226.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv226.hi (iv226.p.getD 4 dPrm) (iv226.d.getD 4 []) (iv226.d.getD 5 [])) = true := by
  decide +kernel

theorem iv226_ok : checkIv2 (lookDT treeK) admPre strsAll iv226 = true :=
  checkIv2_of_cases _ _ _ iv226 rfl rfl (by decide +kernel) iv226_c0 iv226_c1 iv226_c2 iv226_c3 iv226_c4

end ErdosComp
