import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv48_c0 : below iv48.lo (caseIbQ (lookDT treeK) strsAll iv48.hi (iv48.p.getD 0 dPrm) (iv48.d.getD 0 [])) = true := by
  decide +kernel

theorem iv48_c1 : below iv48.lo (caseIIQ (lookDT treeK) admPre strsAll iv48.hi (iv48.p.getD 1 dPrm) (iv48.d.getD 1 [])) = true := by
  decide +kernel

theorem iv48_c2 : below iv48.lo (caseIII1Q (lookDT treeK) admPre strsAll iv48.hi (iv48.p.getD 2 dPrm) (iv48.d.getD 2 [])) = true := by
  decide +kernel

theorem iv48_c3 : below iv48.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv48.hi (iv48.p.getD 3 dPrm) (iv48.d.getD 3 [])) = true := by
  decide +kernel

theorem iv48_c4 : below iv48.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv48.hi (iv48.p.getD 4 dPrm) (iv48.d.getD 4 []) (iv48.d.getD 5 [])) = true := by
  decide +kernel

theorem iv48_ok : checkIv2 (lookDT treeK) admPre strsAll iv48 = true :=
  checkIv2_of_cases _ _ _ iv48 rfl rfl (by decide +kernel) iv48_c0 iv48_c1 iv48_c2 iv48_c3 iv48_c4

end ErdosComp
