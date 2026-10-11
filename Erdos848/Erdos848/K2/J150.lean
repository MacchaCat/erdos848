import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv150_c0 : below iv150.lo (caseIbQ (lookDT treeK) strsAll iv150.hi (iv150.p.getD 0 dPrm) (iv150.d.getD 0 [])) = true := by
  decide +kernel

theorem iv150_c1 : below iv150.lo (caseIIQ (lookDT treeK) admPre strsAll iv150.hi (iv150.p.getD 1 dPrm) (iv150.d.getD 1 [])) = true := by
  decide +kernel

theorem iv150_c2 : below iv150.lo (caseIII1Q (lookDT treeK) admPre strsAll iv150.hi (iv150.p.getD 2 dPrm) (iv150.d.getD 2 [])) = true := by
  decide +kernel

theorem iv150_c3 : below iv150.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv150.hi (iv150.p.getD 3 dPrm) (iv150.d.getD 3 [])) = true := by
  decide +kernel

theorem iv150_c4 : below iv150.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv150.hi (iv150.p.getD 4 dPrm) (iv150.d.getD 4 []) (iv150.d.getD 5 [])) = true := by
  decide +kernel

theorem iv150_ok : checkIv2 (lookDT treeK) admPre strsAll iv150 = true :=
  checkIv2_of_cases _ _ _ iv150 rfl rfl (by decide +kernel) iv150_c0 iv150_c1 iv150_c2 iv150_c3 iv150_c4

end ErdosComp
