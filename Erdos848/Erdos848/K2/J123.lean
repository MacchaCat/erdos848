import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv123_c0 : below iv123.lo (caseIbQ (lookDT treeK) strsAll iv123.hi (iv123.p.getD 0 dPrm) (iv123.d.getD 0 [])) = true := by
  decide +kernel

theorem iv123_c1 : below iv123.lo (caseIIQ (lookDT treeK) admPre strsAll iv123.hi (iv123.p.getD 1 dPrm) (iv123.d.getD 1 [])) = true := by
  decide +kernel

theorem iv123_c2 : below iv123.lo (caseIII1Q (lookDT treeK) admPre strsAll iv123.hi (iv123.p.getD 2 dPrm) (iv123.d.getD 2 [])) = true := by
  decide +kernel

theorem iv123_c3 : below iv123.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv123.hi (iv123.p.getD 3 dPrm) (iv123.d.getD 3 [])) = true := by
  decide +kernel

theorem iv123_c4 : below iv123.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv123.hi (iv123.p.getD 4 dPrm) (iv123.d.getD 4 []) (iv123.d.getD 5 [])) = true := by
  decide +kernel

theorem iv123_ok : checkIv2 (lookDT treeK) admPre strsAll iv123 = true :=
  checkIv2_of_cases _ _ _ iv123 rfl rfl (by decide +kernel) iv123_c0 iv123_c1 iv123_c2 iv123_c3 iv123_c4

end ErdosComp
