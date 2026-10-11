import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv171_c0 : below iv171.lo (caseIbQ (lookDT treeK) strsAll iv171.hi (iv171.p.getD 0 dPrm) (iv171.d.getD 0 [])) = true := by
  decide +kernel

theorem iv171_c1 : below iv171.lo (caseIIQ (lookDT treeK) admPre strsAll iv171.hi (iv171.p.getD 1 dPrm) (iv171.d.getD 1 [])) = true := by
  decide +kernel

theorem iv171_c2 : below iv171.lo (caseIII1Q (lookDT treeK) admPre strsAll iv171.hi (iv171.p.getD 2 dPrm) (iv171.d.getD 2 [])) = true := by
  decide +kernel

theorem iv171_c3 : below iv171.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv171.hi (iv171.p.getD 3 dPrm) (iv171.d.getD 3 [])) = true := by
  decide +kernel

theorem iv171_c4 : below iv171.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv171.hi (iv171.p.getD 4 dPrm) (iv171.d.getD 4 []) (iv171.d.getD 5 [])) = true := by
  decide +kernel

theorem iv171_ok : checkIv2 (lookDT treeK) admPre strsAll iv171 = true :=
  checkIv2_of_cases _ _ _ iv171 rfl rfl (by decide +kernel) iv171_c0 iv171_c1 iv171_c2 iv171_c3 iv171_c4

end ErdosComp
