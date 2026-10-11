import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv105_c0 : below iv105.lo (caseIbQ (lookDT treeK) strsAll iv105.hi (iv105.p.getD 0 dPrm) (iv105.d.getD 0 [])) = true := by
  decide +kernel

theorem iv105_c1 : below iv105.lo (caseIIQ (lookDT treeK) admPre strsAll iv105.hi (iv105.p.getD 1 dPrm) (iv105.d.getD 1 [])) = true := by
  decide +kernel

theorem iv105_c2 : below iv105.lo (caseIII1Q (lookDT treeK) admPre strsAll iv105.hi (iv105.p.getD 2 dPrm) (iv105.d.getD 2 [])) = true := by
  decide +kernel

theorem iv105_c3 : below iv105.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv105.hi (iv105.p.getD 3 dPrm) (iv105.d.getD 3 [])) = true := by
  decide +kernel

theorem iv105_c4 : below iv105.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv105.hi (iv105.p.getD 4 dPrm) (iv105.d.getD 4 []) (iv105.d.getD 5 [])) = true := by
  decide +kernel

theorem iv105_ok : checkIv2 (lookDT treeK) admPre strsAll iv105 = true :=
  checkIv2_of_cases _ _ _ iv105 rfl rfl (by decide +kernel) iv105_c0 iv105_c1 iv105_c2 iv105_c3 iv105_c4

end ErdosComp
