import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv152_c0 : below iv152.lo (caseIbQ (lookDT treeK) strsAll iv152.hi (iv152.p.getD 0 dPrm) (iv152.d.getD 0 [])) = true := by
  decide +kernel

theorem iv152_c1 : below iv152.lo (caseIIQ (lookDT treeK) admPre strsAll iv152.hi (iv152.p.getD 1 dPrm) (iv152.d.getD 1 [])) = true := by
  decide +kernel

theorem iv152_c2 : below iv152.lo (caseIII1Q (lookDT treeK) admPre strsAll iv152.hi (iv152.p.getD 2 dPrm) (iv152.d.getD 2 [])) = true := by
  decide +kernel

theorem iv152_c3 : below iv152.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv152.hi (iv152.p.getD 3 dPrm) (iv152.d.getD 3 [])) = true := by
  decide +kernel

theorem iv152_c4 : below iv152.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv152.hi (iv152.p.getD 4 dPrm) (iv152.d.getD 4 []) (iv152.d.getD 5 [])) = true := by
  decide +kernel

theorem iv152_ok : checkIv2 (lookDT treeK) admPre strsAll iv152 = true :=
  checkIv2_of_cases _ _ _ iv152 rfl rfl (by decide +kernel) iv152_c0 iv152_c1 iv152_c2 iv152_c3 iv152_c4

end ErdosComp
