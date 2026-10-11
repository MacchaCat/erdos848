import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv144_c0 : below iv144.lo (caseIbQ (lookDT treeK) strsAll iv144.hi (iv144.p.getD 0 dPrm) (iv144.d.getD 0 [])) = true := by
  decide +kernel

theorem iv144_c1 : below iv144.lo (caseIIQ (lookDT treeK) admPre strsAll iv144.hi (iv144.p.getD 1 dPrm) (iv144.d.getD 1 [])) = true := by
  decide +kernel

theorem iv144_c2 : below iv144.lo (caseIII1Q (lookDT treeK) admPre strsAll iv144.hi (iv144.p.getD 2 dPrm) (iv144.d.getD 2 [])) = true := by
  decide +kernel

theorem iv144_c3 : below iv144.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv144.hi (iv144.p.getD 3 dPrm) (iv144.d.getD 3 [])) = true := by
  decide +kernel

theorem iv144_c4 : below iv144.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv144.hi (iv144.p.getD 4 dPrm) (iv144.d.getD 4 []) (iv144.d.getD 5 [])) = true := by
  decide +kernel

theorem iv144_ok : checkIv2 (lookDT treeK) admPre strsAll iv144 = true :=
  checkIv2_of_cases _ _ _ iv144 rfl rfl (by decide +kernel) iv144_c0 iv144_c1 iv144_c2 iv144_c3 iv144_c4

end ErdosComp
