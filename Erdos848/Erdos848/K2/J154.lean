import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv154_c0 : below iv154.lo (caseIbQ (lookDT treeK) strsAll iv154.hi (iv154.p.getD 0 dPrm) (iv154.d.getD 0 [])) = true := by
  decide +kernel

theorem iv154_c1 : below iv154.lo (caseIIQ (lookDT treeK) admPre strsAll iv154.hi (iv154.p.getD 1 dPrm) (iv154.d.getD 1 [])) = true := by
  decide +kernel

theorem iv154_c2 : below iv154.lo (caseIII1Q (lookDT treeK) admPre strsAll iv154.hi (iv154.p.getD 2 dPrm) (iv154.d.getD 2 [])) = true := by
  decide +kernel

theorem iv154_c3 : below iv154.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv154.hi (iv154.p.getD 3 dPrm) (iv154.d.getD 3 [])) = true := by
  decide +kernel

theorem iv154_c4 : below iv154.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv154.hi (iv154.p.getD 4 dPrm) (iv154.d.getD 4 []) (iv154.d.getD 5 [])) = true := by
  decide +kernel

theorem iv154_ok : checkIv2 (lookDT treeK) admPre strsAll iv154 = true :=
  checkIv2_of_cases _ _ _ iv154 rfl rfl (by decide +kernel) iv154_c0 iv154_c1 iv154_c2 iv154_c3 iv154_c4

end ErdosComp
