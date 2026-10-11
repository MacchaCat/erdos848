import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv286_c0 : below iv286.lo (caseIbQ (lookDT treeK) strsAll iv286.hi (iv286.p.getD 0 dPrm) (iv286.d.getD 0 [])) = true := by
  decide +kernel

theorem iv286_c1 : below iv286.lo (caseIIQ (lookDT treeK) admPre strsAll iv286.hi (iv286.p.getD 1 dPrm) (iv286.d.getD 1 [])) = true := by
  decide +kernel

theorem iv286_c2 : below iv286.lo (caseIII1Q (lookDT treeK) admPre strsAll iv286.hi (iv286.p.getD 2 dPrm) (iv286.d.getD 2 [])) = true := by
  decide +kernel

theorem iv286_c3 : below iv286.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv286.hi (iv286.p.getD 3 dPrm) (iv286.d.getD 3 [])) = true := by
  decide +kernel

theorem iv286_c4 : below iv286.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv286.hi (iv286.p.getD 4 dPrm) (iv286.d.getD 4 []) (iv286.d.getD 5 [])) = true := by
  decide +kernel

theorem iv286_ok : checkIv2 (lookDT treeK) admPre strsAll iv286 = true :=
  checkIv2_of_cases _ _ _ iv286 rfl rfl (by decide +kernel) iv286_c0 iv286_c1 iv286_c2 iv286_c3 iv286_c4

end ErdosComp
