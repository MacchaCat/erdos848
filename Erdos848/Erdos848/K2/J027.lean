import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv27_c0 : below iv27.lo (caseIbQ (lookDT treeK) strsAll iv27.hi (iv27.p.getD 0 dPrm) (iv27.d.getD 0 [])) = true := by
  decide +kernel

theorem iv27_c1 : below iv27.lo (caseIIQ (lookDT treeK) admPre strsAll iv27.hi (iv27.p.getD 1 dPrm) (iv27.d.getD 1 [])) = true := by
  decide +kernel

theorem iv27_c2 : below iv27.lo (caseIII1Q (lookDT treeK) admPre strsAll iv27.hi (iv27.p.getD 2 dPrm) (iv27.d.getD 2 [])) = true := by
  decide +kernel

theorem iv27_c3 : below iv27.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv27.hi (iv27.p.getD 3 dPrm) (iv27.d.getD 3 [])) = true := by
  decide +kernel

theorem iv27_c4 : below iv27.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv27.hi (iv27.p.getD 4 dPrm) (iv27.d.getD 4 []) (iv27.d.getD 5 [])) = true := by
  decide +kernel

theorem iv27_ok : checkIv2 (lookDT treeK) admPre strsAll iv27 = true :=
  checkIv2_of_cases _ _ _ iv27 rfl rfl (by decide +kernel) iv27_c0 iv27_c1 iv27_c2 iv27_c3 iv27_c4

end ErdosComp
