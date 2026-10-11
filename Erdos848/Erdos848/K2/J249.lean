import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv249_c0 : below iv249.lo (caseIbQ (lookDT treeK) strsAll iv249.hi (iv249.p.getD 0 dPrm) (iv249.d.getD 0 [])) = true := by
  decide +kernel

theorem iv249_c1 : below iv249.lo (caseIIQ (lookDT treeK) admPre strsAll iv249.hi (iv249.p.getD 1 dPrm) (iv249.d.getD 1 [])) = true := by
  decide +kernel

theorem iv249_c2 : below iv249.lo (caseIII1Q (lookDT treeK) admPre strsAll iv249.hi (iv249.p.getD 2 dPrm) (iv249.d.getD 2 [])) = true := by
  decide +kernel

theorem iv249_c3 : below iv249.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv249.hi (iv249.p.getD 3 dPrm) (iv249.d.getD 3 [])) = true := by
  decide +kernel

theorem iv249_c4 : below iv249.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv249.hi (iv249.p.getD 4 dPrm) (iv249.d.getD 4 []) (iv249.d.getD 5 [])) = true := by
  decide +kernel

theorem iv249_ok : checkIv2 (lookDT treeK) admPre strsAll iv249 = true :=
  checkIv2_of_cases _ _ _ iv249 rfl rfl (by decide +kernel) iv249_c0 iv249_c1 iv249_c2 iv249_c3 iv249_c4

end ErdosComp
