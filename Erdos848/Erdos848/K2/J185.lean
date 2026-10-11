import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv185_c0 : below iv185.lo (caseIbQ (lookDT treeK) strsAll iv185.hi (iv185.p.getD 0 dPrm) (iv185.d.getD 0 [])) = true := by
  decide +kernel

theorem iv185_c1 : below iv185.lo (caseIIQ (lookDT treeK) admPre strsAll iv185.hi (iv185.p.getD 1 dPrm) (iv185.d.getD 1 [])) = true := by
  decide +kernel

theorem iv185_c2 : below iv185.lo (caseIII1Q (lookDT treeK) admPre strsAll iv185.hi (iv185.p.getD 2 dPrm) (iv185.d.getD 2 [])) = true := by
  decide +kernel

theorem iv185_c3 : below iv185.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv185.hi (iv185.p.getD 3 dPrm) (iv185.d.getD 3 [])) = true := by
  decide +kernel

theorem iv185_c4 : below iv185.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv185.hi (iv185.p.getD 4 dPrm) (iv185.d.getD 4 []) (iv185.d.getD 5 [])) = true := by
  decide +kernel

theorem iv185_ok : checkIv2 (lookDT treeK) admPre strsAll iv185 = true :=
  checkIv2_of_cases _ _ _ iv185 rfl rfl (by decide +kernel) iv185_c0 iv185_c1 iv185_c2 iv185_c3 iv185_c4

end ErdosComp
