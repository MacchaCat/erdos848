import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv251_c0 : below iv251.lo (caseIbQ (lookDT treeK) strsAll iv251.hi (iv251.p.getD 0 dPrm) (iv251.d.getD 0 [])) = true := by
  decide +kernel

theorem iv251_c1 : below iv251.lo (caseIIQ (lookDT treeK) admPre strsAll iv251.hi (iv251.p.getD 1 dPrm) (iv251.d.getD 1 [])) = true := by
  decide +kernel

theorem iv251_c2 : below iv251.lo (caseIII1Q (lookDT treeK) admPre strsAll iv251.hi (iv251.p.getD 2 dPrm) (iv251.d.getD 2 [])) = true := by
  decide +kernel

theorem iv251_c3 : below iv251.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv251.hi (iv251.p.getD 3 dPrm) (iv251.d.getD 3 [])) = true := by
  decide +kernel

theorem iv251_c4 : below iv251.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv251.hi (iv251.p.getD 4 dPrm) (iv251.d.getD 4 []) (iv251.d.getD 5 [])) = true := by
  decide +kernel

theorem iv251_ok : checkIv2 (lookDT treeK) admPre strsAll iv251 = true :=
  checkIv2_of_cases _ _ _ iv251 rfl rfl (by decide +kernel) iv251_c0 iv251_c1 iv251_c2 iv251_c3 iv251_c4

end ErdosComp
