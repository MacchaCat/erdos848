import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv345_c0 : below iv345.lo (caseIbQ (lookDT treeK) strsAll iv345.hi (iv345.p.getD 0 dPrm) (iv345.d.getD 0 [])) = true := by
  decide +kernel

theorem iv345_c1 : below iv345.lo (caseIIQ (lookDT treeK) admPre strsAll iv345.hi (iv345.p.getD 1 dPrm) (iv345.d.getD 1 [])) = true := by
  decide +kernel

theorem iv345_c2 : below iv345.lo (caseIII1Q (lookDT treeK) admPre strsAll iv345.hi (iv345.p.getD 2 dPrm) (iv345.d.getD 2 [])) = true := by
  decide +kernel

theorem iv345_c3 : below iv345.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv345.hi (iv345.p.getD 3 dPrm) (iv345.d.getD 3 [])) = true := by
  decide +kernel

theorem iv345_c4 : below iv345.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv345.hi (iv345.p.getD 4 dPrm) (iv345.d.getD 4 []) (iv345.d.getD 5 [])) = true := by
  decide +kernel

theorem iv345_ok : checkIv2 (lookDT treeK) admPre strsAll iv345 = true :=
  checkIv2_of_cases _ _ _ iv345 rfl rfl (by decide +kernel) iv345_c0 iv345_c1 iv345_c2 iv345_c3 iv345_c4

end ErdosComp
