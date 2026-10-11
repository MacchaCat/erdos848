import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv108_c0 : below iv108.lo (caseIbQ (lookDT treeK) strsAll iv108.hi (iv108.p.getD 0 dPrm) (iv108.d.getD 0 [])) = true := by
  decide +kernel

theorem iv108_c1 : below iv108.lo (caseIIQ (lookDT treeK) admPre strsAll iv108.hi (iv108.p.getD 1 dPrm) (iv108.d.getD 1 [])) = true := by
  decide +kernel

theorem iv108_c2 : below iv108.lo (caseIII1Q (lookDT treeK) admPre strsAll iv108.hi (iv108.p.getD 2 dPrm) (iv108.d.getD 2 [])) = true := by
  decide +kernel

theorem iv108_c3 : below iv108.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv108.hi (iv108.p.getD 3 dPrm) (iv108.d.getD 3 [])) = true := by
  decide +kernel

theorem iv108_c4 : below iv108.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv108.hi (iv108.p.getD 4 dPrm) (iv108.d.getD 4 []) (iv108.d.getD 5 [])) = true := by
  decide +kernel

theorem iv108_ok : checkIv2 (lookDT treeK) admPre strsAll iv108 = true :=
  checkIv2_of_cases _ _ _ iv108 rfl rfl (by decide +kernel) iv108_c0 iv108_c1 iv108_c2 iv108_c3 iv108_c4

end ErdosComp
