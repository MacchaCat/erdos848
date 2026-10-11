import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv7_c0 : below iv7.lo (caseIbQ (lookDT treeK) strsAll iv7.hi (iv7.p.getD 0 dPrm) (iv7.d.getD 0 [])) = true := by
  decide +kernel

theorem iv7_c1 : below iv7.lo (caseIIQ (lookDT treeK) admPre strsAll iv7.hi (iv7.p.getD 1 dPrm) (iv7.d.getD 1 [])) = true := by
  decide +kernel

theorem iv7_c2 : below iv7.lo (caseIII1Q (lookDT treeK) admPre strsAll iv7.hi (iv7.p.getD 2 dPrm) (iv7.d.getD 2 [])) = true := by
  decide +kernel

theorem iv7_c3 : below iv7.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv7.hi (iv7.p.getD 3 dPrm) (iv7.d.getD 3 [])) = true := by
  decide +kernel

theorem iv7_c4 : below iv7.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv7.hi (iv7.p.getD 4 dPrm) (iv7.d.getD 4 []) (iv7.d.getD 5 [])) = true := by
  decide +kernel

theorem iv7_ok : checkIv2 (lookDT treeK) admPre strsAll iv7 = true :=
  checkIv2_of_cases _ _ _ iv7 rfl rfl (by decide +kernel) iv7_c0 iv7_c1 iv7_c2 iv7_c3 iv7_c4

end ErdosComp
