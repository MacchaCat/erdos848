import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv96_c0 : below iv96.lo (caseIbQ (lookDT treeK) strsAll iv96.hi (iv96.p.getD 0 dPrm) (iv96.d.getD 0 [])) = true := by
  decide +kernel

theorem iv96_c1 : below iv96.lo (caseIIQ (lookDT treeK) admPre strsAll iv96.hi (iv96.p.getD 1 dPrm) (iv96.d.getD 1 [])) = true := by
  decide +kernel

theorem iv96_c2 : below iv96.lo (caseIII1Q (lookDT treeK) admPre strsAll iv96.hi (iv96.p.getD 2 dPrm) (iv96.d.getD 2 [])) = true := by
  decide +kernel

theorem iv96_c3 : below iv96.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv96.hi (iv96.p.getD 3 dPrm) (iv96.d.getD 3 [])) = true := by
  decide +kernel

theorem iv96_c4 : below iv96.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv96.hi (iv96.p.getD 4 dPrm) (iv96.d.getD 4 []) (iv96.d.getD 5 [])) = true := by
  decide +kernel

theorem iv96_ok : checkIv2 (lookDT treeK) admPre strsAll iv96 = true :=
  checkIv2_of_cases _ _ _ iv96 rfl rfl (by decide +kernel) iv96_c0 iv96_c1 iv96_c2 iv96_c3 iv96_c4

end ErdosComp
