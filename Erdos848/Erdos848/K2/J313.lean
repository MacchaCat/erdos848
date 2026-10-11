import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv313_c0 : below iv313.lo (caseIbQ (lookDT treeK) strsAll iv313.hi (iv313.p.getD 0 dPrm) (iv313.d.getD 0 [])) = true := by
  decide +kernel

theorem iv313_c1 : below iv313.lo (caseIIQ (lookDT treeK) admPre strsAll iv313.hi (iv313.p.getD 1 dPrm) (iv313.d.getD 1 [])) = true := by
  decide +kernel

theorem iv313_c2 : below iv313.lo (caseIII1Q (lookDT treeK) admPre strsAll iv313.hi (iv313.p.getD 2 dPrm) (iv313.d.getD 2 [])) = true := by
  decide +kernel

theorem iv313_c3 : below iv313.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv313.hi (iv313.p.getD 3 dPrm) (iv313.d.getD 3 [])) = true := by
  decide +kernel

theorem iv313_c4 : below iv313.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv313.hi (iv313.p.getD 4 dPrm) (iv313.d.getD 4 []) (iv313.d.getD 5 [])) = true := by
  decide +kernel

theorem iv313_ok : checkIv2 (lookDT treeK) admPre strsAll iv313 = true :=
  checkIv2_of_cases _ _ _ iv313 rfl rfl (by decide +kernel) iv313_c0 iv313_c1 iv313_c2 iv313_c3 iv313_c4

end ErdosComp
