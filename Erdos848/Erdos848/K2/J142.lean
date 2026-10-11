import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv142_c0 : below iv142.lo (caseIbQ (lookDT treeK) strsAll iv142.hi (iv142.p.getD 0 dPrm) (iv142.d.getD 0 [])) = true := by
  decide +kernel

theorem iv142_c1 : below iv142.lo (caseIIQ (lookDT treeK) admPre strsAll iv142.hi (iv142.p.getD 1 dPrm) (iv142.d.getD 1 [])) = true := by
  decide +kernel

theorem iv142_c2 : below iv142.lo (caseIII1Q (lookDT treeK) admPre strsAll iv142.hi (iv142.p.getD 2 dPrm) (iv142.d.getD 2 [])) = true := by
  decide +kernel

theorem iv142_c3 : below iv142.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv142.hi (iv142.p.getD 3 dPrm) (iv142.d.getD 3 [])) = true := by
  decide +kernel

theorem iv142_c4 : below iv142.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv142.hi (iv142.p.getD 4 dPrm) (iv142.d.getD 4 []) (iv142.d.getD 5 [])) = true := by
  decide +kernel

theorem iv142_ok : checkIv2 (lookDT treeK) admPre strsAll iv142 = true :=
  checkIv2_of_cases _ _ _ iv142 rfl rfl (by decide +kernel) iv142_c0 iv142_c1 iv142_c2 iv142_c3 iv142_c4

end ErdosComp
