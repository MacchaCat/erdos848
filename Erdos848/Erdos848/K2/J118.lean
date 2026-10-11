import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv118_c0 : below iv118.lo (caseIbQ (lookDT treeK) strsAll iv118.hi (iv118.p.getD 0 dPrm) (iv118.d.getD 0 [])) = true := by
  decide +kernel

theorem iv118_c1 : below iv118.lo (caseIIQ (lookDT treeK) admPre strsAll iv118.hi (iv118.p.getD 1 dPrm) (iv118.d.getD 1 [])) = true := by
  decide +kernel

theorem iv118_c2 : below iv118.lo (caseIII1Q (lookDT treeK) admPre strsAll iv118.hi (iv118.p.getD 2 dPrm) (iv118.d.getD 2 [])) = true := by
  decide +kernel

theorem iv118_c3 : below iv118.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv118.hi (iv118.p.getD 3 dPrm) (iv118.d.getD 3 [])) = true := by
  decide +kernel

theorem iv118_c4 : below iv118.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv118.hi (iv118.p.getD 4 dPrm) (iv118.d.getD 4 []) (iv118.d.getD 5 [])) = true := by
  decide +kernel

theorem iv118_ok : checkIv2 (lookDT treeK) admPre strsAll iv118 = true :=
  checkIv2_of_cases _ _ _ iv118 rfl rfl (by decide +kernel) iv118_c0 iv118_c1 iv118_c2 iv118_c3 iv118_c4

end ErdosComp
