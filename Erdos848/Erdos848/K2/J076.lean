import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv76_c0 : below iv76.lo (caseIbQ (lookDT treeK) strsAll iv76.hi (iv76.p.getD 0 dPrm) (iv76.d.getD 0 [])) = true := by
  decide +kernel

theorem iv76_c1 : below iv76.lo (caseIIQ (lookDT treeK) admPre strsAll iv76.hi (iv76.p.getD 1 dPrm) (iv76.d.getD 1 [])) = true := by
  decide +kernel

theorem iv76_c2 : below iv76.lo (caseIII1Q (lookDT treeK) admPre strsAll iv76.hi (iv76.p.getD 2 dPrm) (iv76.d.getD 2 [])) = true := by
  decide +kernel

theorem iv76_c3 : below iv76.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv76.hi (iv76.p.getD 3 dPrm) (iv76.d.getD 3 [])) = true := by
  decide +kernel

theorem iv76_c4 : below iv76.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv76.hi (iv76.p.getD 4 dPrm) (iv76.d.getD 4 []) (iv76.d.getD 5 [])) = true := by
  decide +kernel

theorem iv76_ok : checkIv2 (lookDT treeK) admPre strsAll iv76 = true :=
  checkIv2_of_cases _ _ _ iv76 rfl rfl (by decide +kernel) iv76_c0 iv76_c1 iv76_c2 iv76_c3 iv76_c4

end ErdosComp
