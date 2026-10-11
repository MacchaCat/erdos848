import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv83_c0 : below iv83.lo (caseIbQ (lookDT treeK) strsAll iv83.hi (iv83.p.getD 0 dPrm) (iv83.d.getD 0 [])) = true := by
  decide +kernel

theorem iv83_c1 : below iv83.lo (caseIIQ (lookDT treeK) admPre strsAll iv83.hi (iv83.p.getD 1 dPrm) (iv83.d.getD 1 [])) = true := by
  decide +kernel

theorem iv83_c2 : below iv83.lo (caseIII1Q (lookDT treeK) admPre strsAll iv83.hi (iv83.p.getD 2 dPrm) (iv83.d.getD 2 [])) = true := by
  decide +kernel

theorem iv83_c3 : below iv83.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv83.hi (iv83.p.getD 3 dPrm) (iv83.d.getD 3 [])) = true := by
  decide +kernel

theorem iv83_c4 : below iv83.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv83.hi (iv83.p.getD 4 dPrm) (iv83.d.getD 4 []) (iv83.d.getD 5 [])) = true := by
  decide +kernel

theorem iv83_ok : checkIv2 (lookDT treeK) admPre strsAll iv83 = true :=
  checkIv2_of_cases _ _ _ iv83 rfl rfl (by decide +kernel) iv83_c0 iv83_c1 iv83_c2 iv83_c3 iv83_c4

end ErdosComp
