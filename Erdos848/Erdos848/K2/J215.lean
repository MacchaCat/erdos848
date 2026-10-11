import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv215_c0 : below iv215.lo (caseIbQ (lookDT treeK) strsAll iv215.hi (iv215.p.getD 0 dPrm) (iv215.d.getD 0 [])) = true := by
  decide +kernel

theorem iv215_c1 : below iv215.lo (caseIIQ (lookDT treeK) admPre strsAll iv215.hi (iv215.p.getD 1 dPrm) (iv215.d.getD 1 [])) = true := by
  decide +kernel

theorem iv215_c2 : below iv215.lo (caseIII1Q (lookDT treeK) admPre strsAll iv215.hi (iv215.p.getD 2 dPrm) (iv215.d.getD 2 [])) = true := by
  decide +kernel

theorem iv215_c3 : below iv215.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv215.hi (iv215.p.getD 3 dPrm) (iv215.d.getD 3 [])) = true := by
  decide +kernel

theorem iv215_c4 : below iv215.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv215.hi (iv215.p.getD 4 dPrm) (iv215.d.getD 4 []) (iv215.d.getD 5 [])) = true := by
  decide +kernel

theorem iv215_ok : checkIv2 (lookDT treeK) admPre strsAll iv215 = true :=
  checkIv2_of_cases _ _ _ iv215 rfl rfl (by decide +kernel) iv215_c0 iv215_c1 iv215_c2 iv215_c3 iv215_c4

end ErdosComp
