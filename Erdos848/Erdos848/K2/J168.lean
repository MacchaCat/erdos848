import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv168_c0 : below iv168.lo (caseIbQ (lookDT treeK) strsAll iv168.hi (iv168.p.getD 0 dPrm) (iv168.d.getD 0 [])) = true := by
  decide +kernel

theorem iv168_c1 : below iv168.lo (caseIIQ (lookDT treeK) admPre strsAll iv168.hi (iv168.p.getD 1 dPrm) (iv168.d.getD 1 [])) = true := by
  decide +kernel

theorem iv168_c2 : below iv168.lo (caseIII1Q (lookDT treeK) admPre strsAll iv168.hi (iv168.p.getD 2 dPrm) (iv168.d.getD 2 [])) = true := by
  decide +kernel

theorem iv168_c3 : below iv168.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv168.hi (iv168.p.getD 3 dPrm) (iv168.d.getD 3 [])) = true := by
  decide +kernel

theorem iv168_c4 : below iv168.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv168.hi (iv168.p.getD 4 dPrm) (iv168.d.getD 4 []) (iv168.d.getD 5 [])) = true := by
  decide +kernel

theorem iv168_ok : checkIv2 (lookDT treeK) admPre strsAll iv168 = true :=
  checkIv2_of_cases _ _ _ iv168 rfl rfl (by decide +kernel) iv168_c0 iv168_c1 iv168_c2 iv168_c3 iv168_c4

end ErdosComp
