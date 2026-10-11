import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv47_c0 : below iv47.lo (caseIbQ (lookDT treeK) strsAll iv47.hi (iv47.p.getD 0 dPrm) (iv47.d.getD 0 [])) = true := by
  decide +kernel

theorem iv47_c1 : below iv47.lo (caseIIQ (lookDT treeK) admPre strsAll iv47.hi (iv47.p.getD 1 dPrm) (iv47.d.getD 1 [])) = true := by
  decide +kernel

theorem iv47_c2 : below iv47.lo (caseIII1Q (lookDT treeK) admPre strsAll iv47.hi (iv47.p.getD 2 dPrm) (iv47.d.getD 2 [])) = true := by
  decide +kernel

theorem iv47_c3 : below iv47.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv47.hi (iv47.p.getD 3 dPrm) (iv47.d.getD 3 [])) = true := by
  decide +kernel

theorem iv47_c4 : below iv47.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv47.hi (iv47.p.getD 4 dPrm) (iv47.d.getD 4 []) (iv47.d.getD 5 [])) = true := by
  decide +kernel

theorem iv47_ok : checkIv2 (lookDT treeK) admPre strsAll iv47 = true :=
  checkIv2_of_cases _ _ _ iv47 rfl rfl (by decide +kernel) iv47_c0 iv47_c1 iv47_c2 iv47_c3 iv47_c4

end ErdosComp
