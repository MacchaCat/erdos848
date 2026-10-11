import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv20_c0 : below iv20.lo (caseIbQ (lookDT treeK) strsAll iv20.hi (iv20.p.getD 0 dPrm) (iv20.d.getD 0 [])) = true := by
  decide +kernel

theorem iv20_c1 : below iv20.lo (caseIIQ (lookDT treeK) admPre strsAll iv20.hi (iv20.p.getD 1 dPrm) (iv20.d.getD 1 [])) = true := by
  decide +kernel

theorem iv20_c2 : below iv20.lo (caseIII1Q (lookDT treeK) admPre strsAll iv20.hi (iv20.p.getD 2 dPrm) (iv20.d.getD 2 [])) = true := by
  decide +kernel

theorem iv20_c3 : below iv20.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv20.hi (iv20.p.getD 3 dPrm) (iv20.d.getD 3 [])) = true := by
  decide +kernel

theorem iv20_c4 : below iv20.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv20.hi (iv20.p.getD 4 dPrm) (iv20.d.getD 4 []) (iv20.d.getD 5 [])) = true := by
  decide +kernel

theorem iv20_ok : checkIv2 (lookDT treeK) admPre strsAll iv20 = true :=
  checkIv2_of_cases _ _ _ iv20 rfl rfl (by decide +kernel) iv20_c0 iv20_c1 iv20_c2 iv20_c3 iv20_c4

end ErdosComp
