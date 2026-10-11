import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv339_c0 : below iv339.lo (caseIbQ (lookDT treeK) strsAll iv339.hi (iv339.p.getD 0 dPrm) (iv339.d.getD 0 [])) = true := by
  decide +kernel

theorem iv339_c1 : below iv339.lo (caseIIQ (lookDT treeK) admPre strsAll iv339.hi (iv339.p.getD 1 dPrm) (iv339.d.getD 1 [])) = true := by
  decide +kernel

theorem iv339_c2 : below iv339.lo (caseIII1Q (lookDT treeK) admPre strsAll iv339.hi (iv339.p.getD 2 dPrm) (iv339.d.getD 2 [])) = true := by
  decide +kernel

theorem iv339_c3 : below iv339.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv339.hi (iv339.p.getD 3 dPrm) (iv339.d.getD 3 [])) = true := by
  decide +kernel

theorem iv339_c4 : below iv339.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv339.hi (iv339.p.getD 4 dPrm) (iv339.d.getD 4 []) (iv339.d.getD 5 [])) = true := by
  decide +kernel

theorem iv339_ok : checkIv2 (lookDT treeK) admPre strsAll iv339 = true :=
  checkIv2_of_cases _ _ _ iv339 rfl rfl (by decide +kernel) iv339_c0 iv339_c1 iv339_c2 iv339_c3 iv339_c4

end ErdosComp
