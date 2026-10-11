import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv247_c0 : below iv247.lo (caseIbQ (lookDT treeK) strsAll iv247.hi (iv247.p.getD 0 dPrm) (iv247.d.getD 0 [])) = true := by
  decide +kernel

theorem iv247_c1 : below iv247.lo (caseIIQ (lookDT treeK) admPre strsAll iv247.hi (iv247.p.getD 1 dPrm) (iv247.d.getD 1 [])) = true := by
  decide +kernel

theorem iv247_c2 : below iv247.lo (caseIII1Q (lookDT treeK) admPre strsAll iv247.hi (iv247.p.getD 2 dPrm) (iv247.d.getD 2 [])) = true := by
  decide +kernel

theorem iv247_c3 : below iv247.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv247.hi (iv247.p.getD 3 dPrm) (iv247.d.getD 3 [])) = true := by
  decide +kernel

theorem iv247_c4 : below iv247.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv247.hi (iv247.p.getD 4 dPrm) (iv247.d.getD 4 []) (iv247.d.getD 5 [])) = true := by
  decide +kernel

theorem iv247_ok : checkIv2 (lookDT treeK) admPre strsAll iv247 = true :=
  checkIv2_of_cases _ _ _ iv247 rfl rfl (by decide +kernel) iv247_c0 iv247_c1 iv247_c2 iv247_c3 iv247_c4

end ErdosComp
