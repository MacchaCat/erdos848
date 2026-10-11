import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv67_c0 : below iv67.lo (caseIbQ (lookDT treeK) strsAll iv67.hi (iv67.p.getD 0 dPrm) (iv67.d.getD 0 [])) = true := by
  decide +kernel

theorem iv67_c1 : below iv67.lo (caseIIQ (lookDT treeK) admPre strsAll iv67.hi (iv67.p.getD 1 dPrm) (iv67.d.getD 1 [])) = true := by
  decide +kernel

theorem iv67_c2 : below iv67.lo (caseIII1Q (lookDT treeK) admPre strsAll iv67.hi (iv67.p.getD 2 dPrm) (iv67.d.getD 2 [])) = true := by
  decide +kernel

theorem iv67_c3 : below iv67.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv67.hi (iv67.p.getD 3 dPrm) (iv67.d.getD 3 [])) = true := by
  decide +kernel

theorem iv67_c4 : below iv67.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv67.hi (iv67.p.getD 4 dPrm) (iv67.d.getD 4 []) (iv67.d.getD 5 [])) = true := by
  decide +kernel

theorem iv67_ok : checkIv2 (lookDT treeK) admPre strsAll iv67 = true :=
  checkIv2_of_cases _ _ _ iv67 rfl rfl (by decide +kernel) iv67_c0 iv67_c1 iv67_c2 iv67_c3 iv67_c4

end ErdosComp
