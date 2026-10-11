import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv112_c0 : below iv112.lo (caseIbQ (lookDT treeK) strsAll iv112.hi (iv112.p.getD 0 dPrm) (iv112.d.getD 0 [])) = true := by
  decide +kernel

theorem iv112_c1 : below iv112.lo (caseIIQ (lookDT treeK) admPre strsAll iv112.hi (iv112.p.getD 1 dPrm) (iv112.d.getD 1 [])) = true := by
  decide +kernel

theorem iv112_c2 : below iv112.lo (caseIII1Q (lookDT treeK) admPre strsAll iv112.hi (iv112.p.getD 2 dPrm) (iv112.d.getD 2 [])) = true := by
  decide +kernel

theorem iv112_c3 : below iv112.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv112.hi (iv112.p.getD 3 dPrm) (iv112.d.getD 3 [])) = true := by
  decide +kernel

theorem iv112_c4 : below iv112.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv112.hi (iv112.p.getD 4 dPrm) (iv112.d.getD 4 []) (iv112.d.getD 5 [])) = true := by
  decide +kernel

theorem iv112_ok : checkIv2 (lookDT treeK) admPre strsAll iv112 = true :=
  checkIv2_of_cases _ _ _ iv112 rfl rfl (by decide +kernel) iv112_c0 iv112_c1 iv112_c2 iv112_c3 iv112_c4

end ErdosComp
