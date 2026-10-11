import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv193_c0 : below iv193.lo (caseIbQ (lookDT treeK) strsAll iv193.hi (iv193.p.getD 0 dPrm) (iv193.d.getD 0 [])) = true := by
  decide +kernel

theorem iv193_c1 : below iv193.lo (caseIIQ (lookDT treeK) admPre strsAll iv193.hi (iv193.p.getD 1 dPrm) (iv193.d.getD 1 [])) = true := by
  decide +kernel

theorem iv193_c2 : below iv193.lo (caseIII1Q (lookDT treeK) admPre strsAll iv193.hi (iv193.p.getD 2 dPrm) (iv193.d.getD 2 [])) = true := by
  decide +kernel

theorem iv193_c3 : below iv193.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv193.hi (iv193.p.getD 3 dPrm) (iv193.d.getD 3 [])) = true := by
  decide +kernel

theorem iv193_c4 : below iv193.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv193.hi (iv193.p.getD 4 dPrm) (iv193.d.getD 4 []) (iv193.d.getD 5 [])) = true := by
  decide +kernel

theorem iv193_ok : checkIv2 (lookDT treeK) admPre strsAll iv193 = true :=
  checkIv2_of_cases _ _ _ iv193 rfl rfl (by decide +kernel) iv193_c0 iv193_c1 iv193_c2 iv193_c3 iv193_c4

end ErdosComp
