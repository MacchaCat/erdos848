import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv223_c0 : below iv223.lo (caseIbQ (lookDT treeK) strsAll iv223.hi (iv223.p.getD 0 dPrm) (iv223.d.getD 0 [])) = true := by
  decide +kernel

theorem iv223_c1 : below iv223.lo (caseIIQ (lookDT treeK) admPre strsAll iv223.hi (iv223.p.getD 1 dPrm) (iv223.d.getD 1 [])) = true := by
  decide +kernel

theorem iv223_c2 : below iv223.lo (caseIII1Q (lookDT treeK) admPre strsAll iv223.hi (iv223.p.getD 2 dPrm) (iv223.d.getD 2 [])) = true := by
  decide +kernel

theorem iv223_c3 : below iv223.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv223.hi (iv223.p.getD 3 dPrm) (iv223.d.getD 3 [])) = true := by
  decide +kernel

theorem iv223_c4 : below iv223.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv223.hi (iv223.p.getD 4 dPrm) (iv223.d.getD 4 []) (iv223.d.getD 5 [])) = true := by
  decide +kernel

theorem iv223_ok : checkIv2 (lookDT treeK) admPre strsAll iv223 = true :=
  checkIv2_of_cases _ _ _ iv223 rfl rfl (by decide +kernel) iv223_c0 iv223_c1 iv223_c2 iv223_c3 iv223_c4

end ErdosComp
