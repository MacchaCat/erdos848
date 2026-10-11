import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv62_c0 : below iv62.lo (caseIbQ (lookDT treeK) strsAll iv62.hi (iv62.p.getD 0 dPrm) (iv62.d.getD 0 [])) = true := by
  decide +kernel

theorem iv62_c1 : below iv62.lo (caseIIQ (lookDT treeK) admPre strsAll iv62.hi (iv62.p.getD 1 dPrm) (iv62.d.getD 1 [])) = true := by
  decide +kernel

theorem iv62_c2 : below iv62.lo (caseIII1Q (lookDT treeK) admPre strsAll iv62.hi (iv62.p.getD 2 dPrm) (iv62.d.getD 2 [])) = true := by
  decide +kernel

theorem iv62_c3 : below iv62.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv62.hi (iv62.p.getD 3 dPrm) (iv62.d.getD 3 [])) = true := by
  decide +kernel

theorem iv62_c4 : below iv62.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv62.hi (iv62.p.getD 4 dPrm) (iv62.d.getD 4 []) (iv62.d.getD 5 [])) = true := by
  decide +kernel

theorem iv62_ok : checkIv2 (lookDT treeK) admPre strsAll iv62 = true :=
  checkIv2_of_cases _ _ _ iv62 rfl rfl (by decide +kernel) iv62_c0 iv62_c1 iv62_c2 iv62_c3 iv62_c4

end ErdosComp
