import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv207_c0 : below iv207.lo (caseIbQ (lookDT treeK) strsAll iv207.hi (iv207.p.getD 0 dPrm) (iv207.d.getD 0 [])) = true := by
  decide +kernel

theorem iv207_c1 : below iv207.lo (caseIIQ (lookDT treeK) admPre strsAll iv207.hi (iv207.p.getD 1 dPrm) (iv207.d.getD 1 [])) = true := by
  decide +kernel

theorem iv207_c2 : below iv207.lo (caseIII1Q (lookDT treeK) admPre strsAll iv207.hi (iv207.p.getD 2 dPrm) (iv207.d.getD 2 [])) = true := by
  decide +kernel

theorem iv207_c3 : below iv207.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv207.hi (iv207.p.getD 3 dPrm) (iv207.d.getD 3 [])) = true := by
  decide +kernel

theorem iv207_c4 : below iv207.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv207.hi (iv207.p.getD 4 dPrm) (iv207.d.getD 4 []) (iv207.d.getD 5 [])) = true := by
  decide +kernel

theorem iv207_ok : checkIv2 (lookDT treeK) admPre strsAll iv207 = true :=
  checkIv2_of_cases _ _ _ iv207 rfl rfl (by decide +kernel) iv207_c0 iv207_c1 iv207_c2 iv207_c3 iv207_c4

end ErdosComp
