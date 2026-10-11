import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv86_c0 : below iv86.lo (caseIbQ (lookDT treeK) strsAll iv86.hi (iv86.p.getD 0 dPrm) (iv86.d.getD 0 [])) = true := by
  decide +kernel

theorem iv86_c1 : below iv86.lo (caseIIQ (lookDT treeK) admPre strsAll iv86.hi (iv86.p.getD 1 dPrm) (iv86.d.getD 1 [])) = true := by
  decide +kernel

theorem iv86_c2 : below iv86.lo (caseIII1Q (lookDT treeK) admPre strsAll iv86.hi (iv86.p.getD 2 dPrm) (iv86.d.getD 2 [])) = true := by
  decide +kernel

theorem iv86_c3 : below iv86.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv86.hi (iv86.p.getD 3 dPrm) (iv86.d.getD 3 [])) = true := by
  decide +kernel

theorem iv86_c4 : below iv86.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv86.hi (iv86.p.getD 4 dPrm) (iv86.d.getD 4 []) (iv86.d.getD 5 [])) = true := by
  decide +kernel

theorem iv86_ok : checkIv2 (lookDT treeK) admPre strsAll iv86 = true :=
  checkIv2_of_cases _ _ _ iv86 rfl rfl (by decide +kernel) iv86_c0 iv86_c1 iv86_c2 iv86_c3 iv86_c4

end ErdosComp
