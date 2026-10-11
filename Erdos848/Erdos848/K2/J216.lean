import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv216_c0 : below iv216.lo (caseIbQ (lookDT treeK) strsAll iv216.hi (iv216.p.getD 0 dPrm) (iv216.d.getD 0 [])) = true := by
  decide +kernel

theorem iv216_c1 : below iv216.lo (caseIIQ (lookDT treeK) admPre strsAll iv216.hi (iv216.p.getD 1 dPrm) (iv216.d.getD 1 [])) = true := by
  decide +kernel

theorem iv216_c2 : below iv216.lo (caseIII1Q (lookDT treeK) admPre strsAll iv216.hi (iv216.p.getD 2 dPrm) (iv216.d.getD 2 [])) = true := by
  decide +kernel

theorem iv216_c3 : below iv216.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv216.hi (iv216.p.getD 3 dPrm) (iv216.d.getD 3 [])) = true := by
  decide +kernel

theorem iv216_c4 : below iv216.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv216.hi (iv216.p.getD 4 dPrm) (iv216.d.getD 4 []) (iv216.d.getD 5 [])) = true := by
  decide +kernel

theorem iv216_ok : checkIv2 (lookDT treeK) admPre strsAll iv216 = true :=
  checkIv2_of_cases _ _ _ iv216 rfl rfl (by decide +kernel) iv216_c0 iv216_c1 iv216_c2 iv216_c3 iv216_c4

end ErdosComp
