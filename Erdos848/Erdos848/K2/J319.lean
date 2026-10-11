import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv319_c0 : below iv319.lo (caseIbQ (lookDT treeK) strsAll iv319.hi (iv319.p.getD 0 dPrm) (iv319.d.getD 0 [])) = true := by
  decide +kernel

theorem iv319_c1 : below iv319.lo (caseIIQ (lookDT treeK) admPre strsAll iv319.hi (iv319.p.getD 1 dPrm) (iv319.d.getD 1 [])) = true := by
  decide +kernel

theorem iv319_c2 : below iv319.lo (caseIII1Q (lookDT treeK) admPre strsAll iv319.hi (iv319.p.getD 2 dPrm) (iv319.d.getD 2 [])) = true := by
  decide +kernel

theorem iv319_c3 : below iv319.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv319.hi (iv319.p.getD 3 dPrm) (iv319.d.getD 3 [])) = true := by
  decide +kernel

theorem iv319_c4 : below iv319.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv319.hi (iv319.p.getD 4 dPrm) (iv319.d.getD 4 []) (iv319.d.getD 5 [])) = true := by
  decide +kernel

theorem iv319_ok : checkIv2 (lookDT treeK) admPre strsAll iv319 = true :=
  checkIv2_of_cases _ _ _ iv319 rfl rfl (by decide +kernel) iv319_c0 iv319_c1 iv319_c2 iv319_c3 iv319_c4

end ErdosComp
