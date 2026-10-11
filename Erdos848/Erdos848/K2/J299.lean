import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv299_c0 : below iv299.lo (caseIbQ (lookDT treeK) strsAll iv299.hi (iv299.p.getD 0 dPrm) (iv299.d.getD 0 [])) = true := by
  decide +kernel

theorem iv299_c1 : below iv299.lo (caseIIQ (lookDT treeK) admPre strsAll iv299.hi (iv299.p.getD 1 dPrm) (iv299.d.getD 1 [])) = true := by
  decide +kernel

theorem iv299_c2 : below iv299.lo (caseIII1Q (lookDT treeK) admPre strsAll iv299.hi (iv299.p.getD 2 dPrm) (iv299.d.getD 2 [])) = true := by
  decide +kernel

theorem iv299_c3 : below iv299.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv299.hi (iv299.p.getD 3 dPrm) (iv299.d.getD 3 [])) = true := by
  decide +kernel

theorem iv299_c4 : below iv299.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv299.hi (iv299.p.getD 4 dPrm) (iv299.d.getD 4 []) (iv299.d.getD 5 [])) = true := by
  decide +kernel

theorem iv299_ok : checkIv2 (lookDT treeK) admPre strsAll iv299 = true :=
  checkIv2_of_cases _ _ _ iv299 rfl rfl (by decide +kernel) iv299_c0 iv299_c1 iv299_c2 iv299_c3 iv299_c4

end ErdosComp
