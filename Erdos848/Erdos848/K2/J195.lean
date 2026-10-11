import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv195_c0 : below iv195.lo (caseIbQ (lookDT treeK) strsAll iv195.hi (iv195.p.getD 0 dPrm) (iv195.d.getD 0 [])) = true := by
  decide +kernel

theorem iv195_c1 : below iv195.lo (caseIIQ (lookDT treeK) admPre strsAll iv195.hi (iv195.p.getD 1 dPrm) (iv195.d.getD 1 [])) = true := by
  decide +kernel

theorem iv195_c2 : below iv195.lo (caseIII1Q (lookDT treeK) admPre strsAll iv195.hi (iv195.p.getD 2 dPrm) (iv195.d.getD 2 [])) = true := by
  decide +kernel

theorem iv195_c3 : below iv195.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv195.hi (iv195.p.getD 3 dPrm) (iv195.d.getD 3 [])) = true := by
  decide +kernel

theorem iv195_c4 : below iv195.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv195.hi (iv195.p.getD 4 dPrm) (iv195.d.getD 4 []) (iv195.d.getD 5 [])) = true := by
  decide +kernel

theorem iv195_ok : checkIv2 (lookDT treeK) admPre strsAll iv195 = true :=
  checkIv2_of_cases _ _ _ iv195 rfl rfl (by decide +kernel) iv195_c0 iv195_c1 iv195_c2 iv195_c3 iv195_c4

end ErdosComp
