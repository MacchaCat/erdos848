import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv201_c0 : below iv201.lo (caseIbQ (lookDT treeK) strsAll iv201.hi (iv201.p.getD 0 dPrm) (iv201.d.getD 0 [])) = true := by
  decide +kernel

theorem iv201_c1 : below iv201.lo (caseIIQ (lookDT treeK) admPre strsAll iv201.hi (iv201.p.getD 1 dPrm) (iv201.d.getD 1 [])) = true := by
  decide +kernel

theorem iv201_c2 : below iv201.lo (caseIII1Q (lookDT treeK) admPre strsAll iv201.hi (iv201.p.getD 2 dPrm) (iv201.d.getD 2 [])) = true := by
  decide +kernel

theorem iv201_c3 : below iv201.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv201.hi (iv201.p.getD 3 dPrm) (iv201.d.getD 3 [])) = true := by
  decide +kernel

theorem iv201_c4 : below iv201.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv201.hi (iv201.p.getD 4 dPrm) (iv201.d.getD 4 []) (iv201.d.getD 5 [])) = true := by
  decide +kernel

theorem iv201_ok : checkIv2 (lookDT treeK) admPre strsAll iv201 = true :=
  checkIv2_of_cases _ _ _ iv201 rfl rfl (by decide +kernel) iv201_c0 iv201_c1 iv201_c2 iv201_c3 iv201_c4

end ErdosComp
