import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv22_c0 : below iv22.lo (caseIbQ (lookDT treeK) strsAll iv22.hi (iv22.p.getD 0 dPrm) (iv22.d.getD 0 [])) = true := by
  decide +kernel

theorem iv22_c1 : below iv22.lo (caseIIQ (lookDT treeK) admPre strsAll iv22.hi (iv22.p.getD 1 dPrm) (iv22.d.getD 1 [])) = true := by
  decide +kernel

theorem iv22_c2 : below iv22.lo (caseIII1Q (lookDT treeK) admPre strsAll iv22.hi (iv22.p.getD 2 dPrm) (iv22.d.getD 2 [])) = true := by
  decide +kernel

theorem iv22_c3 : below iv22.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv22.hi (iv22.p.getD 3 dPrm) (iv22.d.getD 3 [])) = true := by
  decide +kernel

theorem iv22_c4 : below iv22.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv22.hi (iv22.p.getD 4 dPrm) (iv22.d.getD 4 []) (iv22.d.getD 5 [])) = true := by
  decide +kernel

theorem iv22_ok : checkIv2 (lookDT treeK) admPre strsAll iv22 = true :=
  checkIv2_of_cases _ _ _ iv22 rfl rfl (by decide +kernel) iv22_c0 iv22_c1 iv22_c2 iv22_c3 iv22_c4

end ErdosComp
