import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv202_c0 : below iv202.lo (caseIbQ (lookDT treeK) strsAll iv202.hi (iv202.p.getD 0 dPrm) (iv202.d.getD 0 [])) = true := by
  decide +kernel

theorem iv202_c1 : below iv202.lo (caseIIQ (lookDT treeK) admPre strsAll iv202.hi (iv202.p.getD 1 dPrm) (iv202.d.getD 1 [])) = true := by
  decide +kernel

theorem iv202_c2 : below iv202.lo (caseIII1Q (lookDT treeK) admPre strsAll iv202.hi (iv202.p.getD 2 dPrm) (iv202.d.getD 2 [])) = true := by
  decide +kernel

theorem iv202_c3 : below iv202.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv202.hi (iv202.p.getD 3 dPrm) (iv202.d.getD 3 [])) = true := by
  decide +kernel

theorem iv202_c4 : below iv202.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv202.hi (iv202.p.getD 4 dPrm) (iv202.d.getD 4 []) (iv202.d.getD 5 [])) = true := by
  decide +kernel

theorem iv202_ok : checkIv2 (lookDT treeK) admPre strsAll iv202 = true :=
  checkIv2_of_cases _ _ _ iv202 rfl rfl (by decide +kernel) iv202_c0 iv202_c1 iv202_c2 iv202_c3 iv202_c4

end ErdosComp
