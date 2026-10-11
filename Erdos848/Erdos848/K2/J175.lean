import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv175_c0 : below iv175.lo (caseIbQ (lookDT treeK) strsAll iv175.hi (iv175.p.getD 0 dPrm) (iv175.d.getD 0 [])) = true := by
  decide +kernel

theorem iv175_c1 : below iv175.lo (caseIIQ (lookDT treeK) admPre strsAll iv175.hi (iv175.p.getD 1 dPrm) (iv175.d.getD 1 [])) = true := by
  decide +kernel

theorem iv175_c2 : below iv175.lo (caseIII1Q (lookDT treeK) admPre strsAll iv175.hi (iv175.p.getD 2 dPrm) (iv175.d.getD 2 [])) = true := by
  decide +kernel

theorem iv175_c3 : below iv175.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv175.hi (iv175.p.getD 3 dPrm) (iv175.d.getD 3 [])) = true := by
  decide +kernel

theorem iv175_c4 : below iv175.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv175.hi (iv175.p.getD 4 dPrm) (iv175.d.getD 4 []) (iv175.d.getD 5 [])) = true := by
  decide +kernel

theorem iv175_ok : checkIv2 (lookDT treeK) admPre strsAll iv175 = true :=
  checkIv2_of_cases _ _ _ iv175 rfl rfl (by decide +kernel) iv175_c0 iv175_c1 iv175_c2 iv175_c3 iv175_c4

end ErdosComp
