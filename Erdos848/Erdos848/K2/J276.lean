import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv276_c0 : below iv276.lo (caseIbQ (lookDT treeK) strsAll iv276.hi (iv276.p.getD 0 dPrm) (iv276.d.getD 0 [])) = true := by
  decide +kernel

theorem iv276_c1 : below iv276.lo (caseIIQ (lookDT treeK) admPre strsAll iv276.hi (iv276.p.getD 1 dPrm) (iv276.d.getD 1 [])) = true := by
  decide +kernel

theorem iv276_c2 : below iv276.lo (caseIII1Q (lookDT treeK) admPre strsAll iv276.hi (iv276.p.getD 2 dPrm) (iv276.d.getD 2 [])) = true := by
  decide +kernel

theorem iv276_c3 : below iv276.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv276.hi (iv276.p.getD 3 dPrm) (iv276.d.getD 3 [])) = true := by
  decide +kernel

theorem iv276_c4 : below iv276.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv276.hi (iv276.p.getD 4 dPrm) (iv276.d.getD 4 []) (iv276.d.getD 5 [])) = true := by
  decide +kernel

theorem iv276_ok : checkIv2 (lookDT treeK) admPre strsAll iv276 = true :=
  checkIv2_of_cases _ _ _ iv276 rfl rfl (by decide +kernel) iv276_c0 iv276_c1 iv276_c2 iv276_c3 iv276_c4

end ErdosComp
