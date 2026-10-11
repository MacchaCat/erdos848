import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv278_c0 : below iv278.lo (caseIbQ (lookDT treeK) strsAll iv278.hi (iv278.p.getD 0 dPrm) (iv278.d.getD 0 [])) = true := by
  decide +kernel

theorem iv278_c1 : below iv278.lo (caseIIQ (lookDT treeK) admPre strsAll iv278.hi (iv278.p.getD 1 dPrm) (iv278.d.getD 1 [])) = true := by
  decide +kernel

theorem iv278_c2 : below iv278.lo (caseIII1Q (lookDT treeK) admPre strsAll iv278.hi (iv278.p.getD 2 dPrm) (iv278.d.getD 2 [])) = true := by
  decide +kernel

theorem iv278_c3 : below iv278.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv278.hi (iv278.p.getD 3 dPrm) (iv278.d.getD 3 [])) = true := by
  decide +kernel

theorem iv278_c4 : below iv278.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv278.hi (iv278.p.getD 4 dPrm) (iv278.d.getD 4 []) (iv278.d.getD 5 [])) = true := by
  decide +kernel

theorem iv278_ok : checkIv2 (lookDT treeK) admPre strsAll iv278 = true :=
  checkIv2_of_cases _ _ _ iv278 rfl rfl (by decide +kernel) iv278_c0 iv278_c1 iv278_c2 iv278_c3 iv278_c4

end ErdosComp
