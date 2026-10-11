import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv166_c0 : below iv166.lo (caseIbQ (lookDT treeK) strsAll iv166.hi (iv166.p.getD 0 dPrm) (iv166.d.getD 0 [])) = true := by
  decide +kernel

theorem iv166_c1 : below iv166.lo (caseIIQ (lookDT treeK) admPre strsAll iv166.hi (iv166.p.getD 1 dPrm) (iv166.d.getD 1 [])) = true := by
  decide +kernel

theorem iv166_c2 : below iv166.lo (caseIII1Q (lookDT treeK) admPre strsAll iv166.hi (iv166.p.getD 2 dPrm) (iv166.d.getD 2 [])) = true := by
  decide +kernel

theorem iv166_c3 : below iv166.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv166.hi (iv166.p.getD 3 dPrm) (iv166.d.getD 3 [])) = true := by
  decide +kernel

theorem iv166_c4 : below iv166.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv166.hi (iv166.p.getD 4 dPrm) (iv166.d.getD 4 []) (iv166.d.getD 5 [])) = true := by
  decide +kernel

theorem iv166_ok : checkIv2 (lookDT treeK) admPre strsAll iv166 = true :=
  checkIv2_of_cases _ _ _ iv166 rfl rfl (by decide +kernel) iv166_c0 iv166_c1 iv166_c2 iv166_c3 iv166_c4

end ErdosComp
