import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv103_c0 : below iv103.lo (caseIbQ (lookDT treeK) strsAll iv103.hi (iv103.p.getD 0 dPrm) (iv103.d.getD 0 [])) = true := by
  decide +kernel

theorem iv103_c1 : below iv103.lo (caseIIQ (lookDT treeK) admPre strsAll iv103.hi (iv103.p.getD 1 dPrm) (iv103.d.getD 1 [])) = true := by
  decide +kernel

theorem iv103_c2 : below iv103.lo (caseIII1Q (lookDT treeK) admPre strsAll iv103.hi (iv103.p.getD 2 dPrm) (iv103.d.getD 2 [])) = true := by
  decide +kernel

theorem iv103_c3 : below iv103.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv103.hi (iv103.p.getD 3 dPrm) (iv103.d.getD 3 [])) = true := by
  decide +kernel

theorem iv103_c4 : below iv103.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv103.hi (iv103.p.getD 4 dPrm) (iv103.d.getD 4 []) (iv103.d.getD 5 [])) = true := by
  decide +kernel

theorem iv103_ok : checkIv2 (lookDT treeK) admPre strsAll iv103 = true :=
  checkIv2_of_cases _ _ _ iv103 rfl rfl (by decide +kernel) iv103_c0 iv103_c1 iv103_c2 iv103_c3 iv103_c4

end ErdosComp
