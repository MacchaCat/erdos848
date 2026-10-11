import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv203_c0 : below iv203.lo (caseIbQ (lookDT treeK) strsAll iv203.hi (iv203.p.getD 0 dPrm) (iv203.d.getD 0 [])) = true := by
  decide +kernel

theorem iv203_c1 : below iv203.lo (caseIIQ (lookDT treeK) admPre strsAll iv203.hi (iv203.p.getD 1 dPrm) (iv203.d.getD 1 [])) = true := by
  decide +kernel

theorem iv203_c2 : below iv203.lo (caseIII1Q (lookDT treeK) admPre strsAll iv203.hi (iv203.p.getD 2 dPrm) (iv203.d.getD 2 [])) = true := by
  decide +kernel

theorem iv203_c3 : below iv203.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv203.hi (iv203.p.getD 3 dPrm) (iv203.d.getD 3 [])) = true := by
  decide +kernel

theorem iv203_c4 : below iv203.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv203.hi (iv203.p.getD 4 dPrm) (iv203.d.getD 4 []) (iv203.d.getD 5 [])) = true := by
  decide +kernel

theorem iv203_ok : checkIv2 (lookDT treeK) admPre strsAll iv203 = true :=
  checkIv2_of_cases _ _ _ iv203 rfl rfl (by decide +kernel) iv203_c0 iv203_c1 iv203_c2 iv203_c3 iv203_c4

end ErdosComp
