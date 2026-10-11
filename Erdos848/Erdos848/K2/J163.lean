import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv163_c0 : below iv163.lo (caseIbQ (lookDT treeK) strsAll iv163.hi (iv163.p.getD 0 dPrm) (iv163.d.getD 0 [])) = true := by
  decide +kernel

theorem iv163_c1 : below iv163.lo (caseIIQ (lookDT treeK) admPre strsAll iv163.hi (iv163.p.getD 1 dPrm) (iv163.d.getD 1 [])) = true := by
  decide +kernel

theorem iv163_c2 : below iv163.lo (caseIII1Q (lookDT treeK) admPre strsAll iv163.hi (iv163.p.getD 2 dPrm) (iv163.d.getD 2 [])) = true := by
  decide +kernel

theorem iv163_c3 : below iv163.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv163.hi (iv163.p.getD 3 dPrm) (iv163.d.getD 3 [])) = true := by
  decide +kernel

theorem iv163_c4 : below iv163.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv163.hi (iv163.p.getD 4 dPrm) (iv163.d.getD 4 []) (iv163.d.getD 5 [])) = true := by
  decide +kernel

theorem iv163_ok : checkIv2 (lookDT treeK) admPre strsAll iv163 = true :=
  checkIv2_of_cases _ _ _ iv163 rfl rfl (by decide +kernel) iv163_c0 iv163_c1 iv163_c2 iv163_c3 iv163_c4

end ErdosComp
