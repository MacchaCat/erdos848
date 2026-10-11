import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv205_c0 : below iv205.lo (caseIbQ (lookDT treeK) strsAll iv205.hi (iv205.p.getD 0 dPrm) (iv205.d.getD 0 [])) = true := by
  decide +kernel

theorem iv205_c1 : below iv205.lo (caseIIQ (lookDT treeK) admPre strsAll iv205.hi (iv205.p.getD 1 dPrm) (iv205.d.getD 1 [])) = true := by
  decide +kernel

theorem iv205_c2 : below iv205.lo (caseIII1Q (lookDT treeK) admPre strsAll iv205.hi (iv205.p.getD 2 dPrm) (iv205.d.getD 2 [])) = true := by
  decide +kernel

theorem iv205_c3 : below iv205.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv205.hi (iv205.p.getD 3 dPrm) (iv205.d.getD 3 [])) = true := by
  decide +kernel

theorem iv205_c4 : below iv205.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv205.hi (iv205.p.getD 4 dPrm) (iv205.d.getD 4 []) (iv205.d.getD 5 [])) = true := by
  decide +kernel

theorem iv205_ok : checkIv2 (lookDT treeK) admPre strsAll iv205 = true :=
  checkIv2_of_cases _ _ _ iv205 rfl rfl (by decide +kernel) iv205_c0 iv205_c1 iv205_c2 iv205_c3 iv205_c4

end ErdosComp
