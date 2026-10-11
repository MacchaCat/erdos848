import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv297_c0 : below iv297.lo (caseIbQ (lookDT treeK) strsAll iv297.hi (iv297.p.getD 0 dPrm) (iv297.d.getD 0 [])) = true := by
  decide +kernel

theorem iv297_c1 : below iv297.lo (caseIIQ (lookDT treeK) admPre strsAll iv297.hi (iv297.p.getD 1 dPrm) (iv297.d.getD 1 [])) = true := by
  decide +kernel

theorem iv297_c2 : below iv297.lo (caseIII1Q (lookDT treeK) admPre strsAll iv297.hi (iv297.p.getD 2 dPrm) (iv297.d.getD 2 [])) = true := by
  decide +kernel

theorem iv297_c3 : below iv297.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv297.hi (iv297.p.getD 3 dPrm) (iv297.d.getD 3 [])) = true := by
  decide +kernel

theorem iv297_c4 : below iv297.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv297.hi (iv297.p.getD 4 dPrm) (iv297.d.getD 4 []) (iv297.d.getD 5 [])) = true := by
  decide +kernel

theorem iv297_ok : checkIv2 (lookDT treeK) admPre strsAll iv297 = true :=
  checkIv2_of_cases _ _ _ iv297 rfl rfl (by decide +kernel) iv297_c0 iv297_c1 iv297_c2 iv297_c3 iv297_c4

end ErdosComp
