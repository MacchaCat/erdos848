import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv206_c0 : below iv206.lo (caseIbQ (lookDT treeK) strsAll iv206.hi (iv206.p.getD 0 dPrm) (iv206.d.getD 0 [])) = true := by
  decide +kernel

theorem iv206_c1 : below iv206.lo (caseIIQ (lookDT treeK) admPre strsAll iv206.hi (iv206.p.getD 1 dPrm) (iv206.d.getD 1 [])) = true := by
  decide +kernel

theorem iv206_c2 : below iv206.lo (caseIII1Q (lookDT treeK) admPre strsAll iv206.hi (iv206.p.getD 2 dPrm) (iv206.d.getD 2 [])) = true := by
  decide +kernel

theorem iv206_c3 : below iv206.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv206.hi (iv206.p.getD 3 dPrm) (iv206.d.getD 3 [])) = true := by
  decide +kernel

theorem iv206_c4 : below iv206.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv206.hi (iv206.p.getD 4 dPrm) (iv206.d.getD 4 []) (iv206.d.getD 5 [])) = true := by
  decide +kernel

theorem iv206_ok : checkIv2 (lookDT treeK) admPre strsAll iv206 = true :=
  checkIv2_of_cases _ _ _ iv206 rfl rfl (by decide +kernel) iv206_c0 iv206_c1 iv206_c2 iv206_c3 iv206_c4

end ErdosComp
