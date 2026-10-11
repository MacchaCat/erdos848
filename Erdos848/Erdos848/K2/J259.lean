import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv259_c0 : below iv259.lo (caseIbQ (lookDT treeK) strsAll iv259.hi (iv259.p.getD 0 dPrm) (iv259.d.getD 0 [])) = true := by
  decide +kernel

theorem iv259_c1 : below iv259.lo (caseIIQ (lookDT treeK) admPre strsAll iv259.hi (iv259.p.getD 1 dPrm) (iv259.d.getD 1 [])) = true := by
  decide +kernel

theorem iv259_c2 : below iv259.lo (caseIII1Q (lookDT treeK) admPre strsAll iv259.hi (iv259.p.getD 2 dPrm) (iv259.d.getD 2 [])) = true := by
  decide +kernel

theorem iv259_c3 : below iv259.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv259.hi (iv259.p.getD 3 dPrm) (iv259.d.getD 3 [])) = true := by
  decide +kernel

theorem iv259_c4 : below iv259.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv259.hi (iv259.p.getD 4 dPrm) (iv259.d.getD 4 []) (iv259.d.getD 5 [])) = true := by
  decide +kernel

theorem iv259_ok : checkIv2 (lookDT treeK) admPre strsAll iv259 = true :=
  checkIv2_of_cases _ _ _ iv259 rfl rfl (by decide +kernel) iv259_c0 iv259_c1 iv259_c2 iv259_c3 iv259_c4

end ErdosComp
