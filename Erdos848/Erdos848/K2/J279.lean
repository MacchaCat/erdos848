import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv279_c0 : below iv279.lo (caseIbQ (lookDT treeK) strsAll iv279.hi (iv279.p.getD 0 dPrm) (iv279.d.getD 0 [])) = true := by
  decide +kernel

theorem iv279_c1 : below iv279.lo (caseIIQ (lookDT treeK) admPre strsAll iv279.hi (iv279.p.getD 1 dPrm) (iv279.d.getD 1 [])) = true := by
  decide +kernel

theorem iv279_c2 : below iv279.lo (caseIII1Q (lookDT treeK) admPre strsAll iv279.hi (iv279.p.getD 2 dPrm) (iv279.d.getD 2 [])) = true := by
  decide +kernel

theorem iv279_c3 : below iv279.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv279.hi (iv279.p.getD 3 dPrm) (iv279.d.getD 3 [])) = true := by
  decide +kernel

theorem iv279_c4 : below iv279.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv279.hi (iv279.p.getD 4 dPrm) (iv279.d.getD 4 []) (iv279.d.getD 5 [])) = true := by
  decide +kernel

theorem iv279_ok : checkIv2 (lookDT treeK) admPre strsAll iv279 = true :=
  checkIv2_of_cases _ _ _ iv279 rfl rfl (by decide +kernel) iv279_c0 iv279_c1 iv279_c2 iv279_c3 iv279_c4

end ErdosComp
