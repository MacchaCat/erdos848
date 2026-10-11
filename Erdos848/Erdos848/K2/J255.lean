import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv255_c0 : below iv255.lo (caseIbQ (lookDT treeK) strsAll iv255.hi (iv255.p.getD 0 dPrm) (iv255.d.getD 0 [])) = true := by
  decide +kernel

theorem iv255_c1 : below iv255.lo (caseIIQ (lookDT treeK) admPre strsAll iv255.hi (iv255.p.getD 1 dPrm) (iv255.d.getD 1 [])) = true := by
  decide +kernel

theorem iv255_c2 : below iv255.lo (caseIII1Q (lookDT treeK) admPre strsAll iv255.hi (iv255.p.getD 2 dPrm) (iv255.d.getD 2 [])) = true := by
  decide +kernel

theorem iv255_c3 : below iv255.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv255.hi (iv255.p.getD 3 dPrm) (iv255.d.getD 3 [])) = true := by
  decide +kernel

theorem iv255_c4 : below iv255.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv255.hi (iv255.p.getD 4 dPrm) (iv255.d.getD 4 []) (iv255.d.getD 5 [])) = true := by
  decide +kernel

theorem iv255_ok : checkIv2 (lookDT treeK) admPre strsAll iv255 = true :=
  checkIv2_of_cases _ _ _ iv255 rfl rfl (by decide +kernel) iv255_c0 iv255_c1 iv255_c2 iv255_c3 iv255_c4

end ErdosComp
