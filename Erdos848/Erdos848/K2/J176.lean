import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv176_c0 : below iv176.lo (caseIbQ (lookDT treeK) strsAll iv176.hi (iv176.p.getD 0 dPrm) (iv176.d.getD 0 [])) = true := by
  decide +kernel

theorem iv176_c1 : below iv176.lo (caseIIQ (lookDT treeK) admPre strsAll iv176.hi (iv176.p.getD 1 dPrm) (iv176.d.getD 1 [])) = true := by
  decide +kernel

theorem iv176_c2 : below iv176.lo (caseIII1Q (lookDT treeK) admPre strsAll iv176.hi (iv176.p.getD 2 dPrm) (iv176.d.getD 2 [])) = true := by
  decide +kernel

theorem iv176_c3 : below iv176.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv176.hi (iv176.p.getD 3 dPrm) (iv176.d.getD 3 [])) = true := by
  decide +kernel

theorem iv176_c4 : below iv176.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv176.hi (iv176.p.getD 4 dPrm) (iv176.d.getD 4 []) (iv176.d.getD 5 [])) = true := by
  decide +kernel

theorem iv176_ok : checkIv2 (lookDT treeK) admPre strsAll iv176 = true :=
  checkIv2_of_cases _ _ _ iv176 rfl rfl (by decide +kernel) iv176_c0 iv176_c1 iv176_c2 iv176_c3 iv176_c4

end ErdosComp
