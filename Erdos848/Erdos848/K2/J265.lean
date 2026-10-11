import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv265_c0 : below iv265.lo (caseIbQ (lookDT treeK) strsAll iv265.hi (iv265.p.getD 0 dPrm) (iv265.d.getD 0 [])) = true := by
  decide +kernel

theorem iv265_c1 : below iv265.lo (caseIIQ (lookDT treeK) admPre strsAll iv265.hi (iv265.p.getD 1 dPrm) (iv265.d.getD 1 [])) = true := by
  decide +kernel

theorem iv265_c2 : below iv265.lo (caseIII1Q (lookDT treeK) admPre strsAll iv265.hi (iv265.p.getD 2 dPrm) (iv265.d.getD 2 [])) = true := by
  decide +kernel

theorem iv265_c3 : below iv265.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv265.hi (iv265.p.getD 3 dPrm) (iv265.d.getD 3 [])) = true := by
  decide +kernel

theorem iv265_c4 : below iv265.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv265.hi (iv265.p.getD 4 dPrm) (iv265.d.getD 4 []) (iv265.d.getD 5 [])) = true := by
  decide +kernel

theorem iv265_ok : checkIv2 (lookDT treeK) admPre strsAll iv265 = true :=
  checkIv2_of_cases _ _ _ iv265 rfl rfl (by decide +kernel) iv265_c0 iv265_c1 iv265_c2 iv265_c3 iv265_c4

end ErdosComp
