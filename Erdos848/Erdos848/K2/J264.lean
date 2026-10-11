import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv264_c0 : below iv264.lo (caseIbQ (lookDT treeK) strsAll iv264.hi (iv264.p.getD 0 dPrm) (iv264.d.getD 0 [])) = true := by
  decide +kernel

theorem iv264_c1 : below iv264.lo (caseIIQ (lookDT treeK) admPre strsAll iv264.hi (iv264.p.getD 1 dPrm) (iv264.d.getD 1 [])) = true := by
  decide +kernel

theorem iv264_c2 : below iv264.lo (caseIII1Q (lookDT treeK) admPre strsAll iv264.hi (iv264.p.getD 2 dPrm) (iv264.d.getD 2 [])) = true := by
  decide +kernel

theorem iv264_c3 : below iv264.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv264.hi (iv264.p.getD 3 dPrm) (iv264.d.getD 3 [])) = true := by
  decide +kernel

theorem iv264_c4 : below iv264.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv264.hi (iv264.p.getD 4 dPrm) (iv264.d.getD 4 []) (iv264.d.getD 5 [])) = true := by
  decide +kernel

theorem iv264_ok : checkIv2 (lookDT treeK) admPre strsAll iv264 = true :=
  checkIv2_of_cases _ _ _ iv264 rfl rfl (by decide +kernel) iv264_c0 iv264_c1 iv264_c2 iv264_c3 iv264_c4

end ErdosComp
