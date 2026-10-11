import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv211_c0 : below iv211.lo (caseIbQ (lookDT treeK) strsAll iv211.hi (iv211.p.getD 0 dPrm) (iv211.d.getD 0 [])) = true := by
  decide +kernel

theorem iv211_c1 : below iv211.lo (caseIIQ (lookDT treeK) admPre strsAll iv211.hi (iv211.p.getD 1 dPrm) (iv211.d.getD 1 [])) = true := by
  decide +kernel

theorem iv211_c2 : below iv211.lo (caseIII1Q (lookDT treeK) admPre strsAll iv211.hi (iv211.p.getD 2 dPrm) (iv211.d.getD 2 [])) = true := by
  decide +kernel

theorem iv211_c3 : below iv211.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv211.hi (iv211.p.getD 3 dPrm) (iv211.d.getD 3 [])) = true := by
  decide +kernel

theorem iv211_c4 : below iv211.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv211.hi (iv211.p.getD 4 dPrm) (iv211.d.getD 4 []) (iv211.d.getD 5 [])) = true := by
  decide +kernel

theorem iv211_ok : checkIv2 (lookDT treeK) admPre strsAll iv211 = true :=
  checkIv2_of_cases _ _ _ iv211 rfl rfl (by decide +kernel) iv211_c0 iv211_c1 iv211_c2 iv211_c3 iv211_c4

end ErdosComp
