import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv316_c0 : below iv316.lo (caseIbQ (lookDT treeK) strsAll iv316.hi (iv316.p.getD 0 dPrm) (iv316.d.getD 0 [])) = true := by
  decide +kernel

theorem iv316_c1 : below iv316.lo (caseIIQ (lookDT treeK) admPre strsAll iv316.hi (iv316.p.getD 1 dPrm) (iv316.d.getD 1 [])) = true := by
  decide +kernel

theorem iv316_c2 : below iv316.lo (caseIII1Q (lookDT treeK) admPre strsAll iv316.hi (iv316.p.getD 2 dPrm) (iv316.d.getD 2 [])) = true := by
  decide +kernel

theorem iv316_c3 : below iv316.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv316.hi (iv316.p.getD 3 dPrm) (iv316.d.getD 3 [])) = true := by
  decide +kernel

theorem iv316_c4 : below iv316.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv316.hi (iv316.p.getD 4 dPrm) (iv316.d.getD 4 []) (iv316.d.getD 5 [])) = true := by
  decide +kernel

theorem iv316_ok : checkIv2 (lookDT treeK) admPre strsAll iv316 = true :=
  checkIv2_of_cases _ _ _ iv316 rfl rfl (by decide +kernel) iv316_c0 iv316_c1 iv316_c2 iv316_c3 iv316_c4

end ErdosComp
