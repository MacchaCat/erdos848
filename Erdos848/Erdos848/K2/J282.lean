import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv282_c0 : below iv282.lo (caseIbQ (lookDT treeK) strsAll iv282.hi (iv282.p.getD 0 dPrm) (iv282.d.getD 0 [])) = true := by
  decide +kernel

theorem iv282_c1 : below iv282.lo (caseIIQ (lookDT treeK) admPre strsAll iv282.hi (iv282.p.getD 1 dPrm) (iv282.d.getD 1 [])) = true := by
  decide +kernel

theorem iv282_c2 : below iv282.lo (caseIII1Q (lookDT treeK) admPre strsAll iv282.hi (iv282.p.getD 2 dPrm) (iv282.d.getD 2 [])) = true := by
  decide +kernel

theorem iv282_c3 : below iv282.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv282.hi (iv282.p.getD 3 dPrm) (iv282.d.getD 3 [])) = true := by
  decide +kernel

theorem iv282_c4 : below iv282.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv282.hi (iv282.p.getD 4 dPrm) (iv282.d.getD 4 []) (iv282.d.getD 5 [])) = true := by
  decide +kernel

theorem iv282_ok : checkIv2 (lookDT treeK) admPre strsAll iv282 = true :=
  checkIv2_of_cases _ _ _ iv282 rfl rfl (by decide +kernel) iv282_c0 iv282_c1 iv282_c2 iv282_c3 iv282_c4

end ErdosComp
