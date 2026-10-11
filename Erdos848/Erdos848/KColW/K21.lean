import Erdos848.ColW.Roots
import Erdos848.ColW.W21
import Erdos848.ColW.W20

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win21_ok : winCheck winX20 winX21 rootsW ckT20 ckCnt20 ckLast20 winOps21 ckT21 ckCnt21 ckLast21 = true := by
  decide +kernel

end ErdosComp
