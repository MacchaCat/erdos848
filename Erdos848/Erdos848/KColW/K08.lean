import Erdos848.ColW.Roots
import Erdos848.ColW.W08
import Erdos848.ColW.W07

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win8_ok : winCheck winX7 winX8 rootsW ckT7 ckCnt7 ckLast7 winOps8 ckT8 ckCnt8 ckLast8 = true := by
  decide +kernel

end ErdosComp
