import Erdos848.ColW.Roots
import Erdos848.ColW.W09
import Erdos848.ColW.W08

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win9_ok : winCheck winX8 winX9 rootsW ckT8 ckCnt8 ckLast8 winOps9 ckT9 ckCnt9 ckLast9 = true := by
  decide +kernel

end ErdosComp
