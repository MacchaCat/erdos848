import Erdos848.ColW.Roots
import Erdos848.ColW.W10
import Erdos848.ColW.W09

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win10_ok : winCheck winX9 winX10 rootsW ckT9 ckCnt9 ckLast9 winOps10 ckT10 ckCnt10 ckLast10 = true := by
  decide +kernel

end ErdosComp
