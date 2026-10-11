import Erdos848.ColW.Roots
import Erdos848.ColW.W01
import Erdos848.ColW.W00

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win1_ok : winCheck winX0 winX1 rootsW ckT0 ckCnt0 ckLast0 winOps1 ckT1 ckCnt1 ckLast1 = true := by
  decide +kernel

end ErdosComp
