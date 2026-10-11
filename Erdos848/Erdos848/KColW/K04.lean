import Erdos848.ColW.Roots
import Erdos848.ColW.W04
import Erdos848.ColW.W03

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win4_ok : winCheck winX3 winX4 rootsW ckT3 ckCnt3 ckLast3 winOps4 ckT4 ckCnt4 ckLast4 = true := by
  decide +kernel

end ErdosComp
