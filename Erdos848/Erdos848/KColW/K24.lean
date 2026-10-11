import Erdos848.ColW.Roots
import Erdos848.ColW.W24
import Erdos848.ColW.W23

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win24_ok : winCheck winX23 winX24 rootsW ckT23 ckCnt23 ckLast23 winOps24 ckT24 ckCnt24 ckLast24 = true := by
  decide +kernel

end ErdosComp
