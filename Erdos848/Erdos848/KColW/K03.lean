import Erdos848.ColW.Roots
import Erdos848.ColW.W03
import Erdos848.ColW.W02

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win3_ok : winCheck winX2 winX3 rootsW ckT2 ckCnt2 ckLast2 winOps3 ckT3 ckCnt3 ckLast3 = true := by
  decide +kernel

end ErdosComp
