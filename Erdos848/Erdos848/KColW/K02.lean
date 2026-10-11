import Erdos848.ColW.Roots
import Erdos848.ColW.W02
import Erdos848.ColW.W01

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win2_ok : winCheck winX1 winX2 rootsW ckT1 ckCnt1 ckLast1 winOps2 ckT2 ckCnt2 ckLast2 = true := by
  decide +kernel

end ErdosComp
