import Erdos848.ColW.Roots
import Erdos848.ColW.W35
import Erdos848.ColW.W34

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win35_ok : winCheck winX34 winX35 rootsW ckT34 ckCnt34 ckLast34 winOps35 ckT35 ckCnt35 ckLast35 = true := by
  decide +kernel

end ErdosComp
