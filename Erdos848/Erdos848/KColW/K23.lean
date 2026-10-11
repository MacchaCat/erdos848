import Erdos848.ColW.Roots
import Erdos848.ColW.W23
import Erdos848.ColW.W22

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win23_ok : winCheck winX22 winX23 rootsW ckT22 ckCnt22 ckLast22 winOps23 ckT23 ckCnt23 ckLast23 = true := by
  decide +kernel

end ErdosComp
