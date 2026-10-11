import Erdos848.ColW.Roots
import Erdos848.ColW.W14
import Erdos848.ColW.W13

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win14_ok : winCheck winX13 winX14 rootsW ckT13 ckCnt13 ckLast13 winOps14 ckT14 ckCnt14 ckLast14 = true := by
  decide +kernel

end ErdosComp
