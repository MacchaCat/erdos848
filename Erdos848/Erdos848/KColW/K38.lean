import Erdos848.ColW.Roots
import Erdos848.ColW.W38
import Erdos848.ColW.W37

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win38_ok : winCheck winX37 winX38 rootsW ckT37 ckCnt37 ckLast37 winOps38 ckT38 ckCnt38 ckLast38 = true := by
  decide +kernel

end ErdosComp
