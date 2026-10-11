import Erdos848.ColW.Roots
import Erdos848.ColW.W15
import Erdos848.ColW.W14

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win15_ok : winCheck winX14 winX15 rootsW ckT14 ckCnt14 ckLast14 winOps15 ckT15 ckCnt15 ckLast15 = true := by
  decide +kernel

end ErdosComp
