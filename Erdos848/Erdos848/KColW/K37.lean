import Erdos848.ColW.Roots
import Erdos848.ColW.W37
import Erdos848.ColW.W36

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win37_ok : winCheck winX36 winX37 rootsW ckT36 ckCnt36 ckLast36 winOps37 ckT37 ckCnt37 ckLast37 = true := by
  decide +kernel

end ErdosComp
