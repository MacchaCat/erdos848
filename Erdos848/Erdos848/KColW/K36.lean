import Erdos848.ColW.Roots
import Erdos848.ColW.W36
import Erdos848.ColW.W35

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win36_ok : winCheck winX35 winX36 rootsW ckT35 ckCnt35 ckLast35 winOps36 ckT36 ckCnt36 ckLast36 = true := by
  decide +kernel

end ErdosComp
