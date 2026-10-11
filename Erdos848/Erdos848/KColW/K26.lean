import Erdos848.ColW.Roots
import Erdos848.ColW.W26
import Erdos848.ColW.W25

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win26_ok : winCheck winX25 winX26 rootsW ckT25 ckCnt25 ckLast25 winOps26 ckT26 ckCnt26 ckLast26 = true := by
  decide +kernel

end ErdosComp
