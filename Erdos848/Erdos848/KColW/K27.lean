import Erdos848.ColW.Roots
import Erdos848.ColW.W27
import Erdos848.ColW.W26

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win27_ok : winCheck winX26 winX27 rootsW ckT26 ckCnt26 ckLast26 winOps27 ckT27 ckCnt27 ckLast27 = true := by
  decide +kernel

end ErdosComp
