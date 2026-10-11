import Erdos848.ColW.Roots
import Erdos848.ColW.W05
import Erdos848.ColW.W04

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win5_ok : winCheck winX4 winX5 rootsW ckT4 ckCnt4 ckLast4 winOps5 ckT5 ckCnt5 ckLast5 = true := by
  decide +kernel

end ErdosComp
