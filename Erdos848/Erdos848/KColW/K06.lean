import Erdos848.ColW.Roots
import Erdos848.ColW.W06
import Erdos848.ColW.W05

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win6_ok : winCheck winX5 winX6 rootsW ckT5 ckCnt5 ckLast5 winOps6 ckT6 ckCnt6 ckLast6 = true := by
  decide +kernel

end ErdosComp
