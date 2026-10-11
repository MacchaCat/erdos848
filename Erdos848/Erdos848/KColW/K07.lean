import Erdos848.ColW.Roots
import Erdos848.ColW.W07
import Erdos848.ColW.W06

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win7_ok : winCheck winX6 winX7 rootsW ckT6 ckCnt6 ckLast6 winOps7 ckT7 ckCnt7 ckLast7 = true := by
  decide +kernel

end ErdosComp
