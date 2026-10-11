import Erdos848.ColW.Roots
import Erdos848.ColW.W25
import Erdos848.ColW.W24

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win25_ok : winCheck winX24 winX25 rootsW ckT24 ckCnt24 ckLast24 winOps25 ckT25 ckCnt25 ckLast25 = true := by
  decide +kernel

end ErdosComp
