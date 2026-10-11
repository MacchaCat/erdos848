import Erdos848.ColW.Roots
import Erdos848.ColW.W18
import Erdos848.ColW.W17

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win18_ok : winCheck winX17 winX18 rootsW ckT17 ckCnt17 ckLast17 winOps18 ckT18 ckCnt18 ckLast18 = true := by
  decide +kernel

end ErdosComp
