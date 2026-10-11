import Erdos848.ColW.Roots
import Erdos848.ColW.W17
import Erdos848.ColW.W16

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win17_ok : winCheck winX16 winX17 rootsW ckT16 ckCnt16 ckLast16 winOps17 ckT17 ckCnt17 ckLast17 = true := by
  decide +kernel

end ErdosComp
