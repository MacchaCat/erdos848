import Erdos848.ColW.Roots
import Erdos848.ColW.W16
import Erdos848.ColW.W15

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win16_ok : winCheck winX15 winX16 rootsW ckT15 ckCnt15 ckLast15 winOps16 ckT16 ckCnt16 ckLast16 = true := by
  decide +kernel

end ErdosComp
