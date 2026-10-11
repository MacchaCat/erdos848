import Erdos848.ColW.Roots
import Erdos848.ColW.W32
import Erdos848.ColW.W31

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win32_ok : winCheck winX31 winX32 rootsW ckT31 ckCnt31 ckLast31 winOps32 ckT32 ckCnt32 ckLast32 = true := by
  decide +kernel

end ErdosComp
