import Erdos848.ColW.Roots
import Erdos848.ColW.W33
import Erdos848.ColW.W32

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win33_ok : winCheck winX32 winX33 rootsW ckT32 ckCnt32 ckLast32 winOps33 ckT33 ckCnt33 ckLast33 = true := by
  decide +kernel

end ErdosComp
