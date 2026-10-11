import Erdos848.RootsAppend
import Erdos848.ColW.Roots

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option linter.style.longLine false

theorem rootsSeg0 : rootsGo 17657 4415 5 rootsW0 = true := by decide +kernel

theorem rootsSeg1 : rootsGo 38153 5125 17661 rootsW1 = true := by decide +kernel

theorem rootsSeg2 : rootsGo 59509 5340 38157 rootsW2 = true := by decide +kernel

theorem rootsSeg3 : rootsGo 82073 5642 59513 rootsW3 = true := by decide +kernel

theorem rootsSeg4 : rootsGo 105269 5800 82077 rootsW4 = true := by decide +kernel

theorem rootsSeg5 : rootsGo 128861 5899 105273 rootsW5 = true := by decide +kernel

theorem rootsSeg6 : rootsGo 152093 5809 128865 rootsW6 = true := by decide +kernel

theorem rootsSeg7 : rootsGo 176369 6070 152097 rootsW7 = true := by decide +kernel

theorem rootsSeg8 : rootsGo 200569 6051 176373 rootsW8 = true := by decide +kernel

theorem rootsSeg9 : rootsGo 225217 6163 200573 rootsW9 = true := by decide +kernel

theorem rootsSeg10 : rootsGo 250057 6211 225221 rootsW10 = true := by decide +kernel

theorem rootsSeg11 : rootsGo 275129 6269 250061 rootsW11 = true := by decide +kernel

theorem rootsSeg12 : rootsGo 300569 6361 275133 rootsW12 = true := by decide +kernel

theorem rootsSeg13 : rootsGo 325769 6301 300573 rootsW13 = true := by decide +kernel

theorem rootsSeg14 : rootsGo 351413 6412 325773 rootsW14 = true := by decide +kernel

theorem rootsSeg15 : rootsGo 376841 6358 351417 rootsW15 = true := by decide +kernel

theorem rootsSeg16 : rootsGo 402949 6528 376845 rootsW16 = true := by decide +kernel

theorem rootsSeg17 : rootsGo 428801 6464 402953 rootsW17 = true := by decide +kernel

theorem rootsSeg18 : rootsGo 454637 6460 428805 rootsW18 = true := by decide +kernel

theorem rootsSeg19 : rootsGo 480941 6577 454641 rootsW19 = true := by decide +kernel

theorem rootsSeg20 : rootsGo 507193 6564 480945 rootsW20 = true := by decide +kernel

theorem rootsSeg21 : rootsGo 532949 6440 507197 rootsW21 = true := by decide +kernel

theorem rootsSeg22 : rootsGo 559913 6742 532953 rootsW22 = true := by decide +kernel

theorem rootsSeg23 : rootsGo 586009 6525 559917 rootsW23 = true := by decide +kernel

theorem rootsSeg24 : rootsGo 612173 6542 586013 rootsW24 = true := by decide +kernel

theorem rootsSeg25 : rootsGo 639329 6790 612177 rootsW25 = true := by decide +kernel

theorem rootsSeg26 : rootsGo 666041 6679 639333 rootsW26 = true := by decide +kernel

theorem rootsSeg27 : rootsGo 693097 6765 666045 rootsW27 = true := by decide +kernel

theorem rootsSeg28 : rootsGo 720361 6817 693101 rootsW28 = true := by decide +kernel

theorem rootsSeg29 : rootsGo 747869 6878 720365 rootsW29 = true := by decide +kernel

theorem rootsSeg30 : rootsGo 775513 6912 747873 rootsW30 = true := by decide +kernel

theorem rootsSeg31 : rootsGo 802177 6667 775517 rootsW31 = true := by decide +kernel

theorem rootsSeg32 : rootsGo 829069 6724 802181 rootsW32 = true := by decide +kernel

theorem rootsSeg33 : rootsGo 856553 6872 829073 rootsW33 = true := by decide +kernel

theorem rootsSeg34 : rootsGo 883537 6747 856557 rootsW34 = true := by decide +kernel

theorem rootsSeg35 : rootsGo 911129 6899 883541 rootsW35 = true := by decide +kernel

theorem rootsSeg36 : rootsGo 939121 6999 911133 rootsW36 = true := by decide +kernel

theorem rootsSeg37 : rootsGo 966661 6886 939125 rootsW37 = true := by decide +kernel

theorem rootsTail38 : rootsGo 986746 5023 966665 rootsW38 = true := by decide +kernel

theorem rootsTail37 : rootsGo 986746 11908 939125 (rootsW37 ++ (rootsW38)) = true :=
  Erdos848.rootsGo_append 986746 966661 966665 5023 _ rootsTail38 (by norm_num) (by norm_num)
    (by norm_num) 6885 939125 6886 rootsW37 (by norm_num) (by norm_num) rootsSeg37

theorem rootsTail36 : rootsGo 986746 18906 911133 (rootsW36 ++ (rootsW37 ++ (rootsW38))) = true :=
  Erdos848.rootsGo_append 986746 939121 939125 11908 _ rootsTail37 (by norm_num) (by norm_num)
    (by norm_num) 6998 911133 6999 rootsW36 (by norm_num) (by norm_num) rootsSeg36

theorem rootsTail35 : rootsGo 986746 25804 883541 (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))) = true :=
  Erdos848.rootsGo_append 986746 911129 911133 18906 _ rootsTail36 (by norm_num) (by norm_num)
    (by norm_num) 6898 883541 6899 rootsW35 (by norm_num) (by norm_num) rootsSeg35

theorem rootsTail34 : rootsGo 986746 32550 856557 (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))) = true :=
  Erdos848.rootsGo_append 986746 883537 883541 25804 _ rootsTail35 (by norm_num) (by norm_num)
    (by norm_num) 6746 856557 6747 rootsW34 (by norm_num) (by norm_num) rootsSeg34

theorem rootsTail33 : rootsGo 986746 39421 829073 (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))) = true :=
  Erdos848.rootsGo_append 986746 856553 856557 32550 _ rootsTail34 (by norm_num) (by norm_num)
    (by norm_num) 6871 829073 6872 rootsW33 (by norm_num) (by norm_num) rootsSeg33

theorem rootsTail32 : rootsGo 986746 46144 802181 (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))) = true :=
  Erdos848.rootsGo_append 986746 829069 829073 39421 _ rootsTail33 (by norm_num) (by norm_num)
    (by norm_num) 6723 802181 6724 rootsW32 (by norm_num) (by norm_num) rootsSeg32

theorem rootsTail31 : rootsGo 986746 52810 775517 (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))) = true :=
  Erdos848.rootsGo_append 986746 802177 802181 46144 _ rootsTail32 (by norm_num) (by norm_num)
    (by norm_num) 6666 775517 6667 rootsW31 (by norm_num) (by norm_num) rootsSeg31

theorem rootsTail30 : rootsGo 986746 59721 747873 (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))) = true :=
  Erdos848.rootsGo_append 986746 775513 775517 52810 _ rootsTail31 (by norm_num) (by norm_num)
    (by norm_num) 6911 747873 6912 rootsW30 (by norm_num) (by norm_num) rootsSeg30

theorem rootsTail29 : rootsGo 986746 66598 720365 (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))) = true :=
  Erdos848.rootsGo_append 986746 747869 747873 59721 _ rootsTail30 (by norm_num) (by norm_num)
    (by norm_num) 6877 720365 6878 rootsW29 (by norm_num) (by norm_num) rootsSeg29

theorem rootsTail28 : rootsGo 986746 73414 693101 (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))) = true :=
  Erdos848.rootsGo_append 986746 720361 720365 66598 _ rootsTail29 (by norm_num) (by norm_num)
    (by norm_num) 6816 693101 6817 rootsW28 (by norm_num) (by norm_num) rootsSeg28

theorem rootsTail27 : rootsGo 986746 80178 666045 (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))) = true :=
  Erdos848.rootsGo_append 986746 693097 693101 73414 _ rootsTail28 (by norm_num) (by norm_num)
    (by norm_num) 6764 666045 6765 rootsW27 (by norm_num) (by norm_num) rootsSeg27

theorem rootsTail26 : rootsGo 986746 86856 639333 (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 666041 666045 80178 _ rootsTail27 (by norm_num) (by norm_num)
    (by norm_num) 6678 639333 6679 rootsW26 (by norm_num) (by norm_num) rootsSeg26

theorem rootsTail25 : rootsGo 986746 93645 612177 (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 639329 639333 86856 _ rootsTail26 (by norm_num) (by norm_num)
    (by norm_num) 6789 612177 6790 rootsW25 (by norm_num) (by norm_num) rootsSeg25

theorem rootsTail24 : rootsGo 986746 100186 586013 (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 612173 612177 93645 _ rootsTail25 (by norm_num) (by norm_num)
    (by norm_num) 6541 586013 6542 rootsW24 (by norm_num) (by norm_num) rootsSeg24

theorem rootsTail23 : rootsGo 986746 106710 559917 (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 586009 586013 100186 _ rootsTail24 (by norm_num) (by norm_num)
    (by norm_num) 6524 559917 6525 rootsW23 (by norm_num) (by norm_num) rootsSeg23

theorem rootsTail22 : rootsGo 986746 113451 532953 (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 559913 559917 106710 _ rootsTail23 (by norm_num) (by norm_num)
    (by norm_num) 6741 532953 6742 rootsW22 (by norm_num) (by norm_num) rootsSeg22

theorem rootsTail21 : rootsGo 986746 119890 507197 (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 532949 532953 113451 _ rootsTail22 (by norm_num) (by norm_num)
    (by norm_num) 6439 507197 6440 rootsW21 (by norm_num) (by norm_num) rootsSeg21

theorem rootsTail20 : rootsGo 986746 126453 480945 (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 507193 507197 119890 _ rootsTail21 (by norm_num) (by norm_num)
    (by norm_num) 6563 480945 6564 rootsW20 (by norm_num) (by norm_num) rootsSeg20

theorem rootsTail19 : rootsGo 986746 133029 454641 (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 480941 480945 126453 _ rootsTail20 (by norm_num) (by norm_num)
    (by norm_num) 6576 454641 6577 rootsW19 (by norm_num) (by norm_num) rootsSeg19

theorem rootsTail18 : rootsGo 986746 139488 428805 (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 454637 454641 133029 _ rootsTail19 (by norm_num) (by norm_num)
    (by norm_num) 6459 428805 6460 rootsW18 (by norm_num) (by norm_num) rootsSeg18

theorem rootsTail17 : rootsGo 986746 145951 402953 (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 428801 428805 139488 _ rootsTail18 (by norm_num) (by norm_num)
    (by norm_num) 6463 402953 6464 rootsW17 (by norm_num) (by norm_num) rootsSeg17

theorem rootsTail16 : rootsGo 986746 152478 376845 (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 402949 402953 145951 _ rootsTail17 (by norm_num) (by norm_num)
    (by norm_num) 6527 376845 6528 rootsW16 (by norm_num) (by norm_num) rootsSeg16

theorem rootsTail15 : rootsGo 986746 158835 351417 (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 376841 376845 152478 _ rootsTail16 (by norm_num) (by norm_num)
    (by norm_num) 6357 351417 6358 rootsW15 (by norm_num) (by norm_num) rootsSeg15

theorem rootsTail14 : rootsGo 986746 165246 325773 (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 351413 351417 158835 _ rootsTail15 (by norm_num) (by norm_num)
    (by norm_num) 6411 325773 6412 rootsW14 (by norm_num) (by norm_num) rootsSeg14

theorem rootsTail13 : rootsGo 986746 171546 300573 (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 325769 325773 165246 _ rootsTail14 (by norm_num) (by norm_num)
    (by norm_num) 6300 300573 6301 rootsW13 (by norm_num) (by norm_num) rootsSeg13

theorem rootsTail12 : rootsGo 986746 177906 275133 (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 300569 300573 171546 _ rootsTail13 (by norm_num) (by norm_num)
    (by norm_num) 6360 275133 6361 rootsW12 (by norm_num) (by norm_num) rootsSeg12

theorem rootsTail11 : rootsGo 986746 184174 250061 (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 275129 275133 177906 _ rootsTail12 (by norm_num) (by norm_num)
    (by norm_num) 6268 250061 6269 rootsW11 (by norm_num) (by norm_num) rootsSeg11

theorem rootsTail10 : rootsGo 986746 190384 225221 (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 250057 250061 184174 _ rootsTail11 (by norm_num) (by norm_num)
    (by norm_num) 6210 225221 6211 rootsW10 (by norm_num) (by norm_num) rootsSeg10

theorem rootsTail9 : rootsGo 986746 196546 200573 (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 225217 225221 190384 _ rootsTail10 (by norm_num) (by norm_num)
    (by norm_num) 6162 200573 6163 rootsW9 (by norm_num) (by norm_num) rootsSeg9

theorem rootsTail8 : rootsGo 986746 202596 176373 (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 200569 200573 196546 _ rootsTail9 (by norm_num) (by norm_num)
    (by norm_num) 6050 176373 6051 rootsW8 (by norm_num) (by norm_num) rootsSeg8

theorem rootsTail7 : rootsGo 986746 208665 152097 (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 176369 176373 202596 _ rootsTail8 (by norm_num) (by norm_num)
    (by norm_num) 6069 152097 6070 rootsW7 (by norm_num) (by norm_num) rootsSeg7

theorem rootsTail6 : rootsGo 986746 214473 128865 (rootsW6 ++ (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 152093 152097 208665 _ rootsTail7 (by norm_num) (by norm_num)
    (by norm_num) 5808 128865 5809 rootsW6 (by norm_num) (by norm_num) rootsSeg6

theorem rootsTail5 : rootsGo 986746 220371 105273 (rootsW5 ++ (rootsW6 ++ (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 128861 128865 214473 _ rootsTail6 (by norm_num) (by norm_num)
    (by norm_num) 5898 105273 5899 rootsW5 (by norm_num) (by norm_num) rootsSeg5

theorem rootsTail4 : rootsGo 986746 226170 82077 (rootsW4 ++ (rootsW5 ++ (rootsW6 ++ (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 105269 105273 220371 _ rootsTail5 (by norm_num) (by norm_num)
    (by norm_num) 5799 82077 5800 rootsW4 (by norm_num) (by norm_num) rootsSeg4

theorem rootsTail3 : rootsGo 986746 231811 59513 (rootsW3 ++ (rootsW4 ++ (rootsW5 ++ (rootsW6 ++ (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 82073 82077 226170 _ rootsTail4 (by norm_num) (by norm_num)
    (by norm_num) 5641 59513 5642 rootsW3 (by norm_num) (by norm_num) rootsSeg3

theorem rootsTail2 : rootsGo 986746 237150 38157 (rootsW2 ++ (rootsW3 ++ (rootsW4 ++ (rootsW5 ++ (rootsW6 ++ (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 59509 59513 231811 _ rootsTail3 (by norm_num) (by norm_num)
    (by norm_num) 5339 38157 5340 rootsW2 (by norm_num) (by norm_num) rootsSeg2

theorem rootsTail1 : rootsGo 986746 242274 17661 (rootsW1 ++ (rootsW2 ++ (rootsW3 ++ (rootsW4 ++ (rootsW5 ++ (rootsW6 ++ (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38)))))))))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 38153 38157 237150 _ rootsTail2 (by norm_num) (by norm_num)
    (by norm_num) 5124 17661 5125 rootsW1 (by norm_num) (by norm_num) rootsSeg1

theorem rootsTail0 : rootsGo 986746 246688 5 (rootsW0 ++ (rootsW1 ++ (rootsW2 ++ (rootsW3 ++ (rootsW4 ++ (rootsW5 ++ (rootsW6 ++ (rootsW7 ++ (rootsW8 ++ (rootsW9 ++ (rootsW10 ++ (rootsW11 ++ (rootsW12 ++ (rootsW13 ++ (rootsW14 ++ (rootsW15 ++ (rootsW16 ++ (rootsW17 ++ (rootsW18 ++ (rootsW19 ++ (rootsW20 ++ (rootsW21 ++ (rootsW22 ++ (rootsW23 ++ (rootsW24 ++ (rootsW25 ++ (rootsW26 ++ (rootsW27 ++ (rootsW28 ++ (rootsW29 ++ (rootsW30 ++ (rootsW31 ++ (rootsW32 ++ (rootsW33 ++ (rootsW34 ++ (rootsW35 ++ (rootsW36 ++ (rootsW37 ++ (rootsW38))))))))))))))))))))))))))))))))))))))) = true :=
  Erdos848.rootsGo_append 986746 17657 17661 242274 _ rootsTail1 (by norm_num) (by norm_num)
    (by norm_num) 4414 5 4415 rootsW0 (by norm_num) (by norm_num) rootsSeg0

theorem rootsW_ok : rootsOK 986746 rootsW = true := by
  unfold rootsOK
  rw [Bool.and_eq_true]
  exact ⟨by decide, rootsTail0⟩

end ErdosComp
