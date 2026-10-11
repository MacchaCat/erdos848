import ErdosComp.C2Data
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem admPre_ok0 : admPreOK (admPre0 ++ [7076]) 0 0 = true := by decide +kernel

theorem admPre_ok1 : admPreOK (admPre1 ++ [14138]) 40 7076 = true := by decide +kernel

theorem admPre_ok2 : admPreOK (admPre2 ++ [21199]) 80 14138 = true := by decide +kernel

theorem admPre_ok3 : admPreOK (admPre3 ++ [28262]) 120 21199 = true := by decide +kernel

theorem admPre_ok4 : admPreOK (admPre4 ++ [35323]) 160 28262 = true := by decide +kernel

theorem admPre_ok5 : admPreOK (admPre5 ++ [42382]) 200 35323 = true := by decide +kernel

theorem admPre_ok6 : admPreOK (admPre6 ++ [49443]) 240 42382 = true := by decide +kernel

theorem admPre_ok7 : admPreOK (admPre7 ++ [56507]) 280 49443 = true := by decide +kernel

theorem admPre_ok8 : admPreOK (admPre8 ++ [63567]) 320 56507 = true := by decide +kernel

theorem admPre_ok9 : admPreOK (admPre9 ++ [70629]) 360 63567 = true := by decide +kernel

theorem admPre_ok10 : admPreOK (admPre10 ++ [77688]) 400 70629 = true := by decide +kernel

theorem admPre_ok11 : admPreOK (admPre11 ++ [84750]) 440 77688 = true := by decide +kernel

theorem admPre_ok12 : admPreOK (admPre12 ++ [91811]) 480 84750 = true := by decide +kernel

theorem admPre_ok13 : admPreOK (admPre13 ++ [98870]) 520 91811 = true := by decide +kernel

theorem admPre_ok14 : admPreOK (admPre14 ++ [105933]) 560 98870 = true := by decide +kernel

theorem admPre_ok15 : admPreOK (admPre15 ++ [112995]) 600 105933 = true := by decide +kernel

theorem admPre_ok16 : admPreOK (admPre16 ++ [120053]) 640 112995 = true := by decide +kernel

theorem admPre_ok17 : admPreOK (admPre17 ++ [127117]) 680 120053 = true := by decide +kernel

theorem admPre_ok18 : admPreOK (admPre18 ++ [134178]) 720 127117 = true := by decide +kernel

theorem admPre_ok19 : admPreOK (admPre19 ++ [141239]) 760 134178 = true := by decide +kernel

theorem admPre_ok20 : admPreOK (admPre20) 800 141239 = true := by decide +kernel

theorem admPre_tail20 : admPreOK admPre20 800 141239 = true :=
  admPre_ok20

theorem admPre_tail19 : admPreOK (admPre19 ++ (admPre20)) 760 134178 = true :=
  admPreOK_glue 141239 _ admPre19 760 134178 admPre_ok19 admPre_tail20

theorem admPre_tail18 : admPreOK (admPre18 ++ (admPre19 ++ (admPre20))) 720 127117 = true :=
  admPreOK_glue 134178 _ admPre18 720 127117 admPre_ok18 admPre_tail19

theorem admPre_tail17 : admPreOK (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))) 680 120053 = true :=
  admPreOK_glue 127117 _ admPre17 680 120053 admPre_ok17 admPre_tail18

theorem admPre_tail16 : admPreOK (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))) 640 112995 = true :=
  admPreOK_glue 120053 _ admPre16 640 112995 admPre_ok16 admPre_tail17

theorem admPre_tail15 : admPreOK (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))) 600 105933 = true :=
  admPreOK_glue 112995 _ admPre15 600 105933 admPre_ok15 admPre_tail16

theorem admPre_tail14 : admPreOK (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))) 560 98870 = true :=
  admPreOK_glue 105933 _ admPre14 560 98870 admPre_ok14 admPre_tail15

theorem admPre_tail13 : admPreOK (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))))) 520 91811 = true :=
  admPreOK_glue 98870 _ admPre13 520 91811 admPre_ok13 admPre_tail14

theorem admPre_tail12 : admPreOK (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))))) 480 84750 = true :=
  admPreOK_glue 91811 _ admPre12 480 84750 admPre_ok12 admPre_tail13

theorem admPre_tail11 : admPreOK (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))))))) 440 77688 = true :=
  admPreOK_glue 84750 _ admPre11 440 77688 admPre_ok11 admPre_tail12

theorem admPre_tail10 : admPreOK (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))))))) 400 70629 = true :=
  admPreOK_glue 77688 _ admPre10 400 70629 admPre_ok10 admPre_tail11

theorem admPre_tail9 : admPreOK (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))))))))) 360 63567 = true :=
  admPreOK_glue 70629 _ admPre9 360 63567 admPre_ok9 admPre_tail10

theorem admPre_tail8 : admPreOK (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))))))))) 320 56507 = true :=
  admPreOK_glue 63567 _ admPre8 320 56507 admPre_ok8 admPre_tail9

theorem admPre_tail7 : admPreOK (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))))))))))) 280 49443 = true :=
  admPreOK_glue 56507 _ admPre7 280 49443 admPre_ok7 admPre_tail8

theorem admPre_tail6 : admPreOK (admPre6 ++ (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))))))))))) 240 42382 = true :=
  admPreOK_glue 49443 _ admPre6 240 42382 admPre_ok6 admPre_tail7

theorem admPre_tail5 : admPreOK (admPre5 ++ (admPre6 ++ (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))))))))))))) 200 35323 = true :=
  admPreOK_glue 42382 _ admPre5 200 35323 admPre_ok5 admPre_tail6

theorem admPre_tail4 : admPreOK (admPre4 ++ (admPre5 ++ (admPre6 ++ (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))))))))))))) 160 28262 = true :=
  admPreOK_glue 35323 _ admPre4 160 28262 admPre_ok4 admPre_tail5

theorem admPre_tail3 : admPreOK (admPre3 ++ (admPre4 ++ (admPre5 ++ (admPre6 ++ (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))))))))))))))) 120 21199 = true :=
  admPreOK_glue 28262 _ admPre3 120 21199 admPre_ok3 admPre_tail4

theorem admPre_tail2 : admPreOK (admPre2 ++ (admPre3 ++ (admPre4 ++ (admPre5 ++ (admPre6 ++ (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))))))))))))))) 80 14138 = true :=
  admPreOK_glue 21199 _ admPre2 80 14138 admPre_ok2 admPre_tail3

theorem admPre_tail1 : admPreOK (admPre1 ++ (admPre2 ++ (admPre3 ++ (admPre4 ++ (admPre5 ++ (admPre6 ++ (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20)))))))))))))))))))) 40 7076 = true :=
  admPreOK_glue 14138 _ admPre1 40 7076 admPre_ok1 admPre_tail2

theorem admPre_tail0 : admPreOK (admPre0 ++ (admPre1 ++ (admPre2 ++ (admPre3 ++ (admPre4 ++ (admPre5 ++ (admPre6 ++ (admPre7 ++ (admPre8 ++ (admPre9 ++ (admPre10 ++ (admPre11 ++ (admPre12 ++ (admPre13 ++ (admPre14 ++ (admPre15 ++ (admPre16 ++ (admPre17 ++ (admPre18 ++ (admPre19 ++ (admPre20))))))))))))))))))))) 0 0 = true :=
  admPreOK_glue 7076 _ admPre0 0 0 admPre_ok0 admPre_tail1

theorem admPre_ok : admPreOK admPre 0 0 = true := admPre_tail0

end ErdosComp
