import ErdosComp.C2Data
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strsOdd_sorted : sortedBm strsOdd = true := by decide +kernel

theorem strsOdd_valid0 : strsOdd0.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid1 : strsOdd1.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid2 : strsOdd2.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid3 : strsOdd3.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid4 : strsOdd4.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid5 : strsOdd5.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid6 : strsOdd6.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid7 : strsOdd7.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid8 : strsOdd8.all (strValid discT) = true := by decide +kernel

theorem strsOdd_valid : strsOdd.all (strValid discT) = true := by
  simp only [strsOdd, List.all_append, strsOdd_valid0, strsOdd_valid1, strsOdd_valid2, strsOdd_valid3, strsOdd_valid4, strsOdd_valid5, strsOdd_valid6, strsOdd_valid7, strsOdd_valid8, Bool.and_self]

theorem strsOdd_comp0_0 : (((keysOf 1 0).drop (0 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_1 : (((keysOf 1 0).drop (1 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_2 : (((keysOf 1 0).drop (2 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_3 : (((keysOf 1 0).drop (3 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_4 : (((keysOf 1 0).drop (4 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_5 : (((keysOf 1 0).drop (5 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_6 : (((keysOf 1 0).drop (6 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_7 : (((keysOf 1 0).drop (7 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_8 : (((keysOf 1 0).drop (8 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_9 : (((keysOf 1 0).drop (9 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_10 : (((keysOf 1 0).drop (10 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_11 : (((keysOf 1 0).drop (11 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_12 : (((keysOf 1 0).drop (12 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_13 : (((keysOf 1 0).drop (13 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_14 : (((keysOf 1 0).drop (14 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_15 : (((keysOf 1 0).drop (15 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_16 : (((keysOf 1 0).drop (16 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_17 : (((keysOf 1 0).drop (17 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_18 : (((keysOf 1 0).drop (18 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_19 : (((keysOf 1 0).drop (19 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0_20 : (((keysOf 1 0).drop (20 * 40)).take 40).all
    (fun k => strsOdd.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsOdd_comp0 : completeE 1 0 strsOdd = true := by
  unfold completeE
  exact all_of_chunks _ 40 21 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsOdd_comp0_0 | 1, _ => strsOdd_comp0_1 | 2, _ => strsOdd_comp0_2 | 3, _ => strsOdd_comp0_3 | 4, _ => strsOdd_comp0_4 | 5, _ => strsOdd_comp0_5 | 6, _ => strsOdd_comp0_6 | 7, _ => strsOdd_comp0_7 | 8, _ => strsOdd_comp0_8 | 9, _ => strsOdd_comp0_9 | 10, _ => strsOdd_comp0_10 | 11, _ => strsOdd_comp0_11 | 12, _ => strsOdd_comp0_12 | 13, _ => strsOdd_comp0_13 | 14, _ => strsOdd_comp0_14 | 15, _ => strsOdd_comp0_15 | 16, _ => strsOdd_comp0_16 | 17, _ => strsOdd_comp0_17 | 18, _ => strsOdd_comp0_18 | 19, _ => strsOdd_comp0_19 | 20, _ => strsOdd_comp0_20 | _ + 21, h => absurd h (by omega))

theorem strsOdd_comp1 : completeE 1 1 strsOdd = true := by
  unfold completeE
  exact all_of_chunks _ 40 0 _ (by decide +kernel)
    (fun _ hj => absurd hj (by omega))

theorem strsOdd_comp2 : completeE 1 2 strsOdd = true := by
  unfold completeE
  exact all_of_chunks _ 40 0 _ (by decide +kernel)
    (fun _ hj => absurd hj (by omega))

theorem strsOdd_comp3 : completeE 1 3 strsOdd = true := by
  unfold completeE
  exact all_of_chunks _ 40 0 _ (by decide +kernel)
    (fun _ hj => absurd hj (by omega))

end ErdosComp
