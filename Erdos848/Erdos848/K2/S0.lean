import ErdosComp.C2Data
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strsAny_sorted : sortedBm strsAny = true := by decide +kernel

theorem strsAny_valid0 : strsAny0.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid1 : strsAny1.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid2 : strsAny2.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid3 : strsAny3.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid4 : strsAny4.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid5 : strsAny5.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid6 : strsAny6.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid7 : strsAny7.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid8 : strsAny8.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid9 : strsAny9.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid10 : strsAny10.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid11 : strsAny11.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid12 : strsAny12.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid13 : strsAny13.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid14 : strsAny14.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid15 : strsAny15.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid16 : strsAny16.all (strValid discT) = true := by decide +kernel

theorem strsAny_valid : strsAny.all (strValid discT) = true := by
  simp only [strsAny, List.all_append, strsAny_valid0, strsAny_valid1, strsAny_valid2, strsAny_valid3, strsAny_valid4, strsAny_valid5, strsAny_valid6, strsAny_valid7, strsAny_valid8, strsAny_valid9, strsAny_valid10, strsAny_valid11, strsAny_valid12, strsAny_valid13, strsAny_valid14, strsAny_valid15, strsAny_valid16, Bool.and_self]

theorem strsAny_comp0_0 : (((keysOf 0 0).drop (0 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_1 : (((keysOf 0 0).drop (1 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_2 : (((keysOf 0 0).drop (2 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_3 : (((keysOf 0 0).drop (3 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_4 : (((keysOf 0 0).drop (4 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_5 : (((keysOf 0 0).drop (5 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_6 : (((keysOf 0 0).drop (6 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_7 : (((keysOf 0 0).drop (7 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_8 : (((keysOf 0 0).drop (8 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_9 : (((keysOf 0 0).drop (9 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_10 : (((keysOf 0 0).drop (10 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0_11 : (((keysOf 0 0).drop (11 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 0 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp0 : completeE 0 0 strsAny = true := by
  unfold completeE
  exact all_of_chunks _ 40 12 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsAny_comp0_0 | 1, _ => strsAny_comp0_1 | 2, _ => strsAny_comp0_2 | 3, _ => strsAny_comp0_3 | 4, _ => strsAny_comp0_4 | 5, _ => strsAny_comp0_5 | 6, _ => strsAny_comp0_6 | 7, _ => strsAny_comp0_7 | 8, _ => strsAny_comp0_8 | 9, _ => strsAny_comp0_9 | 10, _ => strsAny_comp0_10 | 11, _ => strsAny_comp0_11 | _ + 12, h => absurd h (by omega))

theorem strsAny_comp1_0 : (((keysOf 0 1).drop (0 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_1 : (((keysOf 0 1).drop (1 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_2 : (((keysOf 0 1).drop (2 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_3 : (((keysOf 0 1).drop (3 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_4 : (((keysOf 0 1).drop (4 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_5 : (((keysOf 0 1).drop (5 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_6 : (((keysOf 0 1).drop (6 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_7 : (((keysOf 0 1).drop (7 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_8 : (((keysOf 0 1).drop (8 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_9 : (((keysOf 0 1).drop (9 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1_10 : (((keysOf 0 1).drop (10 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp1 : completeE 0 1 strsAny = true := by
  unfold completeE
  exact all_of_chunks _ 40 11 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsAny_comp1_0 | 1, _ => strsAny_comp1_1 | 2, _ => strsAny_comp1_2 | 3, _ => strsAny_comp1_3 | 4, _ => strsAny_comp1_4 | 5, _ => strsAny_comp1_5 | 6, _ => strsAny_comp1_6 | 7, _ => strsAny_comp1_7 | 8, _ => strsAny_comp1_8 | 9, _ => strsAny_comp1_9 | 10, _ => strsAny_comp1_10 | _ + 11, h => absurd h (by omega))

theorem strsAny_comp2_0 : (((keysOf 0 2).drop (0 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_1 : (((keysOf 0 2).drop (1 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_2 : (((keysOf 0 2).drop (2 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_3 : (((keysOf 0 2).drop (3 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_4 : (((keysOf 0 2).drop (4 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_5 : (((keysOf 0 2).drop (5 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_6 : (((keysOf 0 2).drop (6 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_7 : (((keysOf 0 2).drop (7 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_8 : (((keysOf 0 2).drop (8 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2_9 : (((keysOf 0 2).drop (9 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp2 : completeE 0 2 strsAny = true := by
  unfold completeE
  exact all_of_chunks _ 40 10 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsAny_comp2_0 | 1, _ => strsAny_comp2_1 | 2, _ => strsAny_comp2_2 | 3, _ => strsAny_comp2_3 | 4, _ => strsAny_comp2_4 | 5, _ => strsAny_comp2_5 | 6, _ => strsAny_comp2_6 | 7, _ => strsAny_comp2_7 | 8, _ => strsAny_comp2_8 | 9, _ => strsAny_comp2_9 | _ + 10, h => absurd h (by omega))

theorem strsAny_comp3_0 : (((keysOf 0 3).drop (0 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_1 : (((keysOf 0 3).drop (1 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_2 : (((keysOf 0 3).drop (2 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_3 : (((keysOf 0 3).drop (3 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_4 : (((keysOf 0 3).drop (4 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_5 : (((keysOf 0 3).drop (5 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_6 : (((keysOf 0 3).drop (6 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_7 : (((keysOf 0 3).drop (7 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_8 : (((keysOf 0 3).drop (8 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3_9 : (((keysOf 0 3).drop (9 * 40)).take 40).all
    (fun k => strsAny.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsAny_comp3 : completeE 0 3 strsAny = true := by
  unfold completeE
  exact all_of_chunks _ 40 10 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsAny_comp3_0 | 1, _ => strsAny_comp3_1 | 2, _ => strsAny_comp3_2 | 3, _ => strsAny_comp3_3 | 4, _ => strsAny_comp3_4 | 5, _ => strsAny_comp3_5 | 6, _ => strsAny_comp3_6 | 7, _ => strsAny_comp3_7 | 8, _ => strsAny_comp3_8 | 9, _ => strsAny_comp3_9 | _ + 10, h => absurd h (by omega))

end ErdosComp
