import ErdosComp.C2Data
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strsEven_sorted : sortedBm strsEven = true := by decide +kernel

theorem strsEven_valid0 : strsEven0.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid1 : strsEven1.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid2 : strsEven2.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid3 : strsEven3.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid4 : strsEven4.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid5 : strsEven5.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid6 : strsEven6.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid7 : strsEven7.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid8 : strsEven8.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid9 : strsEven9.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid10 : strsEven10.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid11 : strsEven11.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid12 : strsEven12.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid13 : strsEven13.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid14 : strsEven14.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid15 : strsEven15.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid16 : strsEven16.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid17 : strsEven17.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid18 : strsEven18.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid19 : strsEven19.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid20 : strsEven20.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid21 : strsEven21.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid22 : strsEven22.all (strValid discT) = true := by decide +kernel

theorem strsEven_valid : strsEven.all (strValid discT) = true := by
  simp only [strsEven, List.all_append, strsEven_valid0, strsEven_valid1, strsEven_valid2, strsEven_valid3, strsEven_valid4, strsEven_valid5, strsEven_valid6, strsEven_valid7, strsEven_valid8, strsEven_valid9, strsEven_valid10, strsEven_valid11, strsEven_valid12, strsEven_valid13, strsEven_valid14, strsEven_valid15, strsEven_valid16, strsEven_valid17, strsEven_valid18, strsEven_valid19, strsEven_valid20, strsEven_valid21, strsEven_valid22, Bool.and_self]

theorem strsEven_comp0 : completeE 2 0 strsEven = true := by
  unfold completeE
  exact all_of_chunks _ 40 0 _ (by decide +kernel)
    (fun _ hj => absurd hj (by omega))

theorem strsEven_comp1_0 : (((keysOf 2 1).drop (0 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_1 : (((keysOf 2 1).drop (1 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_2 : (((keysOf 2 1).drop (2 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_3 : (((keysOf 2 1).drop (3 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_4 : (((keysOf 2 1).drop (4 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_5 : (((keysOf 2 1).drop (5 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_6 : (((keysOf 2 1).drop (6 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_7 : (((keysOf 2 1).drop (7 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_8 : (((keysOf 2 1).drop (8 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_9 : (((keysOf 2 1).drop (9 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_10 : (((keysOf 2 1).drop (10 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_11 : (((keysOf 2 1).drop (11 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_12 : (((keysOf 2 1).drop (12 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_13 : (((keysOf 2 1).drop (13 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_14 : (((keysOf 2 1).drop (14 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_15 : (((keysOf 2 1).drop (15 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_16 : (((keysOf 2 1).drop (16 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_17 : (((keysOf 2 1).drop (17 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_18 : (((keysOf 2 1).drop (18 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1_19 : (((keysOf 2 1).drop (19 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 1 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp1 : completeE 2 1 strsEven = true := by
  unfold completeE
  exact all_of_chunks _ 40 20 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsEven_comp1_0 | 1, _ => strsEven_comp1_1 | 2, _ => strsEven_comp1_2 | 3, _ => strsEven_comp1_3 | 4, _ => strsEven_comp1_4 | 5, _ => strsEven_comp1_5 | 6, _ => strsEven_comp1_6 | 7, _ => strsEven_comp1_7 | 8, _ => strsEven_comp1_8 | 9, _ => strsEven_comp1_9 | 10, _ => strsEven_comp1_10 | 11, _ => strsEven_comp1_11 | 12, _ => strsEven_comp1_12 | 13, _ => strsEven_comp1_13 | 14, _ => strsEven_comp1_14 | 15, _ => strsEven_comp1_15 | 16, _ => strsEven_comp1_16 | 17, _ => strsEven_comp1_17 | 18, _ => strsEven_comp1_18 | 19, _ => strsEven_comp1_19 | _ + 20, h => absurd h (by omega))

theorem strsEven_comp2_0 : (((keysOf 2 2).drop (0 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_1 : (((keysOf 2 2).drop (1 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_2 : (((keysOf 2 2).drop (2 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_3 : (((keysOf 2 2).drop (3 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_4 : (((keysOf 2 2).drop (4 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_5 : (((keysOf 2 2).drop (5 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_6 : (((keysOf 2 2).drop (6 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_7 : (((keysOf 2 2).drop (7 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_8 : (((keysOf 2 2).drop (8 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_9 : (((keysOf 2 2).drop (9 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_10 : (((keysOf 2 2).drop (10 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_11 : (((keysOf 2 2).drop (11 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_12 : (((keysOf 2 2).drop (12 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_13 : (((keysOf 2 2).drop (13 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_14 : (((keysOf 2 2).drop (14 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_15 : (((keysOf 2 2).drop (15 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_16 : (((keysOf 2 2).drop (16 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_17 : (((keysOf 2 2).drop (17 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2_18 : (((keysOf 2 2).drop (18 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 2 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp2 : completeE 2 2 strsEven = true := by
  unfold completeE
  exact all_of_chunks _ 40 19 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsEven_comp2_0 | 1, _ => strsEven_comp2_1 | 2, _ => strsEven_comp2_2 | 3, _ => strsEven_comp2_3 | 4, _ => strsEven_comp2_4 | 5, _ => strsEven_comp2_5 | 6, _ => strsEven_comp2_6 | 7, _ => strsEven_comp2_7 | 8, _ => strsEven_comp2_8 | 9, _ => strsEven_comp2_9 | 10, _ => strsEven_comp2_10 | 11, _ => strsEven_comp2_11 | 12, _ => strsEven_comp2_12 | 13, _ => strsEven_comp2_13 | 14, _ => strsEven_comp2_14 | 15, _ => strsEven_comp2_15 | 16, _ => strsEven_comp2_16 | 17, _ => strsEven_comp2_17 | 18, _ => strsEven_comp2_18 | _ + 19, h => absurd h (by omega))

theorem strsEven_comp3_0 : (((keysOf 2 3).drop (0 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_1 : (((keysOf 2 3).drop (1 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_2 : (((keysOf 2 3).drop (2 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_3 : (((keysOf 2 3).drop (3 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_4 : (((keysOf 2 3).drop (4 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_5 : (((keysOf 2 3).drop (5 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_6 : (((keysOf 2 3).drop (6 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_7 : (((keysOf 2 3).drop (7 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_8 : (((keysOf 2 3).drop (8 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_9 : (((keysOf 2 3).drop (9 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_10 : (((keysOf 2 3).drop (10 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_11 : (((keysOf 2 3).drop (11 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_12 : (((keysOf 2 3).drop (12 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_13 : (((keysOf 2 3).drop (13 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_14 : (((keysOf 2 3).drop (14 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_15 : (((keysOf 2 3).drop (15 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_16 : (((keysOf 2 3).drop (16 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3_17 : (((keysOf 2 3).drop (17 * 40)).take 40).all
    (fun k => strsEven.any (fun s => Nat.beq s.e 3 && decide (s.qs = k.1) && Nat.beq s.u k.2)) = true := by decide +kernel

theorem strsEven_comp3 : completeE 2 3 strsEven = true := by
  unfold completeE
  exact all_of_chunks _ 40 18 _ (by decide +kernel)
    (fun j hj => match j, hj with | 0, _ => strsEven_comp3_0 | 1, _ => strsEven_comp3_1 | 2, _ => strsEven_comp3_2 | 3, _ => strsEven_comp3_3 | 4, _ => strsEven_comp3_4 | 5, _ => strsEven_comp3_5 | 6, _ => strsEven_comp3_6 | 7, _ => strsEven_comp3_7 | 8, _ => strsEven_comp3_8 | 9, _ => strsEven_comp3_9 | 10, _ => strsEven_comp3_10 | 11, _ => strsEven_comp3_11 | 12, _ => strsEven_comp3_12 | 13, _ => strsEven_comp3_13 | 14, _ => strsEven_comp3_14 | 15, _ => strsEven_comp3_15 | 16, _ => strsEven_comp3_16 | 17, _ => strsEven_comp3_17 | _ + 18, h => absurd h (by omega))

end ErdosComp
