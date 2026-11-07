import LonelyRunnerNew.LCFiniteSieve

namespace LonelyRunnerNew.LCNumeric.SieveData
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def middle_0 : List ℕ := [73,2,7,2,3,2,0,2,0,2,3,2,17,2,5,2,3,2,43,2,11,2,3,2,5,2,37,2,3,2,7,2,79,2,3,2,0,2,0,2,3,2,11,2,5,2,3,2,13,2,19,2,3,2,5,2,89,2,3,2,0,2,29,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,0,2,17,2,3,2,5,2,7,2,3,2,0,2,0,2,3,2,23,2,0,2,3]
theorem middle_0_valid : SieveValid 10001 middle_0 := by decide +kernel
theorem middle_0_length : middle_0.length=101 := by decide +kernel
theorem middle_0_count : middle_0.count 0=11 := by decide +kernel
theorem middle_0_root : (1:ℚ) ≤ (214198253343/200000000000000000:ℚ)^67*(10001:ℚ)^100 := by
  exact integer_negative_root 214198253343 200000000000000000 10001 100 67 (by decide) (by decide +kernel)

def middle_1 : List ℕ := [2,0,2,5,2,3,2,11,2,0,2,3,2,5,2,67,2,3,2,29,2,53,2,3,2,13,2,7,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,73,2,3,2,0,2,11,2,3,2,7,2,0,2,3,2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,0,2,17,2,3,2,61,2,23,2,3,2,0,2,5,2,3,2,7,2,101,2,3]
theorem middle_1_valid : SieveValid 10102 middle_1 := by decide +kernel
theorem middle_1_length : middle_1.length=102 := by decide +kernel
theorem middle_1_count : middle_1.count 0=12 := by decide +kernel
theorem middle_1_root : (1:ℚ) ≤ (1055048904267/1000000000000000000:ℚ)^67*(10102:ℚ)^100 := by
  exact integer_negative_root 1055048904267 1000000000000000000 10102 100 67 (by decide) (by decide +kernel)

def middle_2 : List ℕ := [2,5,2,59,2,3,2,0,2,7,2,3,2,17,2,11,2,3,2,0,2,5,2,3,2,53,2,13,2,3,2,5,2,29,2,3,2,7,2,0,2,3,2,0,2,37,2,3,2,0,2,5,2,3,2,0,2,31,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,43,2,19,2,3,2,7,2,5,2,3,2,0,2,41,2,3,2,5,2,7,2,3,2,0,2,0,2,3,2]
theorem middle_2_valid : SieveValid 10204 middle_2 := by decide +kernel
theorem middle_2_length : middle_2.length=103 := by decide +kernel
theorem middle_2_count : middle_2.count 0=12 := by decide +kernel
theorem middle_2_root : (1:ℚ) ≤ (519673446931/500000000000000000:ℚ)^67*(10204:ℚ)^100 := by
  exact integer_negative_root 519673446931 500000000000000000 10204 100 67 (by decide) (by decide +kernel)

def middle_3 : List ℕ := [11,2,13,2,3,2,0,2,5,2,3,2,17,2,0,2,3,2,5,2,23,2,3,2,0,2,0,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,79,2,11,2,3,2,5,2,0,2,3,2,13,2,43,2,3,2,7,2,0,2,3,2,11,2,5,2,3,2,97,2,7,2,3,2,5,2,13,2,3,2,0,2,19,2,3,2,37,2,0,2,3,2,101,2,5,2,3,2,7,2]
theorem middle_3_valid : SieveValid 10307 middle_3 := by decide +kernel
theorem middle_3_length : middle_3.length=104 := by decide +kernel
theorem middle_3_count : middle_3.count 0=10 := by decide +kernel
theorem middle_3_root : (1:ℚ) ≤ (511941502349/500000000000000000:ℚ)^67*(10307:ℚ)^100 := by
  exact integer_negative_root 511941502349 500000000000000000 10307 100 67 (by decide) (by decide +kernel)

def middle_4 : List ℕ := [29,2,3,2,5,2,11,2,3,2,17,2,7,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,11,2,53,2,3,2,5,2,31,2,3,2,7,2,0,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,19,2,37,2,3,2,5,2,0,2,3,2,47,2,11,2,3,2,0,2,17,2,3,2,7,2,5,2,3,2,0,2,0,2,3,2,5,2,7,2,3,2,23,2,0,2,3]
theorem middle_4_valid : SieveValid 10411 middle_4 := by decide +kernel
theorem middle_4_length : middle_4.length=105 := by decide +kernel
theorem middle_4_count : middle_4.count 0=12 := by decide +kernel
theorem middle_4_root : (1:ℚ) ≤ (201730986759/200000000000000000:ℚ)^67*(10411:ℚ)^100 := by
  exact integer_negative_root 201730986759 200000000000000000 10411 100 67 (by decide) (by decide +kernel)

def middle_5 : List ℕ := [2,13,2,67,2,3,2,17,2,5,2,3,2,0,2,0,2,3,2,5,2,41,2,3,2,83,2,13,2,3,2,53,2,7,2,3,2,61,2,5,2,3,2,0,2,59,2,3,2,5,2,0,2,3,2,11,2,97,2,3,2,7,2,71,2,3,2,19,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,0,2,23,2,3,2,0,2,103,2,3,2,0,2,5,2,3,2,7,2,13]
theorem middle_5_valid : SieveValid 10516 middle_5 := by decide +kernel
theorem middle_5_length : middle_5.length=106 := by decide +kernel
theorem middle_5_count : middle_5.count 0=9 := by decide +kernel
theorem middle_5_root : (1:ℚ) ≤ (496830156241/500000000000000000:ℚ)^67*(10516:ℚ)^100 := by
  exact integer_negative_root 496830156241 500000000000000000 10516 100 67 (by decide) (by decide +kernel)

def middle_6 : List ℕ := [2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,11,2,0,2,3,2,29,2,5,2,3,2,23,2,0,2,3,2,5,2,0,2,3,2,7,2,0,2,3,2,0,2,47,2,3,2,13,2,5,2,3,2,59,2,11,2,3,2,5,2,0,2,3,2,0,2,17,2,3,2,19,2,13,2,3,2,7,2,5,2,3,2,0,2,0,2,3,2,5,2,7,2,3,2,71,2,0,2,3,2,17,2]
theorem middle_6_valid : SieveValid 10622 middle_6 := by decide +kernel
theorem middle_6_length : middle_6.length=107 := by decide +kernel
theorem middle_6_count : middle_6.count 0=12 := by decide +kernel
theorem middle_6_root : (1:ℚ) ≤ (489448356293/500000000000000000:ℚ)^67*(10622:ℚ)^100 := by
  exact integer_negative_root 489448356293 500000000000000000 10622 100 67 (by decide) (by decide +kernel)

def middle_7 : List ℕ := [0,2,3,2,0,2,5,2,3,2,0,2,23,2,3,2,5,2,11,2,3,2,13,2,0,2,3,2,31,2,7,2,3,2,47,2,5,2,3,2,11,2,0,2,3,2,5,2,13,2,3,2,0,2,41,2,3,2,7,2,0,2,3,2,43,2,5,2,3,2,0,2,7,2,3,2,5,2,101,2,3,2,19,2,11,2,3,2,29,2,31,2,3,2,79,2,5,2,3,2,7,2,0,2,3,2,5,2]
theorem middle_7_valid : SieveValid 10729 middle_7 := by decide +kernel
theorem middle_7_length : middle_7.length=108 := by decide +kernel
theorem middle_7_count : middle_7.count 0=9 := by decide +kernel
theorem middle_7_root : (1:ℚ) ≤ (964361652321/1000000000000000000:ℚ)^67*(10729:ℚ)^100 := by
  exact integer_negative_root 964361652321 1000000000000000000 10729 100 67 (by decide) (by decide +kernel)

def middle_8 : List ℕ := [0,2,3,2,37,2,7,2,3,2,0,2,19,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,0,2,3,2,7,2,83,2,3,2,73,2,11,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,17,2,3,2,11,2,0,2,3,2,13,2,0,2,3,2,7,2,5,2,3,2,61,2,67,2,3,2,5,2,7,2,3,2,17,2,13,2,3,2,0,2,0,2,3,2,31,2,5]
theorem middle_8_valid : SieveValid 10837 middle_8 := by decide +kernel
theorem middle_8_length : middle_8.length=109 := by decide +kernel
theorem middle_8_count : middle_8.count 0=13 := by decide +kernel
theorem middle_8_root : (1:ℚ) ≤ (950052601897/1000000000000000000:ℚ)^67*(10837:ℚ)^100 := by
  exact integer_negative_root 950052601897 1000000000000000000 10837 100 67 (by decide) (by decide +kernel)

def middle_9 : List ℕ := [2,3,2,0,2,47,2,3,2,5,2,0,2,3,2,97,2,19,2,3,2,11,2,7,2,3,2,0,2,5,2,3,2,0,2,79,2,3,2,5,2,0,2,3,2,29,2,0,2,3,2,7,2,17,2,3,2,0,2,5,2,3,2,101,2,7,2,3,2,5,2,23,2,3,2,103,2,73,2,3,2,0,2,41,2,3,2,11,2,5,2,3,2,7,2,61,2,3,2,5,2,0,2,3,2,43,2,7,2,3]
theorem middle_9_valid : SieveValid 10946 middle_9 := by decide +kernel
theorem middle_9_length : middle_9.length=110 := by decide +kernel
theorem middle_9_count : middle_9.count 0=9 := by decide +kernel
theorem middle_9_root : (1:ℚ) ≤ (187193397771/200000000000000000:ℚ)^67*(10946:ℚ)^100 := by
  exact integer_negative_root 187193397771 200000000000000000 10946 100 67 (by decide) (by decide +kernel)

def middle_10 : List ℕ := [2,0,2,0,2,3,2,13,2,5,2,3,2,0,2,0,2,3,2,5,2,11,2,3,2,7,2,0,2,3,2,0,2,13,2,3,2,0,2,5,2,3,2,11,2,17,2,3,2,5,2,29,2,3,2,41,2,0,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,31,2,0,2,3,2,5,2,7,2,3,2,13,2,11,2,3,2,71,2,0,2,3,2,19,2,5,2,3,2,0,2,0,2,3,2,5,2]
theorem middle_10_valid : SieveValid 11056 middle_10 := by decide +kernel
theorem middle_10_length : middle_10.length=111 := by decide +kernel
theorem middle_10_count : middle_10.count 0=14 := by decide +kernel
theorem middle_10_root : (1:ℚ) ≤ (461051101561/500000000000000000:ℚ)^67*(11056:ℚ)^100 := by
  exact integer_negative_root 461051101561 500000000000000000 11056 100 67 (by decide) (by decide +kernel)

def middle_11 : List ℕ := [13,2,3,2,0,2,0,2,3,2,0,2,7,2,3,2,53,2,5,2,3,2,67,2,19,2,3,2,5,2,0,2,3,2,23,2,17,2,3,2,7,2,11,2,3,2,0,2,5,2,3,2,13,2,7,2,3,2,5,2,103,2,3,2,11,2,47,2,3,2,17,2,0,2,3,2,0,2,5,2,3,2,7,2,0,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,19,2,59,2,3,2,0,2,5,2,3,2]
theorem middle_11_valid : SieveValid 11167 middle_11 := by decide +kernel
theorem middle_11_length : middle_11.length=112 := by decide +kernel
theorem middle_11_count : middle_11.count 0=11 := by decide +kernel
theorem middle_11_root : (1:ℚ) ≤ (45422780091/50000000000000000:ℚ)^67*(11167:ℚ)^100 := by
  exact integer_negative_root 45422780091 50000000000000000 11167 100 67 (by decide) (by decide +kernel)

def middle_12 : List ℕ := [0,2,29,2,3,2,5,2,0,2,3,2,7,2,23,2,3,2,11,2,0,2,3,2,89,2,5,2,3,2,43,2,0,2,3,2,5,2,0,2,3,2,0,2,13,2,3,2,47,2,0,2,3,2,7,2,5,2,3,2,17,2,11,2,3,2,5,2,7,2,3,2,0,2,0,2,3,2,41,2,37,2,3,2,11,2,5,2,3,2,0,2,83,2,3,2,5,2,31,2,3,2,19,2,0,2,3,2,59,2,7,2,3]
theorem middle_12_valid : SieveValid 11279 middle_12 := by decide +kernel
theorem middle_12_length : middle_12.length=113 := by decide +kernel
theorem middle_12_count : middle_12.count 0=11 := by decide +kernel
theorem middle_12_root : (1:ℚ) ≤ (223756128453/250000000000000000:ℚ)^67*(11279:ℚ)^100 := by
  exact integer_negative_root 223756128453 250000000000000000 11279 100 67 (by decide) (by decide +kernel)

def middle_13 : List ℕ := [2,0,2,5,2,3,2,0,2,13,2,3,2,5,2,11,2,3,2,0,2,101,2,3,2,7,2,19,2,3,2,0,2,5,2,3,2,11,2,7,2,3,2,5,2,0,2,3,2,17,2,0,2,3,2,0,2,107,2,3,2,13,2,5,2,3,2,7,2,73,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,23,2,13,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,0,2,3,2,7,2,0,2,3]
theorem middle_13_valid : SieveValid 11392 middle_13 := by decide +kernel
theorem middle_13_length : middle_13.length=114 := by decide +kernel
theorem middle_13_count : middle_13.count 0=14 := by decide +kernel
theorem middle_13_root : (1:ℚ) ≤ (881806244013/1000000000000000000:ℚ)^67*(11392:ℚ)^100 := by
  exact integer_negative_root 881806244013 1000000000000000000 11392 100 67 (by decide) (by decide +kernel)

def middle_14 : List ℕ := [2,37,2,17,2,3,2,29,2,5,2,3,2,0,2,41,2,3,2,5,2,0,2,3,2,13,2,19,2,3,2,83,2,11,2,3,2,7,2,5,2,3,2,0,2,0,2,3,2,5,2,7,2,3,2,11,2,31,2,3,2,43,2,23,2,3,2,71,2,5,2,3,2,0,2,37,2,3,2,5,2,0,2,3,2,67,2,0,2,3,2,0,2,7,2,3,2,41,2,5,2,3,2,13,2,17,2,3,2,5,2,0,2,3,2,0]
theorem middle_14_valid : SieveValid 11506 middle_14 := by decide +kernel
theorem middle_14_length : middle_14.length=116 := by decide +kernel
theorem middle_14_count : middle_14.count 0=10 := by decide +kernel
theorem middle_14_root : (1:ℚ) ≤ (434399038733/500000000000000000:ℚ)^67*(11506:ℚ)^100 := by
  exact integer_negative_root 434399038733 500000000000000000 11506 100 67 (by decide) (by decide +kernel)

def middle_15 : List ℕ := [2,59,2,3,2,7,2,29,2,3,2,0,2,5,2,3,2,103,2,7,2,3,2,5,2,19,2,3,2,61,2,43,2,3,2,0,2,89,2,3,2,107,2,5,2,3,2,7,2,11,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,13,2,0,2,3,2,11,2,5,2,3,2,0,2,0,2,3,2,5,2,23,2,3,2,7,2,13,2,3,2,0,2,0,2,3,2,19,2,5,2,3,2,37,2,0,2,3,2,5,2,11,2]
theorem middle_15_valid : SieveValid 11622 middle_15 := by decide +kernel
theorem middle_15_length : middle_15.length=117 := by decide +kernel
theorem middle_15_count : middle_15.count 0=10 := by decide +kernel
theorem middle_15_root : (1:ℚ) ≤ (855887355391/1000000000000000000:ℚ)^67*(11622:ℚ)^100 := by
  exact integer_negative_root 855887355391 1000000000000000000 11622 100 67 (by decide) (by decide +kernel)

def middle_16 : List ℕ := [3,2,59,2,0,2,3,2,17,2,31,2,3,2,7,2,5,2,3,2,11,2,19,2,3,2,5,2,7,2,3,2,79,2,61,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,0,2,13,2,3,2,5,2,47,2,3,2,0,2,11,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,53,2,0,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,7,2,0,2,3,2,13,2,5,2,3,2,17,2,7,2,3,2,5,2]
theorem middle_16_valid : SieveValid 11739 middle_16 := by decide +kernel
theorem middle_16_length : middle_16.length=118 := by decide +kernel
theorem middle_16_count : middle_16.count 0=13 := by decide +kernel
theorem middle_16_root : (1:ℚ) ≤ (843186660881/1000000000000000000:ℚ)^67*(11739:ℚ)^100 := by
  exact integer_negative_root 843186660881 1000000000000000000 11739 100 67 (by decide) (by decide +kernel)

def middle_17 : List ℕ := [71,2,3,2,29,2,0,2,3,2,0,2,11,2,3,2,31,2,5,2,3,2,7,2,109,2,3,2,5,2,0,2,3,2,11,2,7,2,3,2,0,2,73,2,3,2,0,2,5,2,3,2,0,2,43,2,3,2,5,2,17,2,3,2,7,2,0,2,3,2,0,2,79,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,13,2,3,2,17,2,0,2,3,2,11,2,0,2,3,2,7,2,5,2,3,2,0,2,0,2,3,2,5]
theorem middle_17_valid : SieveValid 11857 middle_17 := by decide +kernel
theorem middle_17_length : middle_17.length=119 := by decide +kernel
theorem middle_17_count : middle_17.count 0=15 := by decide +kernel
theorem middle_17_root : (1:ℚ) ≤ (830693031659/1000000000000000000:ℚ)^67*(11857:ℚ)^100 := by
  exact integer_negative_root 830693031659 1000000000000000000 11857 100 67 (by decide) (by decide +kernel)

def middle_18 : List ℕ := [2,7,2,3,2,0,2,23,2,3,2,0,2,19,2,3,2,67,2,5,2,3,2,13,2,11,2,3,2,5,2,0,2,3,2,0,2,41,2,3,2,61,2,7,2,3,2,11,2,5,2,3,2,23,2,53,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,7,2,0,2,3,2,17,2,5,2,3,2,31,2,7,2,3,2,5,2,11,2,3,2,0,2,0,2,3,2,13,2,47,2,3,2,43,2,5,2,3,2,7,2,107,2,3,2,5]
theorem middle_18_valid : SieveValid 11976 middle_18 := by decide +kernel
theorem middle_18_length : middle_18.length=120 := by decide +kernel
theorem middle_18_count : middle_18.count 0=10 := by decide +kernel
theorem middle_18_root : (1:ℚ) ≤ (818403506727/1000000000000000000:ℚ)^67*(11976:ℚ)^100 := by
  exact integer_negative_root 818403506727 1000000000000000000 11976 100 67 (by decide) (by decide +kernel)

def middle_19 : List ℕ := [2,0,2,3,2,0,2,7,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,0,2,17,2,3,2,5,2,67,2,3,2,7,2,11,2,3,2,53,2,61,2,3,2,0,2,5,2,3,2,0,2,29,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,23,2,43,2,3,2,7,2,5,2,3,2,19,2,13,2,3,2,5,2,7,2,3,2,73,2,89,2,3,2,0,2,11,2,3,2,0,2,5,2,3,2,29,2,0,2,3,2,5,2]
theorem middle_19_valid : SieveValid 12096 middle_19 := by decide +kernel
theorem middle_19_length : middle_19.length=121 := by decide +kernel
theorem middle_19_count : middle_19.count 0=14 := by decide +kernel
theorem middle_19_root : (1:ℚ) ≤ (806315129221/1000000000000000000:ℚ)^67*(12096:ℚ)^100 := by
  exact integer_negative_root 806315129221 1000000000000000000 12096 100 67 (by decide) (by decide +kernel)

def middle_20 : List ℕ := [19,2,3,2,11,2,17,2,3,2,0,2,7,2,3,2,13,2,5,2,3,2,0,2,0,2,3,2,5,2,37,2,3,2,0,2,0,2,3,2,7,2,13,2,3,2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,0,2,71,2,3,2,11,2,0,2,3,2,19,2,5,2,3,2,7,2,0,2,3,2,5,2,31,2,3,2,13,2,7,2,3,2,109,2,97,2,3,2,0,2,5,2,3,2,0,2,11,2,3,2,5,2,13,2,3]
theorem middle_20_valid : SieveValid 12217 middle_20 := by decide +kernel
theorem middle_20_length : middle_20.length=123 := by decide +kernel
theorem middle_20_count : middle_20.count 0=13 := by decide +kernel
theorem middle_20_root : (1:ℚ) ≤ (397212474541/500000000000000000:ℚ)^67*(12217:ℚ)^100 := by
  exact integer_negative_root 397212474541 500000000000000000 12217 100 67 (by decide) (by decide +kernel)

def middle_21 : List ℕ := [2,7,2,0,2,3,2,0,2,53,2,3,2,11,2,5,2,3,2,17,2,47,2,3,2,5,2,83,2,3,2,89,2,0,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,13,2,0,2,3,2,5,2,7,2,3,2,0,2,79,2,3,2,19,2,0,2,3,2,0,2,5,2,3,2,11,2,0,2,3,2,5,2,17,2,3,2,31,2,0,2,3,2,0,2,7,2,3,2,23,2,5,2,3,2,59,2,0,2,3,2,5,2,0,2,3,2,17,2,11]
theorem middle_21_valid : SieveValid 12340 middle_21 := by decide +kernel
theorem middle_21_length : middle_21.length=124 := by decide +kernel
theorem middle_21_count : middle_21.count 0=14 := by decide +kernel
theorem middle_21_root : (1:ℚ) ≤ (195658838833/250000000000000000:ℚ)^67*(12340:ℚ)^100 := by
  exact integer_negative_root 195658838833 250000000000000000 12340 100 67 (by decide) (by decide +kernel)

def middle_22 : List ℕ := [2,3,2,7,2,37,2,3,2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,0,2,13,2,3,2,0,2,29,2,3,2,0,2,5,2,3,2,7,2,0,2,3,2,5,2,0,2,3,2,19,2,7,2,3,2,0,2,11,2,3,2,83,2,5,2,3,2,0,2,0,2,3,2,5,2,0,2,3,2,7,2,0,2,3,2,29,2,19,2,3,2,17,2,5,2,3,2,0,2,13,2,3,2,5,2,0,2,3,2,23,2,0,2,3,2,41,2]
theorem middle_22_valid : SieveValid 12464 middle_22 := by decide +kernel
theorem middle_22_length : middle_22.length=125 := by decide +kernel
theorem middle_22_count : middle_22.count 0=16 := by decide +kernel
theorem middle_22_root : (1:ℚ) ≤ (154208546221/200000000000000000:ℚ)^67*(12464:ℚ)^100 := by
  exact integer_negative_root 154208546221 200000000000000000 12464 100 67 (by decide) (by decide +kernel)

def middle_23 : List ℕ := [0,2,3,2,7,2,5,2,3,2,43,2,0,2,3,2,5,2,7,2,3,2,0,2,0,2,3,2,11,2,0,2,3,2,13,2,5,2,3,2,73,2,17,2,3,2,5,2,0,2,3,2,0,2,47,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,0,2,11,2,3,2,5,2,53,2,3,2,0,2,19,2,3,2,7,2,31,2,3,2,11,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,13,2,0,2,3,2,97,2,71,2,3,2,0,2]
theorem middle_23_valid : SieveValid 12589 middle_23 := by decide +kernel
theorem middle_23_length : middle_23.length=126 := by decide +kernel
theorem middle_23_count : middle_23.count 0=15 := by decide +kernel
theorem middle_23_root : (1:ℚ) ≤ (759643977691/1000000000000000000:ℚ)^67*(12589:ℚ)^100 := by
  exact integer_negative_root 759643977691 1000000000000000000 12589 100 67 (by decide) (by decide +kernel)

def middle_24 : List ℕ := [5,2,3,2,7,2,0,2,3,2,5,2,11,2,3,2,29,2,7,2,3,2,47,2,0,2,3,2,0,2,5,2,3,2,11,2,41,2,3,2,5,2,0,2,3,2,7,2,0,2,3,2,17,2,113,2,3,2,53,2,5,2,3,2,13,2,0,2,3,2,5,2,19,2,3,2,0,2,11,2,3,2,67,2,0,2,3,2,7,2,5,2,3,2,0,2,23,2,3,2,5,2,7,2,3,2,0,2,0,2,3,2,101,2,0,2,3,2,41,2,5,2,3,2,37,2,0,2]
theorem middle_24_valid : SieveValid 12715 middle_24 := by decide +kernel
theorem middle_24_length : middle_24.length=128 := by decide +kernel
theorem middle_24_count : middle_24.count 0=13 := by decide +kernel
theorem middle_24_root : (1:ℚ) ≤ (374218009311/500000000000000000:ℚ)^67*(12715:ℚ)^100 := by
  exact integer_negative_root 374218009311 500000000000000000 12715 100 67 (by decide) (by decide +kernel)

def middle_25 : List ℕ := [3,2,5,2,29,2,3,2,71,2,0,2,3,2,13,2,7,2,3,2,19,2,5,2,3,2,17,2,61,2,3,2,5,2,79,2,3,2,11,2,13,2,3,2,7,2,0,2,3,2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,0,2,37,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,7,2,67,2,3,2,5,2,17,2,3,2,0,2,7,2,3,2,11,2,23,2,3,2,0,2,5,2,3,2,0,2,13,2,3,2,5,2,0,2,3,2,7]
theorem middle_25_valid : SieveValid 12843 middle_25 := by decide +kernel
theorem middle_25_length : middle_25.length=129 := by decide +kernel
theorem middle_25_count : middle_25.count 0=13 := by decide +kernel
theorem middle_25_root : (1:ℚ) ≤ (368665052449/500000000000000000:ℚ)^67*(12843:ℚ)^100 := by
  exact integer_negative_root 368665052449 500000000000000000 12843 100 67 (by decide) (by decide +kernel)

def middle_26 : List ℕ := [2,0,2,3,2,19,2,0,2,3,2,0,2,5,2,3,2,31,2,11,2,3,2,5,2,41,2,3,2,0,2,0,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,47,2,29,2,3,2,5,2,7,2,3,2,83,2,0,2,3,2,0,2,13,2,3,2,0,2,5,2,3,2,0,2,31,2,3,2,5,2,11,2,3,2,37,2,0,2,3,2,73,2,7,2,3,2,17,2,5,2,3,2,11,2,103,2,3,2,5,2,23,2,3,2,13,2,0,2,3,2,7,2,0,2,3]
theorem middle_26_valid : SieveValid 12972 middle_26 := by decide +kernel
theorem middle_26_length : middle_26.length=130 := by decide +kernel
theorem middle_26_count : middle_26.count 0=14 := by decide +kernel
theorem middle_26_root : (1:ℚ) ≤ (90801638351/125000000000000000:ℚ)^67*(12972:ℚ)^100 := by
  exact integer_negative_root 90801638351 125000000000000000 12972 100 67 (by decide) (by decide +kernel)

def middle_27 : List ℕ := [2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,13,2,3,2,0,2,11,2,3,2,0,2,19,2,3,2,23,2,5,2,3,2,7,2,17,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,59,2,0,2,3,2,0,2,5,2,3,2,13,2,0,2,3,2,5,2,0,2,3,2,7,2,0,2,3,2,0,2,11,2,3,2,79,2,5,2,3,2,67,2,43,2,3,2,5,2,47,2,3,2,11,2,73,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,0,2,101,2,3]
theorem middle_27_valid : SieveValid 13102 middle_27 := by decide +kernel
theorem middle_27_length : middle_27.length=132 := by decide +kernel
theorem middle_27_count : middle_27.count 0=15 := by decide +kernel
theorem middle_27_root : (1:ℚ) ≤ (715681856363/1000000000000000000:ℚ)^67*(13102:ℚ)^100 := by
  exact integer_negative_root 715681856363 1000000000000000000 13102 100 67 (by decide) (by decide +kernel)

def middle_28 : List ℕ := [2,5,2,7,2,3,2,0,2,17,2,3,2,13,2,0,2,3,2,29,2,5,2,3,2,0,2,89,2,3,2,5,2,0,2,3,2,23,2,13,2,3,2,11,2,7,2,3,2,37,2,5,2,3,2,97,2,0,2,3,2,5,2,0,2,3,2,47,2,53,2,3,2,7,2,0,2,3,2,0,2,5,2,3,2,19,2,7,2,3,2,5,2,0,2,3,2,0,2,67,2,3,2,0,2,0,2,3,2,11,2,5,2,3,2,7,2,13,2,3,2,5,2,19,2,3,2,31,2,7,2,3,2]
theorem middle_28_valid : SieveValid 13234 middle_28 := by decide +kernel
theorem middle_28_length : middle_28.length=133 := by decide +kernel
theorem middle_28_count : middle_28.count 0=12 := by decide +kernel
theorem middle_28_root : (1:ℚ) ≤ (688529/976562500000:ℚ)^67*(13234:ℚ)^100 := by
  exact integer_negative_root 688529 976562500000 13234 100 67 (by decide) (by decide +kernel)

def middle_29 : List ℕ := [0,2,29,2,3,2,43,2,5,2,3,2,17,2,0,2,3,2,5,2,11,2,3,2,7,2,59,2,3,2,0,2,0,2,3,2,13,2,5,2,3,2,11,2,0,2,3,2,5,2,0,2,3,2,0,2,31,2,3,2,29,2,13,2,3,2,7,2,5,2,3,2,89,2,0,2,3,2,5,2,7,2,3,2,0,2,11,2,3,2,0,2,43,2,3,2,0,2,5,2,3,2,0,2,19,2,3,2,5,2,0,2,3,2,13,2,97,2,3,2,0,2,7,2,3,2,103,2,5,2,3,2,0,2]
theorem middle_29_valid : SieveValid 13367 middle_29 := by decide +kernel
theorem middle_29_length : middle_29.length=134 := by decide +kernel
theorem middle_29_count : middle_29.count 0=15 := by decide +kernel
theorem middle_29_root : (1:ℚ) ≤ (694608951871/1000000000000000000:ℚ)^67*(13367:ℚ)^100 := by
  exact integer_negative_root 694608951871 1000000000000000000 13367 100 67 (by decide) (by decide +kernel)

def middle_30 : List ℕ := [23,2,3,2,5,2,13,2,3,2,59,2,0,2,3,2,7,2,11,2,3,2,0,2,5,2,3,2,83,2,7,2,3,2,5,2,0,2,3,2,11,2,29,2,3,2,19,2,17,2,3,2,0,2,5,2,3,2,7,2,71,2,3,2,5,2,0,2,3,2,41,2,7,2,3,2,0,2,37,2,3,2,17,2,5,2,3,2,107,2,0,2,3,2,5,2,0,2,3,2,7,2,61,2,3,2,11,2,31,2,3,2,0,2,5,2,3,2,0,2,53,2,3,2,5,2,0,2,3,2,43,2,0,2,3,2]
theorem middle_30_valid : SieveValid 13501 middle_30 := by decide +kernel
theorem middle_30_length : middle_30.length=136 := by decide +kernel
theorem middle_30_count : middle_30.count 0=12 := by decide +kernel
theorem middle_30_root : (1:ℚ) ≤ (42771525269/62500000000000000:ℚ)^67*(13501:ℚ)^100 := by
  exact integer_negative_root 42771525269 62500000000000000 13501 100 67 (by decide) (by decide +kernel)

def middle_31 : List ℕ := [13,2,23,2,3,2,7,2,5,2,3,2,0,2,11,2,3,2,5,2,7,2,3,2,19,2,13,2,3,2,79,2,0,2,3,2,11,2,5,2,3,2,0,2,0,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,0,2,7,2,3,2,71,2,5,2,3,2,0,2,0,2,3,2,5,2,11,2,3,2,0,2,0,2,3,2,7,2,0,2,3,2,31,2,5,2,3,2,11,2,7,2,3,2,5,2,59,2,3,2,0,2,17,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,7,2,47,2,3]
theorem middle_31_valid : SieveValid 13637 middle_31 := by decide +kernel
theorem middle_31_length : middle_31.length=137 := by decide +kernel
theorem middle_31_count : middle_31.count 0=17 := by decide +kernel
theorem middle_31_root : (1:ℚ) ≤ (337091540919/500000000000000000:ℚ)^67*(13637:ℚ)^100 := by
  exact integer_negative_root 337091540919 500000000000000000 13637 100 67 (by decide) (by decide +kernel)

def middle_32 : List ℕ := [2,5,2,23,2,3,2,0,2,7,2,3,2,17,2,0,2,3,2,13,2,5,2,3,2,0,2,37,2,3,2,5,2,0,2,3,2,7,2,19,2,3,2,41,2,13,2,3,2,23,2,5,2,3,2,0,2,0,2,3,2,5,2,101,2,3,2,0,2,109,2,3,2,61,2,11,2,3,2,7,2,5,2,3,2,0,2,83,2,3,2,5,2,7,2,3,2,11,2,0,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,17,2,29,2,3,2,5,2,13,2,3,2,0,2,0,2,3,2,0,2,7,2,3]
theorem middle_32_valid : SieveValid 13774 middle_32 := by decide +kernel
theorem middle_32_length : middle_32.length=138 := by decide +kernel
theorem middle_32_count : middle_32.count 0=15 := by decide +kernel
theorem middle_32_root : (1:ℚ) ≤ (132839852817/200000000000000000:ℚ)^67*(13774:ℚ)^100 := by
  exact integer_negative_root 132839852817 200000000000000000 13774 100 67 (by decide) (by decide +kernel)

def middle_33 : List ℕ := [2,0,2,5,2,3,2,31,2,0,2,3,2,5,2,19,2,3,2,0,2,0,2,3,2,7,2,53,2,3,2,73,2,5,2,3,2,13,2,7,2,3,2,5,2,17,2,3,2,23,2,0,2,3,2,0,2,61,2,3,2,89,2,5,2,3,2,7,2,11,2,3,2,5,2,71,2,3,2,17,2,7,2,3,2,0,2,0,2,3,2,11,2,5,2,3,2,0,2,0,2,3,2,5,2,107,2,3,2,7,2,37,2,3,2,13,2,0,2,3,2,0,2,5,2,3,2,101,2,19,2,3,2,5,2,11,2,3,2,0]
theorem middle_33_valid : SieveValid 13912 middle_33 := by decide +kernel
theorem middle_33_length : middle_33.length=140 := by decide +kernel
theorem middle_33_count : middle_33.count 0=13 := by decide +kernel
theorem middle_33_root : (1:ℚ) ≤ (654389713867/1000000000000000000:ℚ)^67*(13912:ℚ)^100 := by
  exact integer_negative_root 654389713867 1000000000000000000 13912 100 67 (by decide) (by decide +kernel)

def middle_34 : List ℕ := [2,13,2,3,2,0,2,17,2,3,2,7,2,5,2,3,2,11,2,0,2,3,2,5,2,7,2,3,2,0,2,0,2,3,2,0,2,73,2,3,2,17,2,5,2,3,2,23,2,59,2,3,2,5,2,0,2,3,2,103,2,11,2,3,2,19,2,7,2,3,2,29,2,5,2,3,2,71,2,13,2,3,2,5,2,67,2,3,2,79,2,0,2,3,2,7,2,0,2,3,2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,31,2,3,2,37,2,0,2,3,2,0,2,11,2,3,2,13,2,5,2,3,2,7,2,23,2]
theorem middle_34_valid : SieveValid 14052 middle_34 := by decide +kernel
theorem middle_34_length : middle_34.length=141 := by decide +kernel
theorem middle_34_count : middle_34.count 0=12 := by decide +kernel
theorem middle_34_root : (1:ℚ) ≤ (32234138111/50000000000000000:ℚ)^67*(14052:ℚ)^100 := by
  exact integer_negative_root 32234138111 50000000000000000 14052 100 67 (by decide) (by decide +kernel)

def middle_35 : List ℕ := [3,2,5,2,0,2,3,2,11,2,7,2,3,2,0,2,13,2,3,2,61,2,5,2,3,2,59,2,0,2,3,2,5,2,41,2,3,2,7,2,43,2,3,2,23,2,29,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,53,2,3,2,13,2,17,2,3,2,11,2,19,2,3,2,7,2,5,2,3,2,109,2,0,2,3,2,5,2,7,2,3,2,31,2,0,2,3,2,17,2,79,2,3,2,0,2,5,2,3,2,41,2,11,2,3,2,5,2,103,2,3,2,0,2,0,2,3,2,0,2,7,2,3,2,11,2]
theorem middle_35_valid : SieveValid 14193 middle_35 := by decide +kernel
theorem middle_35_length : middle_35.length=142 := by decide +kernel
theorem middle_35_count : middle_35.count 0=12 := by decide +kernel
theorem middle_35_root : (1:ℚ) ≤ (317573553459/500000000000000000:ℚ)^67*(14193:ℚ)^100 := by
  exact integer_negative_root 317573553459 500000000000000000 14193 100 67 (by decide) (by decide +kernel)

def middle_36 : List ℕ := [5,2,3,2,13,2,0,2,3,2,5,2,0,2,3,2,113,2,31,2,3,2,7,2,83,2,3,2,53,2,5,2,3,2,0,2,7,2,3,2,5,2,11,2,3,2,73,2,19,2,3,2,0,2,0,2,3,2,37,2,5,2,3,2,7,2,0,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,13,2,0,2,3,2,0,2,5,2,3,2,47,2,0,2,3,2,5,2,0,2,3,2,7,2,11,2,3,2,0,2,0,2,3,2,97,2,5,2,3,2,19,2,0,2,3,2,5,2,17,2,3,2,29,2,41,2,3,2,31,2]
theorem middle_36_valid : SieveValid 14335 middle_36 := by decide +kernel
theorem middle_36_length : middle_36.length=144 := by decide +kernel
theorem middle_36_count : middle_36.count 0=15 := by decide +kernel
theorem middle_36_root : (1:ℚ) ≤ (625779522207/1000000000000000000:ℚ)^67*(14335:ℚ)^100 := by
  exact integer_negative_root 625779522207 1000000000000000000 14335 100 67 (by decide) (by decide +kernel)

def middle_37 : List ℕ := [0,2,3,2,7,2,5,2,3,2,0,2,43,2,3,2,5,2,7,2,3,2,17,2,0,2,3,2,89,2,11,2,3,2,23,2,5,2,3,2,0,2,13,2,3,2,5,2,73,2,3,2,11,2,0,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,7,2,17,2,3,2,13,2,5,2,3,2,61,2,7,2,3,2,5,2,29,2,3,2,0,2,0,2,3,2,11,2,13,2,3,2,17,2,5,2,3,2,7,2,19,2,3,2,5,2,47,2,3,2,0,2,7]
theorem middle_37_valid : SieveValid 14479 middle_37 := by decide +kernel
theorem middle_37_length : middle_37.length=145 := by decide +kernel
theorem middle_37_count : middle_37.count 0=15 := by decide +kernel
theorem middle_37_root : (1:ℚ) ≤ (616513279579/1000000000000000000:ℚ)^67*(14479:ℚ)^100 := by
  exact integer_negative_root 616513279579 1000000000000000000 14479 100 67 (by decide) (by decide +kernel)

def middle_38 : List ℕ := [2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,0,2,11,2,3,2,5,2,97,2,3,2,7,2,0,2,3,2,0,2,107,2,3,2,11,2,5,2,3,2,0,2,17,2,3,2,5,2,13,2,3,2,53,2,0,2,3,2,19,2,37,2,3,2,7,2,5,2,3,2,0,2,61,2,3,2,5,2,7,2,3,2,47,2,0,2,3,2,0,2,41,2,3,2,0,2,5,2,3,2,11,2,0,2,3,2,5,2,0,2,3,2,0,2,23,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,0,2,29,2,3,2,5,2,0,2,3,2]
theorem middle_38_valid : SieveValid 14624 middle_38 := by decide +kernel
theorem middle_38_length : middle_38.length=147 := by decide +kernel
theorem middle_38_count : middle_38.count 0=19 := by decide +kernel
theorem middle_38_root : (1:ℚ) ≤ (12148238553/20000000000000000:ℚ)^67*(14624:ℚ)^100 := by
  exact integer_negative_root 12148238553 20000000000000000 14624 100 67 (by decide) (by decide +kernel)

def middle_39 : List ℕ := [0,2,11,2,3,2,7,2,0,2,3,2,0,2,5,2,3,2,23,2,7,2,3,2,5,2,0,2,3,2,19,2,113,2,3,2,13,2,59,2,3,2,0,2,5,2,3,2,7,2,0,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,37,2,11,2,3,2,0,2,5,2,3,2,31,2,0,2,3,2,5,2,83,2,3,2,7,2,89,2,3,2,0,2,0,2,3,2,107,2,5,2,3,2,0,2,23,2,3,2,5,2,0,2,3,2,0,2,53,2,3,2,0,2,47,2,3,2,7,2,5,2,3,2,17,2,13,2,3,2,5,2,7,2]
theorem middle_39_valid : SieveValid 14771 middle_39 := by decide +kernel
theorem middle_39_length : middle_39.length=148 := by decide +kernel
theorem middle_39_count : middle_39.count 0=16 := by decide +kernel
theorem middle_39_root : (1:ℚ) ≤ (29920590227/50000000000000000:ℚ)^67*(14771:ℚ)^100 := by
  exact integer_negative_root 29920590227 50000000000000000 14771 100 67 (by decide) (by decide +kernel)

def middle_40 : List ℕ := [3,2,43,2,0,2,3,2,11,2,0,2,3,2,109,2,5,2,3,2,0,2,67,2,3,2,5,2,0,2,3,2,0,2,19,2,3,2,0,2,7,2,3,2,13,2,5,2,3,2,0,2,11,2,3,2,5,2,17,2,3,2,71,2,0,2,3,2,7,2,13,2,3,2,11,2,5,2,3,2,53,2,7,2,3,2,5,2,43,2,3,2,17,2,0,2,3,2,0,2,23,2,3,2,83,2,5,2,3,2,7,2,0,2,3,2,5,2,11,2,3,2,13,2,7,2,3,2,41,2,101,2,3,2,0,2,5,2,3,2,11,2,0,2,3,2,5,2,13,2]
theorem middle_40_valid : SieveValid 14919 middle_40 := by decide +kernel
theorem middle_40_length : middle_40.length=150 := by decide +kernel
theorem middle_40_count : middle_40.count 0=13 := by decide +kernel
theorem middle_40_root : (1:ℚ) ≤ (147393302249/250000000000000000:ℚ)^67*(14919:ℚ)^100 := by
  exact integer_negative_root 147393302249 250000000000000000 14919 100 67 (by decide) (by decide +kernel)

def middle_41 : List ℕ := [3,2,7,2,0,2,3,2,0,2,17,2,3,2,0,2,5,2,3,2,79,2,0,2,3,2,5,2,31,2,3,2,0,2,11,2,3,2,0,2,29,2,3,2,7,2,5,2,3,2,13,2,0,2,3,2,5,2,7,2,3,2,0,2,37,2,3,2,0,2,0,2,3,2,19,2,5,2,3,2,0,2,109,2,3,2,5,2,23,2,3,2,0,2,59,2,3,2,29,2,7,2,3,2,0,2,5,2,3,2,43,2,17,2,3,2,5,2,0,2,3,2,11,2,0,2,3,2,7,2,0,2,3,2,23,2,5,2,3,2,67,2,7,2,3,2,5,2,0,2,3]
theorem middle_41_valid : SieveValid 15069 middle_41 := by decide +kernel
theorem middle_41_length : middle_41.length=151 := by decide +kernel
theorem middle_41_count : middle_41.count 0=17 := by decide +kernel
theorem middle_41_root : (1:ℚ) ≤ (290417705311/500000000000000000:ℚ)^67*(15069:ℚ)^100 := by
  exact integer_negative_root 290417705311 500000000000000000 15069 100 67 (by decide) (by decide +kernel)

def middle_42 : List ℕ := [2,31,2,13,2,3,2,0,2,97,2,3,2,0,2,5,2,3,2,7,2,0,2,3,2,5,2,79,2,3,2,101,2,7,2,3,2,11,2,0,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,0,2,3,2,7,2,17,2,3,2,0,2,0,2,3,2,41,2,5,2,3,2,0,2,11,2,3,2,5,2,0,2,3,2,61,2,0,2,3,2,17,2,0,2,3,2,7,2,5,2,3,2,0,2,0,2,3,2,5,2,7,2,3,2,23,2,67,2,3,2,103,2,0,2,3,2,13,2,5,2,3,2,0,2,0,2,3,2,5,2,11,2,3,2,19,2]
theorem middle_42_valid : SieveValid 15220 middle_42 := by decide +kernel
theorem middle_42_length : middle_42.length=153 := by decide +kernel
theorem middle_42_count : middle_42.count 0=19 := by decide +kernel
theorem middle_42_root : (1:ℚ) ≤ (286127812973/500000000000000000:ℚ)^67*(15220:ℚ)^100 := by
  exact integer_negative_root 286127812973 500000000000000000 15220 100 67 (by decide) (by decide +kernel)

def middle_43 : List ℕ := [0,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,11,2,0,2,3,2,5,2,89,2,3,2,0,2,73,2,3,2,7,2,19,2,3,2,0,2,5,2,3,2,17,2,7,2,3,2,5,2,0,2,3,2,13,2,11,2,3,2,43,2,0,2,3,2,0,2,5,2,3,2,7,2,0,2,3,2,5,2,13,2,3,2,0,2,7,2,3,2,0,2,31,2,3,2,0,2,5,2,3,2,23,2,113,2,3,2,5,2,17,2,3,2,7,2,0,2,3,2,0,2,11,2,3,2,37,2,5,2,3,2,13,2,0,2,3,2,5,2,59,2,3,2,11,2,19,2,3,2]
theorem middle_43_valid : SieveValid 15373 middle_43 := by decide +kernel
theorem middle_43_length : middle_43.length=154 := by decide +kernel
theorem middle_43_count : middle_43.count 0=16 := by decide +kernel
theorem middle_43_root : (1:ℚ) ≤ (563775925519/1000000000000000000:ℚ)^67*(15373:ℚ)^100 := by
  exact integer_negative_root 563775925519 1000000000000000000 15373 100 67 (by decide) (by decide +kernel)

def middle_44 : List ℕ := [0,2,53,2,3,2,7,2,5,2,3,2,41,2,0,2,3,2,5,2,7,2,3,2,0,2,103,2,3,2,47,2,0,2,3,2,79,2,5,2,3,2,0,2,23,2,3,2,5,2,37,2,3,2,0,2,0,2,3,2,11,2,7,2,3,2,31,2,5,2,3,2,19,2,0,2,3,2,5,2,0,2,3,2,67,2,13,2,3,2,7,2,0,2,3,2,17,2,5,2,3,2,0,2,7,2,3,2,5,2,19,2,3,2,0,2,0,2,3,2,0,2,0,2,3,2,11,2,5,2,3,2,7,2,0,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,61,2,0,2,3,2]
theorem middle_44_valid : SieveValid 15527 middle_44 := by decide +kernel
theorem middle_44_length : middle_44.length=156 := by decide +kernel
theorem middle_44_count : middle_44.count 0=19 := by decide +kernel
theorem middle_44_root : (1:ℚ) ≤ (111090120779/200000000000000000:ℚ)^67*(15527:ℚ)^100 := by
  exact integer_negative_root 111090120779 200000000000000000 15527 100 67 (by decide) (by decide +kernel)

def middle_45 : List ℕ := [0,2,5,2,3,2,29,2,13,2,3,2,5,2,11,2,3,2,7,2,41,2,3,2,113,2,23,2,3,2,19,2,5,2,3,2,11,2,79,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,0,2,19,2,3,2,5,2,7,2,3,2,0,2,11,2,3,2,0,2,13,2,3,2,0,2,5,2,3,2,31,2,43,2,3,2,5,2,0,2,3,2,0,2,17,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,0,2,97,2,3,2,5,2,0,2,3,2,13,2,0,2,3,2,7,2,11,2,3,2,71,2,5,2,3,2,47]
theorem middle_45_valid : SieveValid 15683 middle_45 := by decide +kernel
theorem middle_45_length : middle_45.length=157 := by decide +kernel
theorem middle_45_count : middle_45.count 0=17 := by decide +kernel
theorem middle_45_root : (1:ℚ) ≤ (547224406639/1000000000000000000:ℚ)^67*(15683:ℚ)^100 := by
  exact integer_negative_root 547224406639 1000000000000000000 15683 100 67 (by decide) (by decide +kernel)

def middle_46 : List ℕ := [2,7,2,3,2,5,2,13,2,3,2,11,2,83,2,3,2,101,2,0,2,3,2,29,2,5,2,3,2,7,2,59,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,0,2,0,2,3,2,23,2,5,2,3,2,13,2,0,2,3,2,5,2,0,2,3,2,7,2,0,2,3,2,11,2,0,2,3,2,0,2,5,2,3,2,17,2,89,2,3,2,5,2,0,2,3,2,19,2,107,2,3,2,37,2,41,2,3,2,7,2,5,2,3,2,0,2,11,2,3,2,5,2,7,2,3,2,0,2,0,2,3,2,13,2,19,2,3,2,11,2,5,2,3,2,59,2,0,2,3,2,5,2,17,2]
theorem middle_46_valid : SieveValid 15840 middle_46 := by decide +kernel
theorem middle_46_length : middle_46.length=159 := by decide +kernel
theorem middle_46_count : middle_46.count 0=15 := by decide +kernel
theorem middle_46_root : (1:ℚ) ≤ (53914885927/100000000000000000:ℚ)^67*(15840:ℚ)^100 := by
  exact integer_negative_root 53914885927 100000000000000000 15840 100 67 (by decide) (by decide +kernel)

def middle_47 : List ℕ := [3,2,0,2,13,2,3,2,0,2,7,2,3,2,67,2,5,2,3,2,83,2,37,2,3,2,5,2,11,2,3,2,17,2,0,2,3,2,7,2,43,2,3,2,61,2,5,2,3,2,11,2,7,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,7,2,13,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,0,2,17,2,3,2,0,2,5,2,3,2,89,2,0,2,3,2,5,2,71,2,3,2,7,2,23,2,3,2,0,2,127,2,3,2,13,2,5,2,3,2,0,2,0,2,3,2,5,2,67,2,3,2,31,2,29,2,3,2,107,2]
theorem middle_47_valid : SieveValid 15999 middle_47 := by decide +kernel
theorem middle_47_length : middle_47.length=160 := by decide +kernel
theorem middle_47_count : middle_47.count 0=17 := by decide +kernel
theorem middle_47_root : (1:ℚ) ≤ (66396407631/125000000000000000:ℚ)^67*(15999:ℚ)^100 := by
  exact integer_negative_root 66396407631 125000000000000000 15999 100 67 (by decide) (by decide +kernel)

def middle_48 : List ℕ := [11,2,3,2,7,2,5,2,3,2,19,2,103,2,3,2,5,2,7,2,3,2,11,2,0,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,97,2,17,2,3,2,5,2,19,2,3,2,13,2,31,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,13,2,3,2,109,2,37,2,3,2,7,2,0,2,3,2,0,2,5,2,3,2,71,2,7,2,3,2,5,2,0,2,3,2,53,2,0,2,3,2,41,2,73,2,3,2,19,2,5,2,3,2,7,2,11,2,3,2,5,2,43,2,3,2,0,2,7,2,3,2,23,2,47,2,3,2,11,2,5,2,3,2,0,2]
theorem middle_48_valid : SieveValid 16159 middle_48 := by decide +kernel
theorem middle_48_length : middle_48.length=162 := by decide +kernel
theorem middle_48_count : middle_48.count 0=14 := by decide +kernel
theorem middle_48_root : (1:ℚ) ≤ (523340514219/1000000000000000000:ℚ)^67*(16159:ℚ)^100 := by
  exact integer_negative_root 523340514219 1000000000000000000 16159 100 67 (by decide) (by decide +kernel)

def middle_49 : List ℕ := [19,2,3,2,5,2,29,2,3,2,7,2,0,2,3,2,17,2,0,2,3,2,59,2,5,2,3,2,0,2,83,2,3,2,5,2,11,2,3,2,0,2,0,2,3,2,13,2,0,2,3,2,7,2,5,2,3,2,11,2,0,2,3,2,5,2,7,2,3,2,37,2,13,2,3,2,19,2,23,2,3,2,47,2,5,2,3,2,61,2,0,2,3,2,5,2,0,2,3,2,0,2,11,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,17,2,41,2,3,2,5,2,0,2,3,2,0,2,0,2,3,2,7,2,109,2,3,2,101,2,5,2,3,2,43,2,7,2,3,2,5,2,0,2,3,2,0,2,53,2]
theorem middle_49_valid : SieveValid 16321 middle_49 := by decide +kernel
theorem middle_49_length : middle_49.length=164 := by decide +kernel
theorem middle_49_count : middle_49.count 0=17 := by decide +kernel
theorem middle_49_root : (1:ℚ) ≤ (257803177497/500000000000000000:ℚ)^67*(16321:ℚ)^100 := by
  exact integer_negative_root 257803177497 500000000000000000 16321 100 67 (by decide) (by decide +kernel)

def middle_50 : List ℕ := [3,2,0,2,11,2,3,2,0,2,5,2,3,2,7,2,29,2,3,2,5,2,17,2,3,2,11,2,7,2,3,2,83,2,0,2,3,2,13,2,5,2,3,2,0,2,61,2,3,2,5,2,23,2,3,2,7,2,71,2,3,2,0,2,13,2,3,2,0,2,5,2,3,2,29,2,0,2,3,2,5,2,0,2,3,2,73,2,0,2,3,2,11,2,59,2,3,2,7,2,5,2,3,2,53,2,47,2,3,2,5,2,7,2,3,2,13,2,0,2,3,2,0,2,17,2,3,2,37,2,5,2,3,2,0,2,11,2,3,2,5,2,13,2,3,2,0,2,0,2,3,2,127,2,7,2,3,2,11,2,5,2,3,2,0]
theorem middle_50_valid : SieveValid 16485 middle_50 := by decide +kernel
theorem middle_50_length : middle_50.length=165 := by decide +kernel
theorem middle_50_count : middle_50.count 0=15 := by decide +kernel
theorem middle_50_root : (1:ℚ) ≤ (253984603279/500000000000000000:ℚ)^67*(16485:ℚ)^100 := by
  exact integer_negative_root 253984603279 500000000000000000 16485 100 67 (by decide) (by decide +kernel)

def middle_51 : List ℕ := [2,0,2,3,2,5,2,0,2,3,2,0,2,19,2,3,2,7,2,79,2,3,2,0,2,5,2,3,2,13,2,7,2,3,2,5,2,11,2,3,2,0,2,0,2,3,2,59,2,0,2,3,2,0,2,5,2,3,2,7,2,17,2,3,2,5,2,73,2,3,2,23,2,7,2,3,2,43,2,0,2,3,2,29,2,5,2,3,2,19,2,0,2,3,2,5,2,0,2,3,2,7,2,11,2,3,2,13,2,0,2,3,2,0,2,5,2,3,2,41,2,31,2,3,2,5,2,19,2,3,2,97,2,13,2,3,2,0,2,103,2,3,2,7,2,5,2,3,2,107,2,53,2,3,2,5,2,7,2,3,2,0,2,17,2,3,2]
theorem middle_51_valid : SieveValid 16650 middle_51 := by decide +kernel
theorem middle_51_length : middle_51.length=167 := by decide +kernel
theorem middle_51_count : middle_51.count 0=15 := by decide +kernel
theorem middle_51_root : (1:ℚ) ≤ (500474246711/1000000000000000000:ℚ)^67*(16650:ℚ)^100 := by
  exact integer_negative_root 500474246711 1000000000000000000 16650 100 67 (by decide) (by decide +kernel)

def middle_52 : List ℕ := [67,2,11,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,113,2,3,2,11,2,0,2,3,2,17,2,7,2,3,2,19,2,5,2,3,2,23,2,13,2,3,2,5,2,101,2,3,2,0,2,47,2,3,2,7,2,0,2,3,2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,61,2,3,2,0,2,0,2,3,2,11,2,37,2,3,2,13,2,5,2,3,2,7,2,0,2,3,2,5,2,0,2,3,2,0,2,7,2,3,2,0,2,13,2,3,2,0,2,5,2,3,2,17,2,11,2,3,2,5,2,31,2,3,2,7,2,0,2,3,2,19,2,71,2,3,2,11,2,5,2,3,2,0,2,0,2,3,2,5]
theorem middle_52_valid : SieveValid 16817 middle_52 := by decide +kernel
theorem middle_52_length : middle_52.length=169 := by decide +kernel
theorem middle_52_count : middle_52.count 0=18 := by decide +kernel
theorem middle_52_root : (1:ℚ) ≤ (61634327753/125000000000000000:ℚ)^67*(16817:ℚ)^100 := by
  exact integer_negative_root 61634327753 125000000000000000 16817 100 67 (by decide) (by decide +kernel)

def middle_53 : List ℕ := [2,0,2,3,2,13,2,0,2,3,2,23,2,89,2,3,2,7,2,5,2,3,2,73,2,0,2,3,2,5,2,7,2,3,2,0,2,29,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,11,2,0,2,3,2,5,2,0,2,3,2,17,2,0,2,3,2,37,2,7,2,3,2,113,2,5,2,3,2,13,2,43,2,3,2,5,2,0,2,3,2,19,2,11,2,3,2,7,2,23,2,3,2,0,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,71,2,109,2,3,2,0,2,17,2,3,2,0,2,5,2,3,2,7,2,37,2,3,2,5,2,0,2,3,2,61,2,7,2,3,2,13,2,11,2,3,2,17,2,5]
theorem middle_53_valid : SieveValid 16986 middle_53 := by decide +kernel
theorem middle_53_length : middle_53.length=170 := by decide +kernel
theorem middle_53_count : middle_53.count 0=17 := by decide +kernel
theorem middle_53_root : (1:ℚ) ≤ (15180329077/31250000000000000:ℚ)^67*(16986:ℚ)^100 := by
  exact integer_negative_root 15180329077 31250000000000000 16986 100 67 (by decide) (by decide +kernel)

def middle_54 : List ℕ := [2,3,2,0,2,131,2,3,2,5,2,0,2,3,2,7,2,13,2,3,2,89,2,41,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,29,2,3,2,103,2,0,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,67,2,17,2,3,2,5,2,7,2,3,2,0,2,19,2,3,2,11,2,0,2,3,2,43,2,5,2,3,2,47,2,13,2,3,2,5,2,0,2,3,2,41,2,61,2,3,2,31,2,7,2,3,2,23,2,5,2,3,2,37,2,11,2,3,2,5,2,59,2,3,2,0,2,0,2,3,2,7,2,0,2,3,2,11,2,5,2,3,2,19,2,7,2,3,2,5,2,0,2,3,2,0,2,17,2,3,2,0]
theorem middle_54_valid : SieveValid 17156 middle_54 := by decide +kernel
theorem middle_54_length : middle_54.length=172 := by decide +kernel
theorem middle_54_count : middle_54.count 0=17 := by decide +kernel
theorem middle_54_root : (1:ℚ) ≤ (119650928193/250000000000000000:ℚ)^67*(17156:ℚ)^100 := by
  exact integer_negative_root 119650928193 250000000000000000 17156 100 67 (by decide) (by decide +kernel)

def middle_55 : List ℕ := [2,13,2,3,2,0,2,5,2,3,2,7,2,0,2,3,2,5,2,11,2,3,2,0,2,7,2,3,2,17,2,0,2,3,2,97,2,5,2,3,2,11,2,29,2,3,2,5,2,0,2,3,2,7,2,0,2,3,2,0,2,0,2,3,2,0,2,5,2,3,2,127,2,0,2,3,2,5,2,13,2,3,2,23,2,11,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,29,2,0,2,3,2,5,2,7,2,3,2,107,2,0,2,3,2,73,2,0,2,3,2,31,2,5,2,3,2,13,2,19,2,3,2,5,2,0,2,3,2,0,2,101,2,3,2,0,2,7,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,0,2,3,2,11]
theorem middle_55_valid : SieveValid 17328 middle_55 := by decide +kernel
theorem middle_55_length : middle_55.length=174 := by decide +kernel
theorem middle_55_count : middle_55.count 0=22 := by decide +kernel
theorem middle_55_root : (1:ℚ) ≤ (235765251451/500000000000000000:ℚ)^67*(17328:ℚ)^100 := by
  exact integer_negative_root 235765251451 500000000000000000 17328 100 67 (by decide) (by decide +kernel)

def middle_56 : List ℕ := [2,23,2,3,2,7,2,0,2,3,2,83,2,5,2,3,2,0,2,7,2,3,2,5,2,17,2,3,2,47,2,89,2,3,2,13,2,0,2,3,2,53,2,5,2,3,2,7,2,0,2,3,2,5,2,97,2,3,2,17,2,7,2,3,2,11,2,0,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,43,2,3,2,7,2,73,2,3,2,0,2,0,2,3,2,29,2,5,2,3,2,0,2,11,2,3,2,5,2,79,2,3,2,67,2,0,2,3,2,0,2,17,2,3,2,7,2,5,2,3,2,31,2,13,2,3,2,5,2,7,2,3,2,19,2,127,2,3,2,0,2,0,2,3,2,17,2,5,2,3,2,0,2,41,2,3,2,5,2,11]
theorem middle_56_valid : SieveValid 17502 middle_56 := by decide +kernel
theorem middle_56_length : middle_56.length=176 := by decide +kernel
theorem middle_56_count : middle_56.count 0=16 := by decide +kernel
theorem middle_56_root : (1:ℚ) ≤ (464550908959/1000000000000000000:ℚ)^67*(17502:ℚ)^100 := by
  exact integer_negative_root 464550908959 1000000000000000000 17502 100 67 (by decide) (by decide +kernel)

def middle_57 : List ℕ := [2,3,2,0,2,0,2,3,2,23,2,7,2,3,2,13,2,5,2,3,2,11,2,31,2,3,2,5,2,0,2,3,2,89,2,0,2,3,2,7,2,13,2,3,2,37,2,5,2,3,2,0,2,7,2,3,2,5,2,0,2,3,2,113,2,11,2,3,2,0,2,0,2,3,2,41,2,5,2,3,2,7,2,0,2,3,2,5,2,109,2,3,2,13,2,7,2,3,2,29,2,23,2,3,2,0,2,5,2,3,2,0,2,0,2,3,2,5,2,13,2,3,2,7,2,19,2,3,2,0,2,11,2,3,2,47,2,5,2,3,2,103,2,71,2,3,2,5,2,0,2,3,2,11,2,17,2,3,2,0,2,0,2,3,2,7,2,5,2,3,2,13,2,0,2,3,2]
theorem middle_57_valid : SieveValid 17678 middle_57 := by decide +kernel
theorem middle_57_length : middle_57.length=177 := by decide +kernel
theorem middle_57_count : middle_57.count 0=17 := by decide +kernel
theorem middle_57_root : (1:ℚ) ≤ (457664859691/1000000000000000000:ℚ)^67*(17678:ℚ)^100 := by
  exact integer_negative_root 457664859691 1000000000000000000 17678 100 67 (by decide) (by decide +kernel)

end LonelyRunnerNew.LCNumeric.SieveData
