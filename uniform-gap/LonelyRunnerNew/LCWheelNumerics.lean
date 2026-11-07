import LonelyRunnerNew.LCPrimeTail

namespace LonelyRunnerNew.LCNumeric
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def tailCoefficient : ℚ := 3025857/250000

def wheelUpper_1 : ℚ := (74277839743566083/990000000000000000000:ℚ)
theorem wheel_point_1 : (1:ℚ) ≤ (1108618071/1000000000000000000:ℚ)^67*(999991:ℚ)^100 := by norm_num
theorem wheel_integral_1 : (1:ℚ) ≤ (1108608092711579/1000000000000000000:ℚ)^67*(999991:ℚ)^33 := by norm_num
theorem wheel_bound_1 : (999991:ℝ)^(-(100:ℝ)/67)+
    (999991:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_1:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<999991) (by norm_num : (0:ℝ)<(1108618071/1000000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_1)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<999991) (by norm_num : (0:ℝ)<(1108608092711579/1000000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_1)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (999991:ℝ)^(1-(100:ℝ)/67)=(999991:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((1108618071/1000000000000000000:ℚ):ℝ)+((1108608092711579/1000000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_1:ℝ) := by norm_num [wheelUpper_1]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper_7 : ℚ := (74277620228342321/990000000000000000000:ℚ)
theorem wheel_point_7 : (1:ℚ) ≤ (1108608143/1000000000000000000:ℚ)^67*(999997:ℚ)^100 := by norm_num
theorem wheel_integral_7 : (1:ℚ) ≤ (1108604816511653/1000000000000000000:ℚ)^67*(999997:ℚ)^33 := by norm_num
theorem wheel_bound_7 : (999997:ℝ)^(-(100:ℝ)/67)+
    (999997:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_7:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<999997) (by norm_num : (0:ℝ)<(1108608143/1000000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_7)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<999997) (by norm_num : (0:ℝ)<(1108604816511653/1000000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_7)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (999997:ℝ)^(1-(100:ℝ)/67)=(999997:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((1108608143/1000000000000000000:ℚ):ℝ)+((1108604816511653/1000000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_7:ℝ) := by norm_num [wheelUpper_7]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper_11 : ℚ := (18569368471487879/247500000000000000000:ℚ)
theorem wheel_point_11 : (1:ℚ) ≤ (277150381/250000000000000000:ℚ)^67*(1000001:ℚ)^100 := by norm_num
theorem wheel_integral_11 : (1:ℚ) ≤ (277150658098667/250000000000000000:ℚ)^67*(1000001:ℚ)^33 := by norm_num
theorem wheel_bound_11 : (1000001:ℝ)^(-(100:ℝ)/67)+
    (1000001:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_11:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<1000001) (by norm_num : (0:ℝ)<(277150381/250000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_11)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<1000001) (by norm_num : (0:ℝ)<(277150658098667/250000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_11)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (1000001:ℝ)^(1-(100:ℝ)/67)=(1000001:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((277150381/250000000000000000:ℚ):ℝ)+((277150658098667/250000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_11:ℝ) := by norm_num [wheelUpper_11]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper_13 : ℚ := (4642337544692767/61875000000000000000:ℚ)
theorem wheel_point_13 : (1:ℚ) ≤ (221719643/200000000000000000:ℚ)^67*(1000003:ℚ)^100 := by norm_num
theorem wheel_integral_13 : (1:ℚ) ≤ (554300770170533/500000000000000000:ℚ)^67*(1000003:ℚ)^33 := by norm_num
theorem wheel_bound_13 : (1000003:ℝ)^(-(100:ℝ)/67)+
    (1000003:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_13:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<1000003) (by norm_num : (0:ℝ)<(221719643/200000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_13)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<1000003) (by norm_num : (0:ℝ)<(554300770170533/500000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_13)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (1000003:ℝ)^(1-(100:ℝ)/67)=(1000003:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((221719643/200000000000000000:ℚ):ℝ)+((554300770170533/500000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_13:ℝ) := by norm_num [wheelUpper_13]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper_17 : ℚ := (2475908479133497/33000000000000000000:ℚ)
theorem wheel_point_17 : (1:ℚ) ≤ (1108591597/1000000000000000000:ℚ)^67*(1000007:ℚ)^100 := by norm_num
theorem wheel_integral_17 : (1:ℚ) ≤ (27714983906091/25000000000000000:ℚ)^67*(1000007:ℚ)^33 := by norm_num
theorem wheel_bound_17 : (1000007:ℝ)^(-(100:ℝ)/67)+
    (1000007:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_17:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<1000007) (by norm_num : (0:ℝ)<(1108591597/1000000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_17)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<1000007) (by norm_num : (0:ℝ)<(27714983906091/25000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_17)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (1000007:ℝ)^(1-(100:ℝ)/67)=(1000007:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((1108591597/1000000000000000000:ℚ):ℝ)+((27714983906091/25000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_17:ℝ) := by norm_num [wheelUpper_17]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper_19 : ℚ := (74277181203791869/990000000000000000000:ℚ)
theorem wheel_point_19 : (1:ℚ) ≤ (1108588287/1000000000000000000:ℚ)^67*(1000009:ℚ)^100 := by norm_num
theorem wheel_integral_19 : (1:ℚ) ≤ (1108598264199817/1000000000000000000:ℚ)^67*(1000009:ℚ)^33 := by norm_num
theorem wheel_bound_19 : (1000009:ℝ)^(-(100:ℝ)/67)+
    (1000009:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_19:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<1000009) (by norm_num : (0:ℝ)<(1108588287/1000000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_19)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<1000009) (by norm_num : (0:ℝ)<(1108598264199817/1000000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_19)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (1000009:ℝ)^(1-(100:ℝ)/67)=(1000009:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((1108588287/1000000000000000000:ℚ):ℝ)+((1108598264199817/1000000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_19:ℝ) := by norm_num [wheelUpper_19]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper_23 : ℚ := (24759011621341009/330000000000000000000:ℚ)
theorem wheel_point_23 : (1:ℚ) ≤ (1108581669/1000000000000000000:ℚ)^67*(1000013:ℚ)^100 := by norm_num
theorem wheel_integral_23 : (1:ℚ) ≤ (1108596080121951/1000000000000000000:ℚ)^67*(1000013:ℚ)^33 := by norm_num
theorem wheel_bound_23 : (1000013:ℝ)^(-(100:ℝ)/67)+
    (1000013:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_23:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<1000013) (by norm_num : (0:ℝ)<(1108581669/1000000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_23)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<1000013) (by norm_num : (0:ℝ)<(1108596080121951/1000000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_23)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (1000013:ℝ)^(1-(100:ℝ)/67)=(1000013:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((1108581669/1000000000000000000:ℚ):ℝ)+((1108596080121951/1000000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_23:ℝ) := by norm_num [wheelUpper_23]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper_29 : ℚ := (8252979484000857/110000000000000000000:ℚ)
theorem wheel_point_29 : (1:ℚ) ≤ (554285871/500000000000000000:ℚ)^67*(1000019:ℚ)^100 := by norm_num
theorem wheel_integral_29 : (1:ℚ) ≤ (1108592804029599/1000000000000000000:ℚ)^67*(1000019:ℚ)^33 := by norm_num
theorem wheel_bound_29 : (1000019:ℝ)^(-(100:ℝ)/67)+
    (1000019:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper_29:ℝ) := by
  have hp := negative_power_upper (by norm_num : (0:ℝ)<1000019) (by norm_num : (0:ℝ)<(554285871/500000000000000000:ℚ)) 100 67 (by decide)
    (by exact_mod_cast wheel_point_29)
  have hi := negative_power_upper (by norm_num : (0:ℝ)<1000019) (by norm_num : (0:ℝ)<(1108592804029599/1000000000000000000:ℚ)) 33 67 (by decide)
    (by exact_mod_cast wheel_integral_29)
  norm_num only [Nat.cast_ofNat] at hp hi
  have he : (1000019:ℝ)^(1-(100:ℝ)/67)=(1000019:ℝ)^(-(33:ℝ)/67) := by congr 1; norm_num
  rw [he]
  have hp2 := div_le_div_of_nonneg_right hi (by norm_num : (0:ℝ)≤30*((100:ℝ)/67-1))
  have he2 : ((554285871/500000000000000000:ℚ):ℝ)+((1108592804029599/1000000000000000000:ℚ):ℝ)/(30*((100:ℝ)/67-1))=(wheelUpper_29:ℝ) := by norm_num [wheelUpper_29]
  apply le_trans (add_le_add (by simpa only [neg_div] using hp) (by simpa only [neg_div] using hp2))
  push_cast at he2
  exact le_of_eq he2

def wheelUpper (r : ℕ) : ℚ := if r=1 then wheelUpper_1 else if r=7 then wheelUpper_7 else if r=11 then wheelUpper_11 else if r=13 then wheelUpper_13 else if r=17 then wheelUpper_17 else if r=19 then wheelUpper_19 else if r=23 then wheelUpper_23 else if r=29 then wheelUpper_29 else 0
theorem wheel_upper_sound (r : ℕ) (hr : r ∈ wheelResidues) :
  (wheelBase r:ℝ)^(-(100:ℝ)/67)+(wheelBase r:ℝ)^(1-(100:ℝ)/67)/(30*((100:ℝ)/67-1)) ≤ (wheelUpper r:ℝ) := by
  simp only [wheelResidues,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [wheelBase,wheelUpper] using wheel_bound_1
  · simpa [wheelBase,wheelUpper] using wheel_bound_7
  · simpa [wheelBase,wheelUpper] using wheel_bound_11
  · simpa [wheelBase,wheelUpper] using wheel_bound_13
  · simpa [wheelBase,wheelUpper] using wheel_bound_17
  · simpa [wheelBase,wheelUpper] using wheel_bound_19
  · simpa [wheelBase,wheelUpper] using wheel_bound_23
  · simpa [wheelBase,wheelUpper] using wheel_bound_29

theorem wheel_numeric_budget :
  (tailCoefficient:ℝ)*(∑ r ∈ wheelResidues,(wheelUpper r:ℝ)) < (1/125:ℝ) := by
  norm_num [tailCoefficient,wheelResidues,wheelUpper,wheelUpper_1,wheelUpper_7,wheelUpper_11,wheelUpper_13,wheelUpper_17,wheelUpper_19,wheelUpper_23,wheelUpper_29]

theorem prime_tail_numeric_budget (P : Finset ℕ)
    (hP : ∀ p ∈ P,Nat.Prime p ∧ 1000000<p) :
    (tailCoefficient:ℝ)*(∑ p ∈ P,(p:ℝ)^(-(100:ℝ)/67)) < (1/125:ℝ) := by
  have hh := (prime_wheel_sum P hP).trans (Finset.sum_le_sum (fun r hr => wheel_upper_sound r hr))
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num [tailCoefficient] : (0:ℝ)≤tailCoefficient)
  exact hm.trans_lt wheel_numeric_budget

end LonelyRunnerNew.LCNumeric
