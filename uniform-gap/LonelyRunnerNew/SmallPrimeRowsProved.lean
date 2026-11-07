import LonelyRunnerNew.SmallPrimeRowData0
import LonelyRunnerNew.SmallPrimeRowData1
import LonelyRunnerNew.SmallPrimeRowData2
import LonelyRunnerNew.SmallPrimeRowData3
import LonelyRunnerNew.SmallPrimeRowData4
import LonelyRunnerNew.SmallPrimeRowData5
import LonelyRunnerNew.SmallPrimeRowData6

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.Certificate
set_option maxRecDepth 16384
theorem frozen_analytic_rows_checked : ∀ r∈rows,∃ w : AnalyticWitness,w.Valid r := by
  intro r hr
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨analyticWitness_0,analyticRow_0_checked⟩
  · exact ⟨analyticWitness_1,analyticRow_1_checked⟩
  · exact ⟨analyticWitness_2,analyticRow_2_checked⟩
  · exact ⟨analyticWitness_3,analyticRow_3_checked⟩
  · exact ⟨analyticWitness_4,analyticRow_4_checked⟩
  · exact ⟨analyticWitness_5,analyticRow_5_checked⟩
  · exact ⟨analyticWitness_6,analyticRow_6_checked⟩
  · exact ⟨analyticWitness_7,analyticRow_7_checked⟩
  · exact ⟨analyticWitness_8,analyticRow_8_checked⟩
  · exact ⟨analyticWitness_9,analyticRow_9_checked⟩
  · exact ⟨analyticWitness_10,analyticRow_10_checked⟩
  · exact ⟨analyticWitness_11,analyticRow_11_checked⟩
  · exact ⟨analyticWitness_12,analyticRow_12_checked⟩
  · exact ⟨analyticWitness_13,analyticRow_13_checked⟩
  · exact ⟨analyticWitness_14,analyticRow_14_checked⟩
  · exact ⟨analyticWitness_15,analyticRow_15_checked⟩
  · exact ⟨analyticWitness_16,analyticRow_16_checked⟩
  · exact ⟨analyticWitness_17,analyticRow_17_checked⟩
  · exact ⟨analyticWitness_18,analyticRow_18_checked⟩
  · exact ⟨analyticWitness_19,analyticRow_19_checked⟩
  · exact ⟨analyticWitness_20,analyticRow_20_checked⟩
  · exact ⟨analyticWitness_21,analyticRow_21_checked⟩
  · exact ⟨analyticWitness_22,analyticRow_22_checked⟩
  · exact ⟨analyticWitness_23,analyticRow_23_checked⟩
  · exact ⟨analyticWitness_24,analyticRow_24_checked⟩
  · exact ⟨analyticWitness_25,analyticRow_25_checked⟩
  · exact ⟨analyticWitness_26,analyticRow_26_checked⟩
  · exact ⟨analyticWitness_27,analyticRow_27_checked⟩
  · exact ⟨analyticWitness_28,analyticRow_28_checked⟩
  · exact ⟨analyticWitness_29,analyticRow_29_checked⟩
  · exact ⟨analyticWitness_30,analyticRow_30_checked⟩
  · exact ⟨analyticWitness_31,analyticRow_31_checked⟩
  · exact ⟨analyticWitness_32,analyticRow_32_checked⟩
  · exact ⟨analyticWitness_33,analyticRow_33_checked⟩

theorem frozen_kernelN_upper (r : PrimeRow) (hr : r∈rows) :
    kernelN (r.lambdaUpper:ℝ)≤(r.normUpper:ℝ) := by
  obtain ⟨w,hw⟩ := frozen_analytic_rows_checked r hr
  obtain ⟨_,_,hl0,hl1,_⟩ := frozen_root_rows_checked r hr
  exact w.kernel_bound r hl0 hl1 hw

theorem frozen_log_norm_upper (r : PrimeRow) (hr : r∈rows) :
    Real.log (r.normUpper:ℝ)/(r.tau:ℝ)≤(r.edgeUpper:ℝ) := by
  obtain ⟨w,hw⟩ := frozen_analytic_rows_checked r hr
  exact w.edge_bound r hw

theorem frozen_tau_positive (r : PrimeRow) (hr : r∈rows) : (0:ℝ)<r.tau := by
  obtain ⟨w,hw⟩ := frozen_analytic_rows_checked r hr
  rcases hw with ⟨_,_,_,_,_,_,_,ht,_⟩
  exact_mod_cast ht

def smallPrimes : Finset ℕ := (Finset.range 143).filter Nat.Prime
theorem rows_primes_finset : (rows.map PrimeRow.prime).toFinset=smallPrimes := by decide +kernel
theorem rows_primes_nodup : (rows.map PrimeRow.prime).Nodup := by decide +kernel
theorem frozen_edge_sum : (rows.map PrimeRow.edgeUpper).sum<edgebar := by decide +kernel

theorem smallPrimes_mem {p : ℕ} : p∈smallPrimes ↔ Nat.Prime p ∧ p≤142 := by
  simp only [smallPrimes,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨h,hp⟩; exact ⟨hp,by omega⟩
  · rintro ⟨hp,h⟩; exact ⟨by omega,hp⟩

end LonelyRunnerNew.Certificate
