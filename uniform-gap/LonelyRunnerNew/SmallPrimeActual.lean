import LonelyRunnerNew.SmallPrimeRowsProved
import LonelyRunnerNew.SmallPrimeMoments

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

theorem stable_row_exponential_moment (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (r : Certificate.PrimeRow) (hr : r∈Certificate.rows) :
    s.primeExpMoment r.prime (r.tau:ℝ)≤(r.normUpper:ℝ) := by
  obtain ⟨hp,_,hl0,hl1,_⟩ := Certificate.frozen_root_rows_checked r hr
  exact (s.exp_moment_of_layers r.prime hp (s.stable_layer_concentration hs hM r.prime hp)
    (by exact_mod_cast hl0) (by exact_mod_cast hl1)
    (Certificate.frozen_moment_lambda_bound r hr)).trans (Certificate.frozen_kernelN_upper r hr)

theorem universal_row_exponential_moment (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (r : Certificate.PrimeRow) (hr : r∈Certificate.rows) :
    s.primeExpMoment r.prime (r.tau:ℝ)≤(r.normUpper:ℝ) := by
  obtain ⟨hp,_,hl0,hl1,_⟩ := Certificate.frozen_root_rows_checked r hr
  exact (s.exp_moment_of_layers r.prime hp (s.universal_layer_target_kernel hs hM r.prime hp)
    (by exact_mod_cast hl0) (by exact_mod_cast hl1)
    (Certificate.frozen_moment_lambda_bound r hr)).trans (Certificate.frozen_kernelN_upper r hr)

theorem stable_row_mean_log_distance (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass)
    (r : Certificate.PrimeRow) (hr : r∈Certificate.rows) :
    s.primeMeanLogDistance r.prime≤(r.edgeUpper:ℝ) :=
  (s.mean_log_distance_of_moment hM r.prime (Certificate.frozen_tau_positive r hr)
    (s.stable_row_exponential_moment hs hM r hr)).trans (Certificate.frozen_log_norm_upper r hr)

theorem universal_row_mean_log_distance (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass)
    (r : Certificate.PrimeRow) (hr : r∈Certificate.rows) :
    s.primeMeanLogDistance r.prime≤(r.edgeUpper:ℝ) :=
  (s.mean_log_distance_of_moment hM r.prime (Certificate.frozen_tau_positive r hr)
    (s.universal_row_exponential_moment hs hM r hr)).trans (Certificate.frozen_log_norm_upper r hr)

theorem small_prime_sum_of_row_bounds (s : TaggedState Label n)
    (hrow : ∀ r∈Certificate.rows,s.primeMeanLogDistance r.prime≤(r.edgeUpper:ℝ)) :
    (∑ p∈Certificate.smallPrimes,s.primeMeanLogDistance p)<(Certificate.edgebar:ℝ) := by
  have hsum : (Certificate.rows.map (fun r => s.primeMeanLogDistance r.prime)).sum≤
      (Certificate.rows.map (fun r => (r.edgeUpper:ℝ))).sum := List.sum_le_sum hrow
  have hq : (((Certificate.rows.map Certificate.PrimeRow.edgeUpper).sum:ℚ):ℝ)<(Certificate.edgebar:ℝ) := by
    exact_mod_cast Certificate.frozen_edge_sum
  push_cast at hq
  have he : (∑ p∈Certificate.smallPrimes,s.primeMeanLogDistance p)=
      (Certificate.rows.map (fun r => s.primeMeanLogDistance r.prime)).sum := by
    rw [← Certificate.rows_primes_finset,List.sum_toFinset _ Certificate.rows_primes_nodup,List.map_map]
    rfl
  rw [he]
  exact hsum.trans_lt (by simpa only [List.map_map,Function.comp_def] using hq)

/-- All primes <=142 are covered by the frozen table. The distance includes
log p; only actual ordinary stability and positive mass remain as inputs. -/
theorem stable_small_prime_mean_distance (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.quality≤s.quality) (hM : 0<s.edgeMass) :
    (∑ p∈Certificate.smallPrimes,s.primeMeanLogDistance p)<(Certificate.edgebar:ℝ) :=
  s.small_prime_sum_of_row_bounds (s.stable_row_mean_log_distance hs hM)

theorem universal_small_prime_mean_distance (s : TaggedState Label n)
    (hs : ∀ t,Step s t → t.universalQuality≤s.universalQuality) (hM : 0<s.edgeMass) :
    (∑ p∈Certificate.smallPrimes,s.primeMeanLogDistance p)<(Certificate.edgebar:ℝ) :=
  s.small_prime_sum_of_row_bounds (s.universal_row_mean_log_distance hs hM)

end LonelyRunnerNew.TaggedState
