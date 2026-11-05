import LonelyRunnerNew.BootstrapEndpoint
import LonelyRunnerNew.KernelCells
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.FixedScale

def a0 : ℝ := 311/250
def lambda0 : ℝ := Real.exp (-a0)
def C0 : ℝ := (Real.sqrt 3/2)*lambda0*a0^(3/2:ℝ)/(1-lambda0)^2
def d0 : ℝ := 1-2*lambda0*(a0-1+lambda0)/(1-lambda0)^2
def lamLo : ℝ := 28822899/100000000
def lamHi : ℝ := 288229/1000000
def expLower : ℝ := ∑ k ∈ Finset.range 16,(a0/2)^k/(Nat.factorial k:ℝ)
def expUpper : ℝ := expLower+(a0/2)^16*17/((Nat.factorial 16:ℝ)*16)

theorem a0_pos : 0 < a0 := by norm_num [a0]
theorem lambda0_pos : 0 < lambda0 := Real.exp_pos _
theorem lambda0_lt_one : lambda0 < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos a0_pos)

theorem log149_lower : (62511/12500:ℝ) < Real.log 149 := by
  have h2 := (RationalAnalysis.log_series_enclosure (by norm_num : (1:ℝ)≤2) 5).1
  have hr := (RationalAnalysis.log_series_enclosure (by norm_num : (1:ℝ)≤149/128) 2).1
  have hn : (62511/12500:ℝ) < 7*RationalAnalysis.logSeriesLower 2 5+
      RationalAnalysis.logSeriesLower (149/128) 2 := by
    norm_num [RationalAnalysis.logSeriesLower,Finset.sum_range_succ]
  have he : Real.log 149=7*Real.log 2+Real.log (149/128:ℝ) := by
    convert RationalAnalysis.log_two_pow_mul (y := (149/128:ℝ)) (by norm_num) 7 using 1 <;> norm_num
  linarith

theorem exp_62511_lt_149 : Real.exp (62511/12500:ℝ) < 149 := by
  rw [← Real.exp_log (by norm_num : (0:ℝ)<149)]
  exact Real.exp_lt_exp.mpr log149_lower

theorem prime_lambda_le {p : ℕ} (hp : Nat.Prime p) (hp142 : 142 < p) :
    (p:ℝ)^(-1/q) ≤ lambda0 := by
  have hp149 : (149:ℝ) ≤ p := by exact_mod_cast BootstrapEndpoint.prime_ge_149 hp hp142
  have hlog : q*a0 < Real.log (p:ℝ) := by
    have hmono := Real.log_le_log (by norm_num : (0:ℝ)<149) hp149
    have he : q*a0=(62511/12500:ℝ) := by norm_num [q,a0]
    linarith [log149_lower]
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos)]
  apply Real.exp_le_exp.mpr
  change Real.log (p:ℝ)*(-1/q) ≤ -a0
  have hq : 0 < q := by norm_num [q]
  apply (mul_le_mul_iff_left₀ hq).mp
  have he : (Real.log (p:ℝ)*(-1/q))*q = -Real.log (p:ℝ) := by field_simp
  rw [he]
  linarith

theorem exp_half_enclosure : expLower ≤ Real.exp (a0/2) ∧ Real.exp (a0/2) ≤ expUpper := by
  constructor
  · exact Real.sum_le_exp_of_nonneg (by norm_num [a0]) 16
  · simpa only [expUpper,expLower,Nat.cast_ofNat,show (16:ℝ)+1=17 by norm_num] using Real.exp_bound' (by norm_num [a0] : 0≤a0/2)
      (by norm_num [a0] : a0/2≤1) (by decide : 0<16)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem lambda_certificates : 0<expLower ∧ lamLo*expUpper^2<1 ∧ 1<lamHi*expLower^2 := by
  norm_num [expLower,expUpper,a0,lamLo,lamHi,Finset.sum_range_succ,Nat.factorial]

theorem lambda_enclosure : lamLo < lambda0 ∧ lambda0 < lamHi := by
  have hc := lambda_certificates
  have he : Real.exp a0=(Real.exp (a0/2))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hlo : expLower^2 ≤ Real.exp a0 := by
    rw [he]
    exact pow_le_pow_left₀ hc.1.le exp_half_enclosure.1 2
  have hup : Real.exp a0 ≤ expUpper^2 := by
    rw [he]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_half_enclosure.2 2
  unfold lambda0
  rw [Real.exp_neg,← one_div]
  constructor
  · apply (lt_div_iff₀ (Real.exp_pos a0)).mpr
    exact (mul_le_mul_of_nonneg_left hup (by norm_num [lamLo])).trans_lt hc.2.1
  · apply (div_lt_iff₀ (Real.exp_pos a0)).mpr
    exact hc.2.2.trans_le (mul_le_mul_of_nonneg_left hlo (by norm_num [lamHi]))

theorem sqrt_enclosures : Real.sqrt 3 ≤ (1732051/1000000:ℝ) ∧
    Real.sqrt a0 ≤ (1115348/1000000:ℝ) := by
  constructor <;> apply Real.sqrt_le_iff.mpr <;> norm_num [a0]

theorem coefficient_certificates :
    ((1732051/1000000:ℝ)/2)*lamHi*a0*(1115348/1000000)/(1-lamHi)^2 < 13673/20000 ∧
    1-2*lamLo*(a0-1+lamLo)/(1-lamLo)^2 < (19721/50000:ℝ) ∧
    (13673/20000:ℝ)+(401/500)*(19721/50000)=1-629/25000000 := by
  norm_num [lamLo,lamHi,a0]

theorem C0_upper : C0 < (13673/20000:ℝ) := by
  have hl := lambda_enclosure
  have ha0 := a0_pos
  have hl0 := lambda0_pos
  have hs3 := sqrt_enclosures.1
  have hsa := sqrt_enclosures.2
  have hnum : (Real.sqrt 3/2)*lambda0*a0*Real.sqrt a0 ≤
      ((1732051/1000000:ℝ)/2)*lamHi*a0*(1115348/1000000) := by
    gcongr <;> first | exact hs3 | exact hsa | exact hl.2.le | positivity | norm_num [a0,lamHi]
  have hden : (1-lamHi)^2 ≤ (1-lambda0)^2 :=
    pow_le_pow_left₀ (by norm_num [lamHi]) (by linarith [hl.2]) 2
  have ha : a0^(3/2:ℝ)=a0*Real.sqrt a0 := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_one_add' a0_pos.le (by norm_num),← Real.sqrt_eq_rpow]
  unfold C0
  rw [ha,← mul_assoc]
  exact (div_le_div₀ (by norm_num [lamHi,a0]) hnum (by norm_num [lamHi]) hden).trans_lt coefficient_certificates.1

theorem d0_bounds : 0 < d0 ∧ d0 < (19721/50000:ℝ) := by
  constructor
  · simpa only [d0,lambda0,KernelCells.correction_coefficient a0 a0_pos] using KernelCells.correction_positive a0 a0_pos
  · have hl := lambda_enclosure
    have hLp := lambda0_pos
    have hA : 0 ≤ a0-1 := by norm_num [a0]
    have hl0 : 0 ≤ lamLo := by norm_num [lamLo]
    have hbase : 0 ≤ a0-1+lamLo := by norm_num [a0,lamLo]
    have hnum : 2*lamLo*(a0-1+lamLo) ≤ 2*lambda0*(a0-1+lambda0) := by gcongr <;> linarith [hl.1]
    have hden : (1-lambda0)^2 ≤ (1-lamLo)^2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr lambda0_lt_one.le) (by linarith [hl.1]) 2
    have hh := div_le_div₀ (by positivity : 0 ≤ 2*lambda0*(a0-1+lambda0)) hnum
      (sq_pos_of_pos (sub_pos.mpr lambda0_lt_one)) hden
    have hn := coefficient_certificates.2.1
    unfold d0
    linarith

theorem diagonal_lower {D : ℝ} (h : 1 ≤ C0+d0*D) : (401/500:ℝ) ≤ D := by
  have hd := d0_bounds
  by_contra hn
  have hD : D < (401/500:ℝ) := lt_of_not_ge hn
  have hm := mul_lt_mul_of_pos_left hD hd.1
  have hu := mul_lt_mul_of_pos_left hd.2 (by norm_num : (0:ℝ)<401/500)
  have hc := C0_upper
  nlinarith [coefficient_certificates.2.2]

theorem seed_arithmetic : 1-(401/500:ℝ)^2=(89199/250000:ℝ) ∧
    (89199/250000:ℝ)<357/1000 := by norm_num

end LonelyRunnerNew.FixedScale
