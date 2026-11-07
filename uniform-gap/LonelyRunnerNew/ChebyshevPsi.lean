import LonelyRunnerNew.ChebyshevConstants

noncomputable section
set_option autoImplicit false
namespace LonelyRunnerNew.RCThirty

def psiError (x : ℝ) : ℝ := 200*(1+Real.log (x+1))^2

theorem log_five_ge_one : (1:ℝ)≤Real.log 5 := by
  have h := Certificate.rational_log_enclosure 5 (by norm_num) 2
  have hc : (1:ℚ)≤Certificate.logLowerQ 5 2 := by
    norm_num [Certificate.logLowerQ,Finset.sum_range_succ]
  have hcR : (1:ℝ)≤(Certificate.logLowerQ 5 2:ℝ) := by exact_mod_cast hc
  exact hcR.trans (by simpa using h.1)

theorem psi_error_step {n : ℕ} (hn : 30≤n) :
    5+10*Real.log (n:ℝ)+psiError ((n/6:ℕ):ℝ)≤psiError (n:ℝ) := by
  have hnR : (30:ℝ)≤n := by exact_mod_cast hn
  have hk : (6:ℝ)*(n/6:ℕ)≤n := by
    have hh : (((n/6)*6:ℕ):ℝ)≤n := by exact_mod_cast Nat.div_mul_le_self n 6
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh
  have hpos : (0:ℝ)<(n/6:ℕ)+1 := by positivity
  have hlt : ((n/6:ℕ):ℝ)+1≤((n:ℝ)+1)/5 := by nlinarith
  have hl := Real.log_le_log hpos hlt
  rw [Real.log_div (by positivity : (n:ℝ)+1≠0) (by norm_num : (5:ℝ)≠0)] at hl
  have hlogn : Real.log (n:ℝ)≤Real.log ((n:ℝ)+1) := Real.log_le_log (by linarith) (by linarith)
  have hlogk : 0≤Real.log (((n/6:ℕ):ℝ)+1) := Real.log_nonneg (by have hh := Nat.cast_nonneg (n/6) (α:=ℝ);linarith)
  have hlog5 := log_five_ge_one
  unfold psiError
  have hs : (1+Real.log (((n/6:ℕ):ℝ)+1))^2≤(Real.log ((n:ℝ)+1))^2 := by
    apply sq_le_sq₀ (by linarith) (by linarith) |>.mpr
    linarith
  nlinarith

theorem psi_upper_nat (n : ℕ) :
    Chebyshev.psi (n:ℝ)≤(6/5:ℝ)*constantC*n+psiError (n:ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc := constantC_enclosure
    have hc0 : 0≤constantC := by linarith
    have hnR : (0:ℝ)≤n := Nat.cast_nonneg _
    by_cases hn : n<30
    · have hp := Chebyshev.psi_le_const_mul_self hnR
      have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      have hl4 : Real.log (4:ℝ)≤2 := by
        rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
        norm_num at *
        linarith
      have hm := mul_le_mul_of_nonneg_right hl4 hnR
      have hlog : 0≤Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith)
      have hn30 : (n:ℝ)<30 := by exact_mod_cast hn
      have he : 200≤psiError (n:ℝ) := by unfold psiError;nlinarith
      have hnon : 0≤(6/5:ℝ)*constantC*n := by positivity
      nlinarith
    · have hn30 : 30≤n := by omega
      have hklt : n/6<n := Nat.div_lt_self (by omega) (by norm_num)
      have hrec := psi_le_J_add (n:ℝ)
      have hp : Chebyshev.psi ((n:ℝ)/6)=Chebyshev.psi ((n/6:ℕ):ℝ) := by
        rw [Chebyshev.psi_eq_psi_coe_floor,Nat.floor_div_ofNat,Nat.floor_natCast]
      rw [hp] at hrec
      have hj := (abs_le.mp (J_main_error (x:=(n:ℝ)) (by exact_mod_cast hn30))).2
      have hchild := ih (n/6) hklt
      have hk : (6:ℝ)*(n/6:ℕ)≤n := by
        have hh : (((n/6)*6:ℕ):ℝ)≤n := by exact_mod_cast Nat.div_mul_le_self n 6
        simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh
      have hm := mul_le_mul_of_nonneg_left hk hc0
      have he := psi_error_step hn30
      nlinarith

theorem psi_upper {x : ℝ} (hx : 0≤x) :
    Chebyshev.psi x≤(6/5:ℝ)*constantC*x+psiError x := by
  have hn := Nat.floor_le hx
  have hp := psi_upper_nat ⌊x⌋₊
  have hc : 0≤constantC := by have := constantC_enclosure;linarith
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num : (0:ℝ)≤6/5) hc)
  have hl : Real.log ((⌊x⌋₊:ℝ)+1)≤Real.log (x+1) := Real.log_le_log (by positivity) (by linarith)
  have hlo : 0≤Real.log ((⌊x⌋₊:ℝ)+1) := Real.log_nonneg (by have hh := Nat.cast_nonneg ⌊x⌋₊ (α:=ℝ);linarith)
  have he : psiError (⌊x⌋₊:ℝ)≤psiError x := by
    unfold psiError
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤200)
    exact (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)
  rw [Chebyshev.psi_eq_psi_coe_floor]
  linarith

end LonelyRunnerNew.RCThirty
