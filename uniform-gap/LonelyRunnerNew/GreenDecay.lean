import LonelyRunnerNew.GreenPotential

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LonelyRunnerNew.GreenPotential

theorem kernel_shift_bound {a : ℝ} (ha : 0≤a) (x y R : ℝ) (hy : |y|≤R) :
    kernel a (x-y) ≤ Real.exp (a*R)*kernel a x := by
  have ht : |x| ≤ |x-y|+R := by
    have h := abs_add_le (x-y) y
    rw [sub_add_cancel] at h
    linarith
  unfold kernel
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem cell_kernel_bound {a : ℝ} (ha : 0≤a) (i : ℤ) (x : ℝ) :
    (∫ y in KernelSteps.cell i,Real.exp (-a*|x-y|)) ≤
      Real.exp (a*(|(i:ℝ)|+1))*kernel a x := by
  let B := Real.exp (a*(|(i:ℝ)|+1))*kernel a x
  have hconst : (∫ y in KernelSteps.cell i,B)=B := by
    calc
      _ = ∫ y in KernelSteps.cell i,B*1 := by simp
      _ = B*(∫ y in KernelSteps.cell i,(1:ℝ)) := integral_const_mul _ _
      _ = B := by rw [KernelSteps.cell_one_integral,mul_one]
  change _ ≤ B
  rw [← hconst]
  apply integral_mono_ae
    (KernelSteps.continuous_integrable_cell _ (by fun_prop) i)
    (KernelSteps.continuous_integrable_cell _ continuous_const i)
  filter_upwards [ae_restrict_mem (show MeasurableSet (KernelSteps.cell i) from measurableSet_Ico)] with y hy
  apply kernel_shift_bound ha x y (|(i:ℝ)|+1)
  apply abs_le.mpr
  have hl := neg_abs_le (i:ℝ)
  have hu := le_abs_self (i:ℝ)
  exact ⟨by linarith [hy.1],by linarith [hy.2]⟩

def S (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) : ℝ := ∑ i ∈ F,f i*Real.exp (a*(|(i:ℝ)|+1))

theorem S_nonneg (a : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) : 0≤S a F f :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hf i hi) (Real.exp_pos _).le)

theorem U_bound {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) (x : ℝ) :
    |U a F f x| ≤ (S a F f/(2*a))*kernel a x := by
  rw [abs_of_nonneg (U_nonneg ha F f hf x),U_eq_green,KernelSteps.potential_eq_sum]
  apply (div_le_iff₀ (by positivity : 0<2*a)).mpr
  calc
    _ ≤ ∑ i ∈ F,f i*(Real.exp (a*(|(i:ℝ)|+1))*kernel a x) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (cell_kernel_bound ha.le i x) (hf i hi))
    _ = _ := by
      have he : S a F f/(2*a)*kernel a x*(2*a)=S a F f*kernel a x := by field_simp
      rw [he]
      unfold S
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem V_bound {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) (x : ℝ) :
    |V a F f x| ≤ (S a F f/a)*kernel a x := by
  unfold V
  calc
    _ ≤ ∑ i ∈ F,|f i*((kernel a (x-i)-kernel a (x-((i:ℝ)+1)))/(2*a))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ F,f i*((2*Real.exp (a*(|(i:ℝ)|+1))*kernel a x)/(2*a)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (hf i hi),abs_div,abs_of_pos (by positivity : 0<2*a)]
      apply mul_le_mul_of_nonneg_left _ (hf i hi)
      apply (div_le_div_iff_of_pos_right (by positivity : 0<2*a)).mpr
      have hk0 (y : ℝ) : 0≤kernel a y := (Real.exp_pos _).le
      have h1 := kernel_shift_bound ha.le x (i:ℝ) (|(i:ℝ)|+1) (by linarith)
      have h2 := kernel_shift_bound ha.le x ((i:ℝ)+1) (|(i:ℝ)|+1) (by simpa using abs_add_le (i:ℝ) 1)
      have hh : |kernel a (x-i)-kernel a (x-((i:ℝ)+1))| ≤ kernel a (x-i)+kernel a (x-((i:ℝ)+1)) :=
        abs_le.mpr ⟨by linarith [hk0 (x-i)],by linarith [hk0 (x-((i:ℝ)+1))]⟩
      nlinarith only [h1,h2,hh]
    _ = _ := by
      unfold S
      rw [div_mul_eq_mul_div,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp

theorem kernel_integrable {a : ℝ} (ha : 0<a) : Integrable (kernel a) := by
  have hl : IntegrableOn (kernel a) (Set.Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    have hx0 : x≤0 := hx
    simp only [kernel,abs_of_nonpos hx0]
    congr 1
    ring
  have hr : IntegrableOn (kernel a) (Set.Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := hx
    simp only [kernel,abs_of_pos hx0]
  simpa only [Set.Iic_union_Ioi,integrableOn_univ] using hl.union hr

theorem kernel_top {a : ℝ} (ha : 0<a) : Tendsto (kernel a) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simp [kernel,abs_of_nonneg hx]

theorem kernel_bot {a : ℝ} (ha : 0<a) : Tendsto (kernel a) atBot (𝓝 0) := by
  change Tendsto (fun x : ℝ => Real.exp (-a*|x|)) atBot (𝓝 0)
  simpa only [Function.comp_def,kernel,abs_neg] using (kernel_top ha).comp tendsto_neg_atBot_atTop

theorem dominated_square_integrable {a : ℝ} (ha : 0<a) (W : ℝ → ℝ) (hc : Continuous W)
    (C : ℝ) (hC : 0≤C) (hb : ∀ x,|W x|≤C*kernel a x) : Integrable (fun x => (W x)^2) := by
  apply Integrable.mono' ((kernel_integrable (by positivity : 0<2*a)).const_mul (C^2)) (hc.pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  change |(W x)^2| ≤ C^2*kernel (2*a) x
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh := pow_le_pow_left₀ (abs_nonneg (W x)) (hb x) 2
  rw [sq_abs,mul_pow] at hh
  have he : (kernel a x)^2=kernel (2*a) x := by unfold kernel; rw [← Real.exp_nat_mul]; congr 1; ring
  simpa only [he] using hh

theorem U_square_integrable {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) :
    Integrable (fun x => (U a F f x)^2) :=
  dominated_square_integrable ha _ (U_continuous a F f) _ (div_nonneg (S_nonneg a F f hf) (by positivity)) (U_bound ha F f hf)

theorem V_square_integrable {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) :
    Integrable (fun x => (V a F f x)^2) :=
  dominated_square_integrable ha _ (V_continuous a F f) _ (div_nonneg (S_nonneg a F f hf) ha.le) (V_bound ha F f hf)

theorem U_limits {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) :
    Tendsto (U a F f) atBot (𝓝 0) ∧ Tendsto (U a F f) atTop (𝓝 0) := by
  have hb (x : ℝ) : U a F f x ≤ S a F f/(2*a)*kernel a x := by simpa only [abs_of_nonneg (U_nonneg ha F f hf x)] using U_bound ha F f hf x
  constructor
  · exact squeeze_zero (U_nonneg ha F f hf) hb (by simpa using (kernel_bot ha).const_mul (S a F f/(2*a)))
  · exact squeeze_zero (U_nonneg ha F f hf) hb (by simpa using (kernel_top ha).const_mul (S a F f/(2*a)))

theorem positive_maximum {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hne : ∃ i ∈ F,0<f i) :
    ∃ c : ℝ,0<U a F f c ∧ ∀ x,U a F f x≤U a F f c := by
  have hpos := U_pos ha F f hf hne 0
  have hlim : Tendsto (U a F f) (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop]
    exact (U_limits ha F f hf).1.sup (U_limits ha F f hf).2
  have hev : ∀ᶠ x in cocompact ℝ,U a F f x≤U a F f 0 :=
    ((tendsto_order.mp hlim).2 _ hpos).mono (fun _ hx => hx.le)
  obtain ⟨c,hc⟩ := (U_continuous a F f).exists_forall_ge' 0 hev
  exact ⟨c,hpos.trans_le (hc 0),hc⟩

theorem V_limits {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ i ∈ F,0≤f i) :
    Tendsto (V a F f) atBot (𝓝 0) ∧ Tendsto (V a F f) atTop (𝓝 0) := by
  constructor
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun _ => abs_nonneg _) (V_bound ha F f hf)
      (by simpa using (kernel_bot ha).const_mul (S a F f/a))
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun _ => abs_nonneg _) (V_bound ha F f hf)
      (by simpa using (kernel_top ha).const_mul (S a F f/a))

theorem actual_energy_sharp {a : ℝ} (ha : 0<a) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ i ∈ F,0≤f i) (hne : ∃ i ∈ F,0<f i) :
    (4*a^(3/2:ℝ)/Real.sqrt 3)*Real.sqrt (∫ x,(U a F f x)^4) ≤
      ∫ x,(V a F f x)^2+a^2*(U a F f x)^2 := by
  obtain ⟨c,hM,hmax⟩ := positive_maximum ha F f hf hne
  exact GreenEnergy.energy_sharp _ _ a (U a F f c) c ha hM (U_deriv a F f) (V_continuous a F f)
    (U_nonneg ha F f hf) hmax rfl (U_limits ha F f hf).1 (U_limits ha F f hf).2
    (U_square_integrable ha F f hf) (V_square_integrable ha F f hf)

end LonelyRunnerNew.GreenPotential
