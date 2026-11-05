import LonelyRunnerNew.LCNumericChecker

namespace LonelyRunnerNew.LCNumeric

def SixthCross (n h e d : ℚ) : Prop :=
  n.num^6*h.num*(e.den:ℤ)*(d.den:ℤ)^6 ≤ e.num*d.num^6*(h.den:ℤ)*(n.den:ℤ)^6
instance (n h e d : ℚ) : Decidable (SixthCross n h e d) := by unfold SixthCross; infer_instance

theorem sixth_cross_sound (n h e d : ℚ) (hc : SixthCross n h e d) : n^6*h ≤ e*d^6 := by
  have hB : (0:ℚ) < (n.den:ℚ)^6*(h.den:ℚ) := by positivity
  have hD : (0:ℚ) < (e.den:ℚ)*(d.den:ℚ)^6 := by positivity
  have hn : n^6*h=((n.num:ℚ)^6*(h.num:ℚ))/((n.den:ℚ)^6*(h.den:ℚ)) := by
    conv_lhs => rw [← n.num_div_den,← h.num_div_den]
    ring
  have he : e*d^6=((e.num:ℚ)*(d.num:ℚ)^6)/((e.den:ℚ)*(d.den:ℚ)^6) := by
    conv_lhs => rw [← e.num_div_den,← d.num_div_den]
    ring
  rw [hn,he]
  apply (div_le_div_iff₀ hB hD).mpr
  have hi : (n.num:ℚ)^6*(h.num:ℚ)*(e.den:ℚ)*(d.den:ℚ)^6 ≤
      (e.num:ℚ)*(d.num:ℚ)^6*(h.den:ℚ)*(n.den:ℚ)^6 := by exact_mod_cast hc
  nlinarith only [hi]

/-- Identical mathematics to Accepts, with sixth powers compared as integers
after clearing the four positive rational denominators. -/
def CellStep.FastAccepts (d : CellStep) (b : Box) : Prop :=
  0 < d.lowerDen b ∧ d.pre*(b.f1+b.f2) ≤ d.bUpper*d.lowerDen b ∧
    SixthCross (d.pre*(b.f1+b.f2)) (b.h1+b.h2) d.eUpper (d.lowerDen b)
instance (d : CellStep) (b : Box) : Decidable (d.FastAccepts b) := by
  unfold CellStep.FastAccepts; infer_instance

theorem CellStep.fast_sound (d : CellStep) (b : Box) (hh : d.FastAccepts b) : d.Accepts b :=
  ⟨hh.1,hh.2.1,sixth_cross_sound _ _ _ _ hh.2.2⟩

end LonelyRunnerNew.LCNumeric
