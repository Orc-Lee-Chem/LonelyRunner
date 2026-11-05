import LonelyRunnerNew.LCNumericIntegerCheck

namespace LonelyRunnerNew.LCNumeric

/-- Unreduced fractions are used only to evaluate polynomial certificates.
Every denominator is proved positive before interpreting comparisons. -/
structure Raw where
  num : ℤ
  den : ℕ
  deriving Inhabited
def Raw.val (a : Raw) : ℚ := (a.num:ℚ)/a.den
def Raw.ofRat (a : ℚ) : Raw := ⟨a.num,a.den⟩
def Raw.add (a b : Raw) : Raw := ⟨a.num*b.den+b.num*a.den,a.den*b.den⟩
def Raw.sub (a b : Raw) : Raw := ⟨a.num*b.den-b.num*a.den,a.den*b.den⟩
def Raw.mul (a b : Raw) : Raw := ⟨a.num*b.num,a.den*b.den⟩
def Raw.Le (a b : Raw) : Prop := a.num*(b.den:ℤ) ≤ b.num*(a.den:ℤ)
instance (a b : Raw) : Decidable (a.Le b) := by unfold Raw.Le; infer_instance

theorem Raw.ofRat_val (a : ℚ) : (Raw.ofRat a).val=a := a.num_div_den
theorem Raw.ofRat_pos (a : ℚ) : 0 < (Raw.ofRat a).den := a.den_pos
theorem Raw.add_pos (a b : Raw) (ha : 0<a.den) (hb : 0<b.den) : 0<(a.add b).den := Nat.mul_pos ha hb
theorem Raw.sub_pos (a b : Raw) (ha : 0<a.den) (hb : 0<b.den) : 0<(a.sub b).den := Nat.mul_pos ha hb
theorem Raw.mul_pos (a b : Raw) (ha : 0<a.den) (hb : 0<b.den) : 0<(a.mul b).den := Nat.mul_pos ha hb
theorem Raw.add_val (a b : Raw) (ha : 0<a.den) (hb : 0<b.den) : (a.add b).val=a.val+b.val := by
  have haQ : (a.den:ℚ)≠0 := by exact_mod_cast ha.ne'
  have hbQ : (b.den:ℚ)≠0 := by exact_mod_cast hb.ne'
  unfold Raw.val Raw.add
  push_cast
  field_simp <;> ring
theorem Raw.sub_val (a b : Raw) (ha : 0<a.den) (hb : 0<b.den) : (a.sub b).val=a.val-b.val := by
  have haQ : (a.den:ℚ)≠0 := by exact_mod_cast ha.ne'
  have hbQ : (b.den:ℚ)≠0 := by exact_mod_cast hb.ne'
  unfold Raw.val Raw.sub
  push_cast
  field_simp <;> ring
theorem Raw.mul_val (a b : Raw) : (a.mul b).val=a.val*b.val := by
  unfold Raw.val Raw.mul
  push_cast
  ring
theorem Raw.le_sound (a b : Raw) (ha : 0<a.den) (hb : 0<b.den) (h : a.Le b) : a.val ≤ b.val := by
  unfold Raw.val
  apply (div_le_div_iff₀ (by exact_mod_cast ha : (0:ℚ)<a.den) (by exact_mod_cast hb : (0:ℚ)<b.den)).mpr
  exact_mod_cast h

def CellStep.rawDen (d : CellStep) (b : Box) : Raw :=
  (Raw.ofRat d.aLower).sub (((Raw.ofRat b.h1).add (Raw.ofRat b.h2)).add
    ((Raw.ofRat d.cross).mul (Raw.ofRat b.jj)) |>.mul (Raw.ofRat d.sqrtUpper))
def CellStep.rawNum (d : CellStep) (b : Box) : Raw :=
  (Raw.ofRat d.pre).mul ((Raw.ofRat b.f1).add (Raw.ofRat b.f2))
def CellStep.rawH (b : Box) : Raw := (Raw.ofRat b.h1).add (Raw.ofRat b.h2)

theorem CellStep.rawDen_pos (d : CellStep) (b : Box) : 0<(d.rawDen b).den := by
  simp only [rawDen,Raw.sub,Raw.add,Raw.mul,Raw.ofRat]
  positivity
theorem CellStep.rawNum_pos (d : CellStep) (b : Box) : 0<(d.rawNum b).den := by
  simp only [rawNum,Raw.mul,Raw.add,Raw.ofRat]
  positivity
theorem CellStep.rawH_pos (b : Box) : 0<(CellStep.rawH b).den := by
  exact Raw.add_pos _ _ b.h1.den_pos b.h2.den_pos

theorem CellStep.rawDen_val (d : CellStep) (b : Box) : (d.rawDen b).val=d.lowerDen b := by
  rw [rawDen,Raw.sub_val _ _ (Raw.ofRat_pos _) (Raw.mul_pos _ _
    (Raw.add_pos _ _ (Raw.add_pos _ _ (Raw.ofRat_pos _) (Raw.ofRat_pos _))
      (Raw.mul_pos _ _ (Raw.ofRat_pos _) (Raw.ofRat_pos _))) (Raw.ofRat_pos _)),
    Raw.mul_val,Raw.add_val _ _ (Raw.add_pos _ _ (Raw.ofRat_pos _) (Raw.ofRat_pos _))
      (Raw.mul_pos _ _ (Raw.ofRat_pos _) (Raw.ofRat_pos _)),
    Raw.add_val _ _ (Raw.ofRat_pos _) (Raw.ofRat_pos _),Raw.mul_val]
  simp only [Raw.ofRat_val,CellStep.lowerDen]
theorem CellStep.rawNum_val (d : CellStep) (b : Box) : (d.rawNum b).val=d.pre*(b.f1+b.f2) := by
  rw [rawNum,Raw.mul_val,Raw.add_val _ _ (Raw.ofRat_pos _) (Raw.ofRat_pos _)]
  simp only [Raw.ofRat_val]
theorem CellStep.rawH_val (b : Box) : (CellStep.rawH b).val=b.h1+b.h2 := by
  rw [rawH,Raw.add_val _ _ (Raw.ofRat_pos _) (Raw.ofRat_pos _)]
  simp only [Raw.ofRat_val]

def Raw.Sixth (n h e d : Raw) : Prop :=
  n.num^6*h.num*(e.den:ℤ)*(d.den:ℤ)^6 ≤ e.num*d.num^6*(h.den:ℤ)*(n.den:ℤ)^6
instance (n h e d : Raw) : Decidable (Raw.Sixth n h e d) := by unfold Raw.Sixth; infer_instance
theorem Raw.sixth_sound (n h e d : Raw) (hn : 0<n.den) (hh : 0<h.den)
    (he : 0<e.den) (hd : 0<d.den) (hc : Raw.Sixth n h e d) : n.val^6*h.val ≤ e.val*d.val^6 := by
  unfold Raw.val
  rw [div_pow,div_pow,div_mul_div_comm,div_mul_div_comm]
  apply (div_le_div_iff₀ (by positivity : (0:ℚ)<(n.den:ℚ)^6*(h.den:ℚ))
    (by positivity : (0:ℚ)<(e.den:ℚ)*(d.den:ℚ)^6)).mpr
  have hi : (n.num:ℚ)^6*(h.num:ℚ)*(e.den:ℚ)*(d.den:ℚ)^6 ≤
      (e.num:ℚ)*(d.num:ℚ)^6*(h.den:ℚ)*(n.den:ℚ)^6 := by exact_mod_cast hc
  nlinarith only [hi]

def CellStep.IntegerAccepts (d : CellStep) (b : Box) : Prop :=
  0<(d.rawDen b).num ∧ (d.rawNum b).Le ((Raw.ofRat d.bUpper).mul (d.rawDen b)) ∧
    Raw.Sixth (d.rawNum b) (CellStep.rawH b) (Raw.ofRat d.eUpper) (d.rawDen b)
instance (d : CellStep) (b : Box) : Decidable (d.IntegerAccepts b) := by
  unfold CellStep.IntegerAccepts; infer_instance

theorem CellStep.integer_sound (d : CellStep) (b : Box) (hi : d.IntegerAccepts b) : d.Accepts b := by
  have hd := d.rawDen_pos b
  have hn := d.rawNum_pos b
  have hpos : 0<(d.rawDen b).val := div_pos (by exact_mod_cast hi.1) (by exact_mod_cast hd)
  have hle := Raw.le_sound _ _ hn (Raw.mul_pos _ _ (Raw.ofRat_pos _) hd) hi.2.1
  have hsix := Raw.sixth_sound _ _ _ _ hn (CellStep.rawH_pos b) (Raw.ofRat_pos _) hd hi.2.2
  rw [Raw.mul_val,Raw.ofRat_val,d.rawNum_val b,d.rawDen_val b] at hle
  rw [d.rawDen_val b] at hpos
  rw [d.rawNum_val b,CellStep.rawH_val,Raw.ofRat_val,d.rawDen_val b] at hsix
  exact ⟨hpos,hle,hsix⟩

end LonelyRunnerNew.LCNumeric
