import LonelyRunnerNew.PhysicalBlockTransport
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace LonelyRunnerNew.DyadicPhysical

def index (r : ℝ) : ℕ :=
  if h : 1≤r then Classical.choose (exists_nat_pow_near h (by norm_num : (1:ℝ)<2)) else 0

theorem index_bounds {r : ℝ} (hr : 1≤r) :
    (2:ℝ)^(index r)≤r ∧ r<(2:ℝ)^(index r+1) := by
  unfold index
  rw [dif_pos hr]
  exact Classical.choose_spec (exists_nat_pow_near hr (by norm_num : (1:ℝ)<2))

def gap (i j : ℕ) : ℕ := ((i:ℤ)-(j:ℤ)).natAbs

end LonelyRunnerNew.DyadicPhysical

namespace LonelyRunnerNew.TaggedState
variable {Label : Type*} [DecidableEq Label] {n : ℕ}

def blockUnit (s : TaggedState Label n) : ℝ := min s.a s.b
def leftBlockCode (s : TaggedState Label n) (x : Label) : ℕ :=
  DyadicPhysical.index (s.a*(s.leftValue x:ℝ)/s.blockUnit)
def rightBlockCode (s : TaggedState Label n) (y : Label) : ℕ :=
  DyadicPhysical.index (s.b*(s.rightValue y:ℝ)/s.blockUnit)
def leftBlockCodes (s : TaggedState Label n) : Finset ℕ := s.left.image s.leftBlockCode
def rightBlockCodes (s : TaggedState Label n) : Finset ℕ := s.right.image s.rightBlockCode
def leftBlock (s : TaggedState Label n) (i : ℕ) : Finset Label := s.left.filter (fun x => s.leftBlockCode x=i)
def rightBlock (s : TaggedState Label n) (j : ℕ) : Finset Label := s.right.filter (fun y => s.rightBlockCode y=j)
def blockA (s : TaggedState Label n) (i : ℕ) : ℝ := s.blockUnit*(2:ℝ)^i/s.a
def blockB (s : TaggedState Label n) (j : ℕ) : ℝ := s.blockUnit*(2:ℝ)^j/s.b
def blockEdges (s : TaggedState Label n) (G : Finset (Label × Label)) (ij : ℕ × ℕ) : Finset (Label × Label) :=
  G.filter (fun e => (s.leftBlockCode e.1,s.rightBlockCode e.2)=ij)
def blockMass (s : TaggedState Label n) (G : Finset (Label × Label)) (ij : ℕ × ℕ) : ℝ :=
  ∑ e∈s.blockEdges G ij,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2)

theorem blockUnit_pos (s : TaggedState Label n) : 0<s.blockUnit := lt_min s.a_positive s.b_positive

theorem blockA_pos (s : TaggedState Label n) (i : ℕ) : 0<s.blockA i := by
  exact div_pos (mul_pos s.blockUnit_pos (by positivity)) s.a_positive
theorem blockB_pos (s : TaggedState Label n) (j : ℕ) : 0<s.blockB j := by
  exact div_pos (mul_pos s.blockUnit_pos (by positivity)) s.b_positive

theorem leftBlock_bounds (s : TaggedState Label n) {i : ℕ} {x : Label} (hx : x∈s.leftBlock i) :
    s.blockA i≤(s.leftValue x:ℝ) ∧ (s.leftValue x:ℝ)<2*s.blockA i := by
  obtain ⟨hx,hcode⟩ := Finset.mem_filter.mp hx
  have hv : (1:ℝ)≤s.leftValue x := by exact_mod_cast s.left_positive x hx
  have ha : s.blockUnit≤s.a*(s.leftValue x:ℝ) :=
    (min_le_left _ _).trans (by nlinarith [s.a_positive])
  have hb := DyadicPhysical.index_bounds ((le_div_iff₀ s.blockUnit_pos).mpr (by simpa using ha))
  change DyadicPhysical.index (s.a*(s.leftValue x:ℝ)/s.blockUnit)=i at hcode
  rw [hcode,pow_succ] at hb
  have hl := (le_div_iff₀ s.blockUnit_pos).mp hb.1
  have hu := (div_lt_iff₀ s.blockUnit_pos).mp hb.2
  constructor
  · exact (div_le_iff₀ s.a_positive).mpr (by nlinarith only [hl])
  · rw [blockA,← mul_div_assoc]
    apply (lt_div_iff₀ s.a_positive).mpr
    change (s.leftValue x:ℝ)*s.a<2*(s.blockUnit*(2:ℝ)^i)
    nlinarith only [hu]

theorem rightBlock_bounds (s : TaggedState Label n) {j : ℕ} {y : Label} (hy : y∈s.rightBlock j) :
    s.blockB j≤(s.rightValue y:ℝ) ∧ (s.rightValue y:ℝ)<2*s.blockB j := by
  obtain ⟨hy,hcode⟩ := Finset.mem_filter.mp hy
  have hv : (1:ℝ)≤s.rightValue y := by exact_mod_cast s.right_positive y hy
  have ha : s.blockUnit≤s.b*(s.rightValue y:ℝ) :=
    (min_le_right _ _).trans (by nlinarith [s.b_positive])
  have hb := DyadicPhysical.index_bounds ((le_div_iff₀ s.blockUnit_pos).mpr (by simpa using ha))
  change DyadicPhysical.index (s.b*(s.rightValue y:ℝ)/s.blockUnit)=j at hcode
  rw [hcode,pow_succ] at hb
  have hl := (le_div_iff₀ s.blockUnit_pos).mp hb.1
  have hu := (div_lt_iff₀ s.blockUnit_pos).mp hb.2
  constructor
  · exact (div_le_iff₀ s.b_positive).mpr (by nlinarith only [hl])
  · rw [blockB,← mul_div_assoc]
    apply (lt_div_iff₀ s.b_positive).mpr
    change (s.rightValue y:ℝ)*s.b<2*(s.blockUnit*(2:ℝ)^j)
    nlinarith only [hu]

theorem leftBlock_nonempty (s : TaggedState Label n) {i : ℕ} (hi : i∈s.leftBlockCodes) :
    (s.leftBlock i).Nonempty := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
  exact ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
theorem rightBlock_nonempty (s : TaggedState Label n) {j : ℕ} (hj : j∈s.rightBlockCodes) :
    (s.rightBlock j).Nonempty := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hj
  exact ⟨y,Finset.mem_filter.mpr ⟨hy,rfl⟩⟩

theorem blockEdges_eq_inter (s : TaggedState Label n) (G : Finset (Label × Label))
    (hG : G⊆s.edges) (i j : ℕ) :
    s.blockEdges G (i,j)=G∩(s.leftBlock i).product (s.rightBlock j) := by
  ext e
  simp only [blockEdges,Finset.mem_filter,Finset.mem_inter]
  constructor
  · rintro ⟨he,hc⟩
    have hm := Finset.mem_product.mp (s.edges_subset (hG he))
    exact ⟨he,Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm.1,(Prod.mk.inj hc).1⟩,
      Finset.mem_filter.mpr ⟨hm.2,(Prod.mk.inj hc).2⟩⟩⟩
  · rintro ⟨he,hp⟩
    have hh := Finset.mem_product.mp hp
    exact ⟨he,Prod.ext (Finset.mem_filter.mp hh.1).2 (Finset.mem_filter.mp hh.2).2⟩

theorem blockEdges_unique (s : TaggedState Label n) (G : Finset (Label × Label))
    {e : Label × Label} {ij kl : ℕ × ℕ} (hi : e∈s.blockEdges G ij) (hk : e∈s.blockEdges G kl) : ij=kl :=
  (Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hk).2

theorem blockMass_sum (s : TaggedState Label n) (G : Finset (Label × Label)) (hG : G⊆s.edges) :
    (∑ ij∈s.leftBlockCodes.product s.rightBlockCodes,s.blockMass G ij)=
      ∑ e∈G,weight s.a s.b (s.leftValue e.1) (s.rightValue e.2) := by
  unfold blockMass blockEdges
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro e he
  have hm := Finset.mem_product.mp (s.edges_subset (hG he))
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hm.1,Finset.mem_image_of_mem _ hm.2⟩

theorem leftBlock_card_sum (s : TaggedState Label n) :
    (∑ i∈s.leftBlockCodes,(s.leftBlock i).card)=s.left.card := by
  rw [show (∑ i∈s.leftBlockCodes,(s.leftBlock i).card)=
    (s.left.filter (fun x => s.leftBlockCode x∈s.leftBlockCodes)).card from
      Finset.sum_card_fiberwise_eq_card_filter _ _ _]
  have hf : s.left.filter (fun x => s.leftBlockCode x∈s.leftBlockCodes)=s.left :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_image_of_mem s.leftBlockCode hx)
  rw [hf]
theorem rightBlock_card_sum (s : TaggedState Label n) :
    (∑ j∈s.rightBlockCodes,(s.rightBlock j).card)=s.right.card := by
  rw [show (∑ j∈s.rightBlockCodes,(s.rightBlock j).card)=
    (s.right.filter (fun y => s.rightBlockCode y∈s.rightBlockCodes)).card from
      Finset.sum_card_fiberwise_eq_card_filter _ _ _]
  have hf : s.right.filter (fun y => s.rightBlockCode y∈s.rightBlockCodes)=s.right :=
    Finset.filter_eq_self.mpr (fun y hy => Finset.mem_image_of_mem s.rightBlockCode hy)
  rw [hf]

end LonelyRunnerNew.TaggedState
