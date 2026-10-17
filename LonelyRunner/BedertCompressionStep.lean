import LonelyRunner.ModularModelTransfer
import LonelyRunner.ModularSimultaneousCompression
import Mathlib.NumberTheory.Bertrand

/-!
# Bedert 建模的单步压缩

对应论文 `prop:bedert` 建模输入。这里从明确的 `L` 条件构造单步模型；
不处理重复压缩的累计误差或最终低高度模型。
-/

namespace LonelyRunner
open Finset

/-- 高度小于模数时，自然数速度到实际模像的映射单射。 -/
theorem bedert_modCast_injOn (V : Finset ℕ) (M p : ℕ) (hlarge : 2 * M < p)
    (hV : ∀ v ∈ V, v ≤ M) : Set.InjOn (fun v : ℕ => (v : ZMod p)) V := by
  have : NeZero p := ⟨by omega⟩
  intro a ha b hb heq
  have halt : a < p := by have := hV a ha; omega
  have hblt : b < p := by have := hV b hb; omega
  simpa only [ZMod.val_natCast_of_lt halt, ZMod.val_natCast_of_lt hblt] using
    congrArg ZMod.val heq

/-- 实际模像保留基数。 -/
theorem bedert_modCast_card (V : Finset ℕ) (M p : ℕ) (hlarge : 2 * M < p)
    (hV : ∀ v ∈ V, v ≤ M) :
    (V.image (fun v : ℕ => (v : ZMod p))).card = V.card :=
  card_image_iff.mpr (bedert_modCast_injOn V M p hlarge hV)

/-- 模像的二解离子集拉回后仍二解离：整数零关系必给出模零关系。 -/
theorem bedert_modCast_pullback (S : Finset ℕ) (p : ℕ)
    (hinj : Set.InjOn (fun v : ℕ => (v : ZMod p)) S)
    (hD : TwoDissociated (S.image (fun v : ℕ => (v : ZMod p)))) :
    TwoDissociated (S.image (fun v : ℕ => (v : ℤ))) := by
  classical
  intro c hc hs x hx
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
  have hsN : ∑ u ∈ S, c (u : ℤ) * (u : ℤ) = 0 := by
    rw [sum_image] at hs
    · simpa [zsmul_eq_mul] using hs
    · intro a ha b hb heq
      exact Nat.cast_injective heq
  have hsmod : ∑ u ∈ S, c (u : ℤ) • (u : ZMod p) = 0 := by
    have hh := congrArg (fun a : ℤ => (a : ZMod p)) hsN
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero,
      zsmul_eq_mul] using hh
  exact hD.image_relation S (fun u : ℕ => (u : ZMod p)) hinj
    (fun u => c (u : ℤ))
    (fun u hu => hc (u : ℤ) (mem_image.mpr ⟨u, hu, rfl⟩)) hsmod v hv

/-- 实际模像的最大二解离维数不超过原整数嵌入的维数。 -/
theorem bedert_modCast_dimension_le (V : Finset ℕ) (M p : ℕ)
    (hlarge : 2 * M < p) (hV : ∀ v ∈ V, v ≤ M) :
    twoDissociatedDimension (V.image (fun v : ℕ => (v : ZMod p))) ≤
      twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ))) := by
  classical
  obtain ⟨D, hDV, hD, hcard⟩ := twoDissociatedDimension_attained
    (V.image (fun v : ℕ => (v : ZMod p)))
  let S := V.filter (fun v : ℕ => (v : ZMod p) ∈ D)
  have hSV : S ⊆ V := filter_subset _ _
  have himage : S.image (fun v : ℕ => (v : ZMod p)) = D := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hv).2
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp (hDV hx)
      exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hx⟩, rfl⟩
  have hf := (bedert_modCast_injOn V M p hlarge hV).mono hSV
  have hsource := bedert_modCast_pullback S p hf (by rw [himage]; exact hD)
  rw [← hcard]
  calc
    D.card = (S.image (fun v : ℕ => (v : ZMod p))).card := by rw [himage]
    _ = S.card := card_image_iff.mpr hf
    _ = (S.image (fun v : ℕ => (v : ℤ))).card :=
      (card_image_iff.mpr (fun a ha b hb heq => Nat.cast_injective heq)).symm
    _ ≤ _ := card_le_twoDissociatedDimension (image_subset_image hSV) hsource

/-- 自然数高度 `Q=(4dp)/L` 的严格小关系界、实数高度界和覆盖误差界。 -/
theorem bedertCompressionStep_numeric (m d M p L : ℕ) (hm : 2 ≤ m) (hd : 1 ≤ d)
    (hp : 0 < p) (hpM : p ≤ 4 * M) (hL : 16 * m * d ≤ L) :
    let Q := (4 * d * p) / L
    2 * m * Q < p ∧ (Q : ℝ) ≤ 16 * (d : ℝ) * (M : ℝ) / (L : ℝ) ∧
      16 * (d : ℝ) * (M : ℝ) / (L : ℝ) ≤ (M : ℝ) / 2 ∧
      (Q : ℝ) / (p : ℝ) ≤ 4 * (d : ℝ) / (L : ℝ) := by
  intro Q
  have hLpos : 0 < L := by nlinarith
  have hdpos : 0 < 4 * d := by omega
  have hq : Q * L ≤ 4 * d * p := Nat.div_mul_le_self _ _
  have hprod : (4 * d) * (4 * m * Q) ≤ (4 * d) * p := by
    calc
      _ = (16 * m * d) * Q := by ring
      _ ≤ L * Q := Nat.mul_le_mul_right Q hL
      _ = Q * L := mul_comm _ _
      _ ≤ _ := hq
  have h4 : 4 * m * Q ≤ p := (mul_le_mul_iff_right₀ hdpos).mp hprod
  have hsmall : 2 * m * Q < p := by nlinarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (Q : ℝ) * (L : ℝ) ≤ 4 * (d : ℝ) * (p : ℝ) := by exact_mod_cast hq
  have hpMR : (p : ℝ) ≤ 4 * (M : ℝ) := by exact_mod_cast hpM
  have h32 : 32 * d ≤ L := by nlinarith
  have h32R : 32 * (d : ℝ) ≤ (L : ℝ) := by exact_mod_cast h32
  refine ⟨hsmall, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hLR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpMR (show (0 : ℝ) ≤ 4 * (d : ℝ) by positivity)]
  · apply (div_le_iff₀ hLR).mpr
    nlinarith [mul_le_mul_of_nonneg_right h32R (show (0 : ℝ) ≤ M by positivity)]
  · exact (div_le_div_iff₀ hpR hLR).mpr hqR

/-- 单步压缩的无外部构造参数接口。素数、非零缩放及整数代表均在证明内构造。
同一个正整数模型对每个原有逐点距离覆盖界给出所述误差转移。
这里只保留明确的 `L` 条件，不声称已完成反复压缩或误差累积。 -/
theorem bedertCompressionStep (V : Finset ℕ) (M d L : ℕ)
    (hV : ∀ v ∈ V, 0 < v ∧ v ≤ M) (hm : 2 ≤ V.card) (hd : 1 ≤ d)
    (hdim : twoDissociatedDimension (V.image (fun v : ℕ => (v : ℤ))) ≤ d)
    (hL : 16 * V.card * d ≤ L) (hpow : L ^ (2 * d) < 2 * M) :
    ∃ (W : Finset ℕ) (Q : ℕ), 0 < Q ∧ W.card = V.card ∧
      (∀ w ∈ W, 1 ≤ w ∧ w ≤ Q) ∧
      twoDissociatedDimension (W.image (fun w : ℕ => (w : ℤ))) ≤ d ∧
      (Q : ℝ) ≤ 16 * (d : ℝ) * (M : ℝ) / (L : ℝ) ∧
      16 * (d : ℝ) * (M : ℝ) / (L : ℝ) ≤ (M : ℝ) / 2 ∧
      ∀ δ : ℝ, (∀ t : UnitAddCircle, ∃ v ∈ V, dist (v • t) 0 ≤ δ) →
        ∀ t : UnitAddCircle, ∃ w ∈ W,
          dist (w • t) 0 ≤ δ + 4 * (d : ℝ) / (L : ℝ) := by
  classical
  obtain ⟨v₀, hv₀⟩ := card_pos.mp (show 0 < V.card by omega)
  have hMpos : 0 < M := (hV v₀ hv₀).1.trans_le (hV v₀ hv₀).2
  have hLpos : 0 < L := by nlinarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  obtain ⟨p, hp, hlarge, hpupper⟩ := Nat.exists_prime_lt_and_le_two_mul
    (2 * M) (by positivity)
  have hpM : p ≤ 4 * M := by omega
  have hodd : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  let B := V.image (fun v : ℕ => (v : ZMod p))
  have hBcard : B.card = V.card := bedert_modCast_card V M p hlarge (fun v hv => (hV v hv).2)
  have hBdim : twoDissociatedDimension B ≤ d :=
    (bedert_modCast_dimension_le V M p hlarge (fun v hv => (hV v hv).2)).trans hdim
  obtain ⟨D₀, hD₀B, hD₀, hD₀dim, hDcard, hspan⟩ :=
    zmod_twoDissociatedDimension_spanning p hodd B
  let D := D₀ ∪ D₀.image (fun x => x / 2)
  have hDdim : D.card ≤ 2 * d := by
    change D.card ≤ 2 * twoDissociatedDimension B at hDcard
    omega
  have hDpow : L ^ D.card < p :=
    (pow_le_pow_right' (by omega : 1 ≤ L) hDdim).trans_lt (hpow.trans hlarge)
  obtain ⟨lam, hlam, hgenerators, hreps⟩ :=
    modularSimultaneousCompression_of_twoBoundedSpan p hp D B L hLpos hDpow hspan
  have hrepsV : ∀ v ∈ V, ∃ a : ℤ, (a : ZMod p) = lam * (v : ZMod p) ∧
      |(a : ℝ)| ≤ 4 * (d : ℝ) * (p : ℝ) / (L : ℝ) := by
    intro v hv
    obtain ⟨a, ha, habs⟩ := hreps (v : ZMod p) (mem_image.mpr ⟨v, hv, rfl⟩)
    refine ⟨a, ha, habs.trans ?_⟩
    have hDreal : (D.card : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast hDdim
    apply div_le_div_of_nonneg_right _ hLR.le
    nlinarith [mul_le_mul_of_nonneg_right hDreal (show (0 : ℝ) ≤ p by positivity)]
  let z : ℕ → ℤ := fun v => if hv : v ∈ V then (hrepsV v hv).choose else 0
  have hzall : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p) ∧
      |(z v : ℝ)| ≤ 4 * (d : ℝ) * (p : ℝ) / (L : ℝ) := by
    intro v hv
    simpa only [z, dite_eq_left hv] using (hrepsV v hv).choose_spec
  let Q := (4 * d * p) / L
  have hQ : ∀ v ∈ V, |z v| ≤ (Q : ℤ) := by
    intro v hv
    have hnatR : ((z v).natAbs : ℝ) ≤ 4 * (d : ℝ) * (p : ℝ) / (L : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      exact (hzall v hv).2
    have hmulR := (le_div_iff₀ hLR).mp hnatR
    have hmul : (z v).natAbs * L ≤ 4 * d * p := by exact_mod_cast hmulR
    have hnat : (z v).natAbs ≤ Q := (Nat.le_div_iff_mul_le hLpos).mpr hmul
    have hi : ((z v).natAbs : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hnat
    simpa only [Int.natCast_natAbs] using hi
  have hz : ∀ v ∈ V, (z v : ZMod p) = lam * (v : ZMod p) :=
    fun v hv => (hzall v hv).1
  obtain ⟨hsmall, hQheight, hhalf, herror⟩ :=
    bedertCompressionStep_numeric V.card d M p L hm hd hp.pos hpM hL
  obtain ⟨hcard, hbounds⟩ := modularModel_card_bounds V M p Q hp hlarge lam hlam z hV hz hQ
  have hQpos : 0 < Q := by
    have hh := hbounds (z v₀).natAbs (mem_image.mpr ⟨v₀, hv₀, rfl⟩)
    omega
  refine ⟨modularModelSpeeds V z, Q, hQpos, hcard, hbounds,
    (modularModel_dimension_le V M p Q hp hlarge lam hlam z hV hz hQ hsmall).trans hdim,
    hQheight, hhalf, ?_⟩
  intro δ hcover t
  obtain ⟨_, _, _, htransfer⟩ :=
    modularModel_transfer V M p Q hp hlarge lam hlam z hV hz hQ hsmall δ hcover
  obtain ⟨w, hw, hwt⟩ := htransfer t
  exact ⟨w, hw, hwt.trans (by linarith)⟩

#print axioms bedert_modCast_card
#print axioms bedert_modCast_dimension_le
#print axioms bedertCompressionStep_numeric
#print axioms bedertCompressionStep

end LonelyRunner
