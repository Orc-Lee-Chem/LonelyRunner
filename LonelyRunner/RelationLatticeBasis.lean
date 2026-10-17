import LonelyRunner.PrimeGridCover
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD

namespace LonelyRunner



/-- 论文 `lem:latticebasis`：三个正速度的共同最大公因子。 -/
def relationGcd (a b c : ℕ) : ℕ := (a.gcd b).gcd c

/-- 论文 `lem:latticebasis`：第一个本原法向量坐标。 -/
def relationA (a b c : ℕ) : ℕ := a / relationGcd a b c

/-- 论文 `lem:latticebasis`：第二个本原法向量坐标。 -/
def relationB (a b c : ℕ) : ℕ := b / relationGcd a b c

/-- 论文 `lem:latticebasis`：第三个本原法向量坐标。 -/
def relationC (a b c : ℕ) : ℕ := c / relationGcd a b c

private theorem relationGcd_pos (a b c : ℕ) (hc : 0 < c) :
    0 < relationGcd a b c := by
  exact Nat.gcd_pos_of_pos_right (a.gcd b) hc

private theorem relationGcd_dvd_a (a b c : ℕ) : relationGcd a b c ∣ a :=
  (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)

private theorem relationGcd_dvd_b (a b c : ℕ) : relationGcd a b c ∣ b :=
  (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)

private theorem relationGcd_dvd_c (a b c : ℕ) : relationGcd a b c ∣ c :=
  Nat.gcd_dvd_right _ _

/-- 论文 `lem:latticebasis`：原关系方程等价于本原系数关系方程。 -/
theorem relationEquation_iff (a b c : ℕ) (hc : 0 < c)
    (w : Fin 3 → ℤ) :
    (a : ℤ) * w 0 + (b : ℤ) * w 1 + (c : ℤ) * w 2 = 0 ↔
      (relationA a b c : ℤ) * w 0 + (relationB a b c : ℤ) * w 1 +
        (relationC a b c : ℤ) * w 2 = 0 := by
  let g := relationGcd a b c
  have hg : g ≠ 0 := Nat.ne_of_gt (relationGcd_pos a b c hc)
  have ha : a = g * relationA a b c := by
    simp only [relationA, g]
    exact ((Nat.mul_comm _ _).trans (Nat.div_mul_cancel (relationGcd_dvd_a a b c))).symm
  have hb : b = g * relationB a b c := by
    simp only [relationB, g]
    exact ((Nat.mul_comm _ _).trans (Nat.div_mul_cancel (relationGcd_dvd_b a b c))).symm
  have hc' : c = g * relationC a b c := by
    simp only [relationC, g]
    exact ((Nat.mul_comm _ _).trans (Nat.div_mul_cancel (relationGcd_dvd_c a b c))).symm
  have haZ : (a : ℤ) = (g : ℤ) * (relationA a b c : ℤ) := by exact_mod_cast ha
  have hbZ : (b : ℤ) = (g : ℤ) * (relationB a b c : ℤ) := by exact_mod_cast hb
  have hcZ : (c : ℤ) = (g : ℤ) * (relationC a b c : ℤ) := by exact_mod_cast hc'
  have heq : (a : ℤ) * w 0 + (b : ℤ) * w 1 + (c : ℤ) * w 2 =
      (g : ℤ) * ((relationA a b c : ℤ) * w 0 +
        (relationB a b c : ℤ) * w 1 + (relationC a b c : ℤ) * w 2) := by
    rw [haZ, hbZ, hcZ]
    ring
  rw [heq, mul_eq_zero]
  simp [hg]

/-- 论文 `lem:latticebasis`：`(A,B,C)=(a,b,c)/g` 是本原整数三元组。 -/
theorem relationPrimitive (a b c : ℕ) (hc : 0 < c) :
    (relationA a b c |>.gcd (relationB a b c)).gcd (relationC a b c) = 1 := by
  let g := relationGcd a b c
  have hg : 0 < g := relationGcd_pos a b c hc
  have ha : a = g * relationA a b c := by
    simp only [relationA, g]
    exact ((Nat.mul_comm _ _).trans (Nat.div_mul_cancel (relationGcd_dvd_a a b c))).symm
  have hb : b = g * relationB a b c := by
    simp only [relationB, g]
    exact ((Nat.mul_comm _ _).trans (Nat.div_mul_cancel (relationGcd_dvd_b a b c))).symm
  have hc' : c = g * relationC a b c := by
    simp only [relationC, g]
    exact ((Nat.mul_comm _ _).trans (Nat.div_mul_cancel (relationGcd_dvd_c a b c))).symm
  have hmul : g * ((relationA a b c).gcd (relationB a b c)).gcd
      (relationC a b c) = g := by
    rw [← Nat.gcd_mul_left, ← Nat.gcd_mul_left, ← ha, ← hb, ← hc']
    rfl
  exact Nat.mul_left_cancel hg (by simpa only [mul_one] using hmul)

/-- 论文 `lem:latticebasis`：原始整数关系格 `Λ`。 -/
def relationLattice (a b c : ℕ) : Set (Fin 3 → ℤ) :=
  {w | (a : ℤ) * w 0 + (b : ℤ) * w 1 + (c : ℤ) * w 2 = 0}

/-- 论文 `lem:latticebasis`：`d=gcd(A,B)`，用于显式格基。 -/
def relationD (A B : ℕ) : ℕ := A.gcd B

/-- 论文 `lem:latticebasis`：第一个显式整数基向量 `(B',-A',0)`。 -/
def relationU0 (A B : ℕ) : Fin 3 → ℤ :=
  ![((B / relationD A B : ℕ) : ℤ), -((A / relationD A B : ℕ) : ℤ), 0]

/-- 论文 `lem:latticebasis`：第二个显式整数基向量 `(-rC,-sC,d)`，
其中 `r=Nat.gcdA A B`、`s=Nat.gcdB A B` 是 Mathlib 的 Bézout 系数。 -/
def relationV0 (A B C : ℕ) : Fin 3 → ℤ :=
  ![-(Nat.gcdA A B * (C : ℤ)), -(Nat.gcdB A B * (C : ℤ)),
      (relationD A B : ℤ)]

/-- 论文 `lem:latticebasis`：三维整数向量的代数叉积。此处未使用欧氏范数。 -/
def relationCross (u v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- 论文 `lem:latticebasis`：Mathlib 的 Bézout 系数满足 `rA+sB=d`。 -/
theorem relationBezout (A B : ℕ) :
    Nat.gcdA A B * (A : ℤ) + Nat.gcdB A B * (B : ℤ) =
      (relationD A B : ℤ) := by
  simpa only [relationD, mul_comm] using (Nat.gcd_eq_gcd_ab A B).symm

private theorem relationD_pos (A B : ℕ) (hA : 0 < A) :
    0 < relationD A B := Nat.gcd_pos_of_pos_left B hA

private theorem relationA_mul_div (A B : ℕ) :
    (A / relationD A B) * relationD A B = A :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left A B)

private theorem relationB_mul_div (A B : ℕ) :
    (B / relationD A B) * relationD A B = B :=
  Nat.div_mul_cancel (Nat.gcd_dvd_right A B)

private theorem relationA_factor (A B : ℕ) :
    (A : ℤ) = (relationD A B : ℤ) * ((A / relationD A B : ℕ) : ℤ) := by
  have h := relationA_mul_div A B
  exact_mod_cast ((Nat.mul_comm _ _).trans h).symm

private theorem relationB_factor (A B : ℕ) :
    (B : ℤ) = (relationD A B : ℤ) * ((B / relationD A B : ℕ) : ℤ) := by
  have h := relationB_mul_div A B
  exact_mod_cast ((Nat.mul_comm _ _).trans h).symm

/-- 论文 `lem:latticebasis`：`A'=A/d` 与 `B'=B/d` 互素。 -/
theorem relationReducedCoprime (A B : ℕ) (hA : 0 < A) :
    Nat.Coprime (A / relationD A B) (B / relationD A B) :=
  Nat.coprime_div_gcd_div_gcd (relationD_pos A B hA)

private theorem relationBezout_reduced (A B : ℕ) (hA : 0 < A) :
    Nat.gcdA A B * ((A / relationD A B : ℕ) : ℤ) +
      Nat.gcdB A B * ((B / relationD A B : ℕ) : ℤ) = 1 := by
  have hAf := relationA_factor A B
  have hBf := relationB_factor A B
  have hbez := relationBezout A B
  have hd : (relationD A B : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (relationD_pos A B hA))
  apply (mul_left_cancel₀ hd)
  calc
    (relationD A B : ℤ) *
        (Nat.gcdA A B * ((A / relationD A B : ℕ) : ℤ) +
          Nat.gcdB A B * ((B / relationD A B : ℕ) : ℤ)) =
        Nat.gcdA A B * (A : ℤ) + Nat.gcdB A B * (B : ℤ) := by
          rw [hAf, hBf]
          ring
    _ = (relationD A B : ℤ) * 1 := by rw [hbez]; ring

/-- 论文 `lem:latticebasis`：`u₀=(B',-A',0)` 满足本原关系方程。 -/
theorem relationU0_mem (A B C : ℕ) :
    (A : ℤ) * relationU0 A B 0 + (B : ℤ) * relationU0 A B 1 +
      (C : ℤ) * relationU0 A B 2 = 0 := by
  rw [relationA_factor A B, relationB_factor A B]
  simp [relationU0]
  ring

/-- 论文 `lem:latticebasis`：`v₀=(-rC,-sC,d)` 满足本原关系方程。 -/
theorem relationV0_mem (A B C : ℕ) :
    (A : ℤ) * relationV0 A B C 0 + (B : ℤ) * relationV0 A B C 1 +
      (C : ℤ) * relationV0 A B C 2 = 0 := by
  calc
    _ = (C : ℤ) *
        ((relationD A B : ℤ) -
          (Nat.gcdA A B * (A : ℤ) + Nat.gcdB A B * (B : ℤ))) := by
            dsimp [relationV0]
            ring
    _ = 0 := by rw [relationBezout]; ring

/-- 论文 `lem:latticebasis`：显式基的整数叉积正好是本原法向量的相反数。 -/
theorem relationCross_basis (A B C : ℕ) (hA : 0 < A) :
    relationCross (relationU0 A B) (relationV0 A B C) =
      ![-(A : ℤ), -(B : ℤ), -(C : ℤ)] := by
  have hAf := relationA_factor A B
  have hBf := relationB_factor A B
  have hsmall := relationBezout_reduced A B hA
  funext i
  fin_cases i <;> dsimp [relationCross, relationU0, relationV0] <;>
    simp only [← Int.natCast_div] <;>
    nlinarith [hAf, hBf, congrArg (fun z : ℤ => z * (C : ℤ)) hsmall]

/-- 论文 `lem:latticebasis`：每个本原关系格点可由显式两向量作整数线性组合。 -/
theorem relationBasis_exists (A B C : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hprim : (A.gcd B).gcd C = 1) (w : Fin 3 → ℤ)
    (hw : (A : ℤ) * w 0 + (B : ℤ) * w 1 + (C : ℤ) * w 2 = 0) :
    ∃ j t : ℤ, w = fun i => j * relationU0 A B i + t * relationV0 A B C i := by
  let d := relationD A B
  let P := A / d
  let Q := B / d
  let r := Nat.gcdA A B
  let s := Nat.gcdB A B
  have hdpos : 0 < d := relationD_pos A B hA
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hQpos : 0 < Q :=
    Nat.div_pos (Nat.le_of_dvd hB (Nat.gcd_dvd_right A B)) hdpos
  have hQ : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQpos)
  have hAf : (A : ℤ) = (d : ℤ) * (P : ℤ) := relationA_factor A B
  have hBf : (B : ℤ) = (d : ℤ) * (Q : ℤ) := relationB_factor A B
  have hred : r * (P : ℤ) + s * (Q : ℤ) = 1 :=
    relationBezout_reduced A B hA
  have hcopDC : Nat.Coprime d C := hprim
  have hdA : (d : ℤ) ∣ (A : ℤ) := by exact_mod_cast (Nat.gcd_dvd_left A B)
  have hdB : (d : ℤ) ∣ (B : ℤ) := by exact_mod_cast (Nat.gcd_dvd_right A B)
  have hdCz : (d : ℤ) ∣ (C : ℤ) * w 2 := by
    have hsum : (d : ℤ) ∣ (A : ℤ) * w 0 + (B : ℤ) * w 1 :=
      (dvd_mul_of_dvd_left hdA _).add (dvd_mul_of_dvd_left hdB _)
    have heq : (C : ℤ) * w 2 = -((A : ℤ) * w 0 + (B : ℤ) * w 1) := by
      linarith [hw]
    rw [heq]
    exact dvd_neg.mpr hsum
  have hdz : (d : ℤ) ∣ w 2 :=
    (hcopDC.isCoprime : IsCoprime (d : ℤ) (C : ℤ)).dvd_of_dvd_mul_left hdCz
  obtain ⟨t, ht⟩ := hdz
  have hn : (P : ℤ) * w 0 + (Q : ℤ) * w 1 + (C : ℤ) * t = 0 := by
    have hprod : (d : ℤ) *
        ((P : ℤ) * w 0 + (Q : ℤ) * w 1 + (C : ℤ) * t) = 0 := by
      calc
        _ = (A : ℤ) * w 0 + (B : ℤ) * w 1 + (C : ℤ) * w 2 := by
          rw [hAf, hBf, ht]
          ring
        _ = 0 := hw
    exact (mul_eq_zero.mp hprod).resolve_left hd
  let X : ℤ := w 0 + t * r * (C : ℤ)
  let Y : ℤ := w 1 + t * s * (C : ℤ)
  have hxy : (P : ℤ) * X + (Q : ℤ) * Y = 0 := by
    dsimp [X, Y]
    calc
      _ = ((P : ℤ) * w 0 + (Q : ℤ) * w 1 + (C : ℤ) * t) +
            t * (C : ℤ) * (r * (P : ℤ) + s * (Q : ℤ) - 1) := by ring
      _ = 0 := by rw [hn, hred]; ring
  have hQX : (Q : ℤ) ∣ X := by
    apply ((relationReducedCoprime A B hA).symm.isCoprime :
      IsCoprime (Q : ℤ) (P : ℤ)).dvd_of_dvd_mul_left
    refine ⟨-Y, ?_⟩
    nlinarith [hxy]
  obtain ⟨j, hj⟩ := hQX
  have hY : Y = -(P : ℤ) * j := by
    have hmul : (Q : ℤ) * ((P : ℤ) * j + Y) = 0 := by
      rw [hj] at hxy
      nlinarith [hxy]
    have hzero := (mul_eq_zero.mp hmul).resolve_left hQ
    linarith
  refine ⟨j, t, ?_⟩
  funext i
  fin_cases i
  · dsimp [relationU0, relationV0]
    rw [← Int.natCast_div]
    dsimp [X] at hj
    nlinarith [hj]
  · dsimp [relationU0, relationV0]
    rw [← Int.natCast_div]
    dsimp [Y] at hY
    nlinarith [hY]
  · simpa [relationU0, relationV0, d, mul_comm] using ht

/-- 论文 `lem:latticebasis`：显式两向量的整数线性组合参数唯一。 -/
theorem relationBasis_repr_injective (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) :
    Function.Injective (fun jt : ℤ × ℤ =>
      (fun i : Fin 3 => jt.1 * relationU0 A B i + jt.2 * relationV0 A B C i)) := by
  intro p q hpq
  have hd : (relationD A B : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (relationD_pos A B hA))
  have hQpos : 0 < B / relationD A B :=
    Nat.div_pos (Nat.le_of_dvd hB (Nat.gcd_dvd_right A B))
      (relationD_pos A B hA)
  have hQ : (((B / relationD A B : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hQpos)
  have hz := congrArg (fun f : Fin 3 → ℤ => f 2) hpq
  have ht : p.2 = q.2 := by
    have hmul : (relationD A B : ℤ) * p.2 =
        (relationD A B : ℤ) * q.2 := by
      simpa [relationU0, relationV0, mul_comm] using hz
    exact mul_left_cancel₀ hd hmul
  have hx := congrArg (fun f : Fin 3 → ℤ => f 0) hpq
  have hj : p.1 = q.1 := by
    have hmul : ((B / relationD A B : ℕ) : ℤ) * p.1 =
        ((B / relationD A B : ℕ) : ℤ) * q.1 := by
      dsimp [relationU0, relationV0] at hx
      rw [← Int.natCast_div] at hx
      rw [ht] at hx
      nlinarith [hx]
    exact mul_left_cancel₀ hQ hmul
  exact Prod.ext hj ht

/-- 论文 `lem:latticebasis`：每个本原关系格点存在唯一一对整数基坐标。 -/
theorem relationBasis_existsUnique (A B C : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hprim : (A.gcd B).gcd C = 1) (w : Fin 3 → ℤ)
    (hw : (A : ℤ) * w 0 + (B : ℤ) * w 1 + (C : ℤ) * w 2 = 0) :
    ∃! jt : ℤ × ℤ,
      w = fun i => jt.1 * relationU0 A B i + jt.2 * relationV0 A B C i := by
  obtain ⟨j, t, hrepr⟩ := relationBasis_exists A B C hA hB hprim w hw
  refine ⟨(j, t), hrepr, ?_⟩
  intro jt hjt
  exact relationBasis_repr_injective A B C hA hB (hjt.symm.trans hrepr)

private theorem relationA_pos (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    0 < relationA a b c :=
  Nat.div_pos (Nat.le_of_dvd ha (relationGcd_dvd_a a b c))
    (relationGcd_pos a b c hc)

private theorem relationB_pos (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    0 < relationB a b c :=
  Nat.div_pos (Nat.le_of_dvd hb (relationGcd_dvd_b a b c))
    (relationGcd_pos a b c hc)

/-- 论文 `lem:latticebasis`：本原性蕴含 `gcd(d,C)=1`，用于证明 `d∣z`。 -/
theorem relationD_coprime_C (a b c : ℕ) (hc : 0 < c) :
    Nat.Coprime
      (relationD (relationA a b c) (relationB a b c))
      (relationC a b c) :=
  relationPrimitive a b c hc

/-- 论文 `lem:latticebasis`：本原基的第一向量确实属于原始关系格 `Λ`。 -/
theorem relationU0_mem_lattice (a b c : ℕ) (hc : 0 < c) :
    relationU0 (relationA a b c) (relationB a b c) ∈
      relationLattice a b c := by
  exact (relationEquation_iff a b c hc _).mpr
    (relationU0_mem (relationA a b c) (relationB a b c) (relationC a b c))

/-- 论文 `lem:latticebasis`：本原基的第二向量确实属于原始关系格 `Λ`。 -/
theorem relationV0_mem_lattice (a b c : ℕ) (hc : 0 < c) :
    relationV0 (relationA a b c) (relationB a b c) (relationC a b c) ∈
      relationLattice a b c := by
  exact (relationEquation_iff a b c hc _).mpr
    (relationV0_mem (relationA a b c) (relationB a b c) (relationC a b c))

/-- 论文 `lem:latticebasis`：原始关系格每个格点存在唯一的 `j u₀+t v₀` 表示。 -/
theorem relationLattice_basis_existsUnique (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (w : Fin 3 → ℤ) (hw : w ∈ relationLattice a b c) :
    ∃! jt : ℤ × ℤ,
      w = fun i =>
        jt.1 * relationU0 (relationA a b c) (relationB a b c) i +
        jt.2 * relationV0 (relationA a b c) (relationB a b c)
          (relationC a b c) i := by
  exact relationBasis_existsUnique (relationA a b c) (relationB a b c)
    (relationC a b c) (relationA_pos a b c ha hc)
    (relationB_pos a b c hb hc) (relationPrimitive a b c hc) w
    ((relationEquation_iff a b c hc w).mp hw)

/-- 论文 `lem:latticebasis`：原始关系格显式基的叉积为本原法向量的相反数。 -/
theorem relationLattice_basis_cross (a b c : ℕ)
    (ha : 0 < a) (hc : 0 < c) :
    relationCross
      (relationU0 (relationA a b c) (relationB a b c))
      (relationV0 (relationA a b c) (relationB a b c) (relationC a b c)) =
        ![-(relationA a b c : ℤ), -(relationB a b c : ℤ),
          -(relationC a b c : ℤ)] :=
  relationCross_basis (relationA a b c) (relationB a b c) (relationC a b c)
    (relationA_pos a b c ha hc)

#print axioms LonelyRunner.relationEquation_iff
#print axioms LonelyRunner.relationPrimitive
#print axioms LonelyRunner.relationBezout
#print axioms LonelyRunner.relationReducedCoprime
#print axioms LonelyRunner.relationD_coprime_C
#print axioms LonelyRunner.relationU0_mem_lattice
#print axioms LonelyRunner.relationV0_mem_lattice
#print axioms LonelyRunner.relationLattice_basis_existsUnique
#print axioms LonelyRunner.relationLattice_basis_cross

end LonelyRunner
