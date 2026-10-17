import LonelyRunner.PrimeGridCover
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-! 论文 `paper/lonely_runner_zh.tex` 第 619–653 行，引理 `lem:denominator`。
本模块处理素数幂分摊与共同分母的对数上界。 -/

namespace LonelyRunner

/-- 论文第 584、599、620 行：`v/G` 的既约分母 `q_v=G/gcd(G,v)`。 -/
def reducedDenominator (G v : ℕ) : ℕ := G / Nat.gcd G v

/-- 论文第 620–623 行：非例外速度的共同分母 `Q`。空族的最小公倍数为 `1`。 -/
def commonDenominator (V E : Finset ℕ) (G : ℕ) : ℕ :=
  (V \ E).lcm (reducedDenominator G)

/-- 论文第 622 行的空指标边界：若全体速度被列为例外，空最小公倍数为 `1`。 -/
@[simp] theorem commonDenominator_all_exceptional (V : Finset ℕ) (G : ℕ) :
    commonDenominator V V G = 1 := by
  simp [commonDenominator]

/-- 论文第 622 行的无例外边界：`E=∅` 时取全体速度的分母最小公倍数。 -/
@[simp] theorem commonDenominator_no_exceptions (V : Finset ℕ) (G : ℕ) :
    commonDenominator V ∅ G = V.lcm (reducedDenominator G) := by
  simp [commonDenominator]

/-- 论文第 638 行：`G>0` 时，每个既约分母为正且整除 `G`。 -/
theorem reducedDenominator_pos_dvd (G v : ℕ) (hG : 0 < G) :
    0 < reducedDenominator G v ∧ reducedDenominator G v ∣ G := by
  have hdvd : Nat.gcd G v ∣ G := Nat.gcd_dvd_left G v
  have hgdpos : 0 < Nat.gcd G v := Nat.gcd_pos_of_pos_left v hG
  constructor
  · exact Nat.div_pos (Nat.le_of_dvd hG hdvd) hgdpos
  · exact Nat.div_dvd_of_dvd hdvd

/-- 论文第 638 行：包括 `V\E=∅` 的情形，`Q>0` 且 `Q∣G`。 -/
theorem commonDenominator_pos_dvd (V E : Finset ℕ) (G : ℕ) (hG : 0 < G) :
    0 < commonDenominator V E G ∧ commonDenominator V E G ∣ G := by
  constructor
  · apply Nat.pos_of_ne_zero
    exact (Finset.lcm_ne_zero_iff).2 (by
      intro v hv
      exact (reducedDenominator_pos_dvd G v hG).1.ne')
  · exact Finset.lcm_dvd (fun v hv => (reducedDenominator_pos_dvd G v hG).2)

/-- 论文第 635–637 行：结合圆周网格覆盖与 `|C|≥m/2`，得到
`p≤2m` 且 `r_p≥p/4`。这里 `2mδ=1+ε`、`0≤ε≤1/2` 均为显式假设。 -/
theorem prime_size_and_nondivisible_lower (V C : Finset ℕ) (m G p : ℕ)
    (δ ε : ℝ) (hm : m = V.card) (hVpos : ∀ v ∈ V, 0 < v)
    (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2)
    (hirr : IrreducibleCover V δ) (hgcd : V.gcd id = 1)
    (hCV : C ⊆ V) (hCcard : (m : ℝ) / 2 ≤ (C.card : ℝ))
    (hGpos : 0 < G) (hGdiv : ∀ v ∈ C, G ∣ v)
    (hp : p.Prime) (hpG : p ∣ G)
    (hδeq : 2 * (m : ℝ) * δ = 1 + ε)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    (p : ℝ) ≤ 2 * (m : ℝ) ∧
      (p : ℝ) / 4 ≤ (nondivisibleCount V p : ℝ) := by
  have hgrid := prime_grid_cover_bound V C m G p δ hm hVpos hδ0 hδhalf
    hirr hgcd hCV hCcard hGpos hGdiv hp hpG
  have hrhalf := nondivisibleCount_le_half V C m G p hm hCV hCcard hGdiv hpG
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hmR : (0 : ℝ) < m := by
    obtain ⟨v, hv, _⟩ := hirr.1 0
    exact Nat.cast_pos.mpr (hm ▸ Finset.card_pos.mpr ⟨v, hv⟩)
  have hden : (0 : ℝ) < (p : ℝ) := hpR
  have hgrid' : (p : ℝ) ≤
      (nondivisibleCount V p : ℝ) * (2 * δ * (p : ℝ) + 1) := by
    have h := (mul_le_mul_of_nonneg_right hgrid hpR.le)
    field_simp at h ⊢
    nlinarith
  have hupper : (p : ℝ) ≤ 2 * (m : ℝ) := by
    have hfac : 0 ≤ 2 * δ + 1 / (p : ℝ) := by positivity
    have h := hgrid.trans (mul_le_mul_of_nonneg_right hrhalf hfac)
    have hmul := (mul_le_mul_of_nonneg_right h hpR.le)
    have heq := congrArg (fun x : ℝ => x * (p : ℝ)) hδeq
    field_simp at hmul
    nlinarith [mul_nonneg hε0 hpR.le]
  have hfactor : 2 * δ * (p : ℝ) + 1 ≤ 4 := by
    have hδm := mul_le_mul_of_nonneg_left hupper (show 0 ≤ δ by positivity)
    nlinarith [hδeq, hεhalf]
  have hrnonneg : (0 : ℝ) ≤ nondivisibleCount V p := Nat.cast_nonneg _
  constructor
  · exact hupper
  · nlinarith [hgrid', mul_le_mul_of_nonneg_left hfactor hrnonneg]

/-- 论文第 642 行：`p∤v` 时，`q_v` 保留 `G` 的完整 `p` 赋值。 -/
theorem reducedDenominator_factorization_of_not_dvd (G v p : ℕ)
    (hnp : ¬ p ∣ v) :
    (reducedDenominator G v).factorization p = G.factorization p := by
  have hngcd : ¬ p ∣ Nat.gcd G v := by
    intro hpv
    exact hnp (hpv.trans (Nat.gcd_dvd_right G v))
  rw [reducedDenominator, Nat.factorization_div (Nat.gcd_dvd_left G v)]
  simp [Nat.factorization_eq_zero_of_not_dvd hngcd]

/-- 论文第 638–641 行，式 `eq:localvaluation`：若所有非例外
`q_v≤2m`，则对 `p∣Q` 有 `ν_p(Q) log p≤log(2m)`。 -/
theorem commonDenominator_localValuation_bound (V E : Finset ℕ) (m G p : ℕ)
    (_hmpos : 0 < m) (hGpos : 0 < G)
    (hqbound : ∀ v ∈ V \ E, reducedDenominator G v ≤ 2 * m)
    (hp : p.Prime) (hpQ : p ∣ commonDenominator V E G) :
    ((commonDenominator V E G).factorization p : ℝ) * Real.log (p : ℝ) ≤
      Real.log (2 * (m : ℝ)) := by
  classical
  let Q := commonDenominator V E G
  have hQpos : 0 < Q := (commonDenominator_pos_dvd V E G hGpos).1
  have hbpos : 0 < Q.factorization p :=
    hp.factorization_pos_of_dvd hQpos.ne' hpQ
  have hfac : Q.factorization p =
      (V \ E).sup (fun v => (reducedDenominator G v).factorization p) := by
    exact Finset.factorization_lcm (fun v hv =>
      (reducedDenominator_pos_dvd G v hGpos).1.ne') p
  obtain ⟨v, hv, hle⟩ := (Finset.le_sup_iff hbpos).mp (by rw [← hfac])
  have hqfac : Q.factorization p = (reducedDenominator G v).factorization p := by
    apply le_antisymm hle
    rw [hfac]
    exact Finset.le_sup (s := V \ E)
      (f := fun v => (reducedDenominator G v).factorization p) hv
  have hqpos : 0 < reducedDenominator G v :=
    (reducedDenominator_pos_dvd G v hGpos).1
  have hpowdvd : p ^ Q.factorization p ∣ reducedDenominator G v :=
    (hp.pow_dvd_iff_le_factorization hqpos.ne').2 (by rw [hqfac])
  have hpowle : (p : ℝ) ^ Q.factorization p ≤
      (reducedDenominator G v : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hqpos hpowdvd
  have hlogpow : (Q.factorization p : ℝ) * Real.log (p : ℝ) ≤
      Real.log (reducedDenominator G v : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos (Nat.cast_pos.mpr hp.pos) _) hpowle
  have hqle : (reducedDenominator G v : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hqbound v hv
  exact hlogpow.trans (Real.log_le_log (Nat.cast_pos.mpr hqpos) hqle)

/-- 论文第 642–643 行：在非例外速度中仍未被 `p` 整除的集合 `S_p`。 -/
def survivingNondivisible (V E : Finset ℕ) (p : ℕ) : Finset ℕ :=
  (V \ E).filter (fun v => ¬ p ∣ v)

/-- 论文第 642–643 行：若 `p>8e` 且 `r_p≥p/4`，则
`|S_p|≥p/8`；每个 `v∈S_p` 的 `q_v` 都具有 `Q` 的完整 `p` 赋值。 -/
theorem large_prime_survivors_full_valuation (V E : Finset ℕ) (e G p : ℕ)
    (he : e = E.card) (hGpos : 0 < G) (hp : p.Prime)
    (_hpQ : p ∣ commonDenominator V E G) (hbig : 8 * e < p)
    (hrlower : (p : ℝ) / 4 ≤ (nondivisibleCount V p : ℝ)) :
    (p : ℝ) / 8 ≤ ((survivingNondivisible V E p).card : ℝ) ∧
      ∀ v ∈ survivingNondivisible V E p,
        (reducedDenominator G v).factorization p =
          (commonDenominator V E G).factorization p := by
  classical
  let S := survivingNondivisible V E p
  have hsub : V.filter (fun v => ¬ p ∣ v) ⊆ S ∪ E := by
    intro v hv
    by_cases hve : v ∈ E
    · exact Finset.mem_union.mpr (Or.inr hve)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hv).1,
          hve⟩, (Finset.mem_filter.mp hv).2⟩))
  have hcard : (V.filter (fun v => ¬ p ∣ v)).card ≤ S.card + E.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR : (nondivisibleCount V p : ℝ) ≤ (S.card : ℝ) + e := by
    exact_mod_cast (he ▸ hcard)
  have hbigR : 8 * (e : ℝ) < (p : ℝ) := by exact_mod_cast hbig
  have hSbound : (p : ℝ) / 8 ≤ (S.card : ℝ) := by linarith
  refine ⟨hSbound, ?_⟩
  have hSpos : 0 < S.card := by
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ) < (p : ℝ) / 8) hSbound)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hSpos
  have hQpos : 0 < commonDenominator V E G :=
    (commonDenominator_pos_dvd V E G hGpos).1
  have hQleG : (commonDenominator V E G).factorization p ≤ G.factorization p :=
    (Nat.factorization_le_iff_dvd hQpos.ne' hGpos.ne').2
      (commonDenominator_pos_dvd V E G hGpos).2 p
  have hwVE : w ∈ V \ E := (Finset.mem_filter.mp hw).1
  have hqpos : 0 < reducedDenominator G w :=
    (reducedDenominator_pos_dvd G w hGpos).1
  have hqleQ : (reducedDenominator G w).factorization p ≤
      (commonDenominator V E G).factorization p :=
    (Nat.factorization_le_iff_dvd hqpos.ne' hQpos.ne').2
      (Finset.dvd_lcm hwVE) p
  have hGQ : G.factorization p = (commonDenominator V E G).factorization p := by
    have hwG := reducedDenominator_factorization_of_not_dvd G w p
      (Finset.mem_filter.mp hw).2
    omega
  intro v hv
  rw [reducedDenominator_factorization_of_not_dvd G v p (Finset.mem_filter.mp hv).2,
    hGQ]

/-- 论文第 648 行：任意有限素数子集的赋值对数和不超过整数的对数。
`n=1` 时两边均为零。 -/
theorem partial_factorization_log_le (n : ℕ) (S : Finset ℕ) :
    ∑ p ∈ S, ((n.factorization p : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      Real.log (n : ℝ) := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  let T := S ∪ n.primeFactors
  have hT : n.factorization.support ⊆ T := by
    intro p hp
    exact Finset.mem_union.mpr (Or.inr (by simpa using hp))
  have hsum : n.factorization.sum (fun p t => (t : ℝ) * Real.log (p : ℝ)) =
      ∑ p ∈ T, ((n.factorization p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    exact Finsupp.sum_of_support_subset n.factorization hT
      (fun p t => (t : ℝ) * Real.log (p : ℝ)) (by simp)
  rw [hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (by intro p hp _; positivity)

/-- 论文第 644–651 行用于分摊的有限素数集合。 -/
def largePrimeFactors (V E : Finset ℕ) (e G : ℕ) : Finset ℕ :=
  (commonDenominator V E G).primeFactors.filter (fun p => 8 * e < p)

/-- 论文第 644–651 行，式 `eq:charge` 的纯有限求和部分。
假设每个大素数已有 `|S_p|≥p/8` 及完整赋值；后面的最终定理会
从不可约圆周覆盖推出这些条件。 -/
theorem finite_prime_charge_bound (V E : Finset ℕ) (m e G : ℕ)
    (hm : m = V.card) (hmpos : 0 < m) (hGpos : 0 < G)
    (hqbound : ∀ v ∈ V \ E, reducedDenominator G v ≤ 2 * m)
    (hlarge : ∀ p ∈ largePrimeFactors V E e G,
      (p : ℝ) / 8 ≤ ((survivingNondivisible V E p).card : ℝ) ∧
      ∀ v ∈ survivingNondivisible V E p,
        (reducedDenominator G v).factorization p =
          (commonDenominator V E G).factorization p) :
    ∑ p ∈ largePrimeFactors V E e G,
      (p : ℝ) * ((commonDenominator V E G).factorization p : ℝ) * Real.log (p : ℝ) ≤
        8 * (m : ℝ) * Real.log (2 * (m : ℝ)) := by
  classical
  let P := largePrimeFactors V E e G
  let T := V \ E
  let Q := commonDenominator V E G
  have hpoint : ∀ p ∈ P,
      (p : ℝ) * (Q.factorization p : ℝ) * Real.log (p : ℝ) ≤
        8 * ∑ v ∈ T,
          if ¬ p ∣ v then (Q.factorization p : ℝ) * Real.log (p : ℝ) else 0 := by
    intro p hp
    have hS := (hlarge p hp).1
    have hsum : (∑ v ∈ T,
        if ¬ p ∣ v then (Q.factorization p : ℝ) * Real.log (p : ℝ) else 0) =
        ((survivingNondivisible V E p).card : ℝ) *
          ((Q.factorization p : ℝ) * Real.log (p : ℝ)) := by
      rw [← Finset.sum_filter]
      simp [survivingNondivisible, T, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hweight : 0 ≤ (Q.factorization p : ℝ) * Real.log (p : ℝ) := by
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
    nlinarith [mul_nonneg (show 0 ≤ 8 *
      ((survivingNondivisible V E p).card : ℝ) - (p : ℝ) by linarith) hweight]
  have hinner : ∀ v ∈ T,
      (∑ p ∈ P, if ¬ p ∣ v then
        (Q.factorization p : ℝ) * Real.log (p : ℝ) else 0) ≤
        Real.log (reducedDenominator G v : ℝ) := by
    intro v hv
    calc
      (∑ p ∈ P, if ¬ p ∣ v then
          (Q.factorization p : ℝ) * Real.log (p : ℝ) else 0) ≤
          ∑ p ∈ P, ((reducedDenominator G v).factorization p : ℝ) *
            Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hnp : ¬ p ∣ v
        · have hvS : v ∈ survivingNondivisible V E p :=
            Finset.mem_filter.mpr ⟨hv, hnp⟩
          simp only [if_pos hnp]
          rw [(hlarge p hp).2 v hvS]
        · simp only [if_neg hnp]
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
      _ ≤ Real.log (reducedDenominator G v : ℝ) :=
        partial_factorization_log_le _ P
  have hsumlog : (∑ v ∈ T, Real.log (reducedDenominator G v : ℝ)) ≤
      (m : ℝ) * Real.log (2 * (m : ℝ)) := by
    have hcard : (T.card : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (hm ▸ Finset.card_le_card (Finset.sdiff_subset : T ⊆ V))
    have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := by
      apply Real.log_nonneg
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
      linarith
    calc
      (∑ v ∈ T, Real.log (reducedDenominator G v : ℝ)) ≤
          ∑ v ∈ T, Real.log (2 * (m : ℝ)) := by
        apply Finset.sum_le_sum
        intro v hv
        have hqpos := (reducedDenominator_pos_dvd G v hGpos).1
        have hqle : (reducedDenominator G v : ℝ) ≤ 2 * (m : ℝ) := by
          exact_mod_cast hqbound v hv
        exact Real.log_le_log (Nat.cast_pos.mpr hqpos) hqle
      _ = (T.card : ℝ) * Real.log (2 * (m : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * Real.log (2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hlog
  calc
    (∑ p ∈ P, (p : ℝ) * (Q.factorization p : ℝ) * Real.log (p : ℝ)) ≤
        ∑ p ∈ P, 8 * ∑ v ∈ T,
          if ¬ p ∣ v then (Q.factorization p : ℝ) * Real.log (p : ℝ) else 0 := by
      exact Finset.sum_le_sum hpoint
    _ = 8 * ∑ v ∈ T, ∑ p ∈ P,
          if ¬ p ∣ v then (Q.factorization p : ℝ) * Real.log (p : ℝ) else 0 := by
      simp only [← Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ 8 * ∑ v ∈ T, Real.log (reducedDenominator G v : ℝ) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by norm_num)
    _ ≤ 8 * (m : ℝ) * Real.log (2 * (m : ℝ)) := by
      nlinarith [hsumlog]

/-- 论文第 653 行的计数工具：不超过实数 `B` 的不同素数至多有 `B` 个。 -/
theorem prime_finset_card_le_real (S : Finset ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hprime : ∀ p ∈ S, p.Prime) (hbound : ∀ p ∈ S, (p : ℝ) ≤ B) :
    (S.card : ℝ) ≤ B := by
  classical
  have hsub : S ⊆ Finset.Icc 1 ⌊B⌋₊ := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hprime p hp).one_lt.le,
      (Nat.le_floor_iff hB).2 (hbound p hp)⟩
  have hcard : S.card ≤ ⌊B⌋₊ := by
    have h := Finset.card_le_card hsub
    simpa [Nat.card_Icc] using h
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hB)

/-- 论文第 653 行：将素数按 `p≤8e`、`8e<p≤√m`、`p>√m`
分组，由逐项赋值上界及分摊上界推出 `log Q` 的常数 `8e+9√m`。 -/
theorem log_bound_from_local_and_charge (Q m e : ℕ)
    (_hQpos : 0 < Q) (hmpos : 0 < m)
    (hlocal : ∀ p ∈ Q.primeFactors,
      (Q.factorization p : ℝ) * Real.log (p : ℝ) ≤
        Real.log (2 * (m : ℝ)))
    (hcharge : ∑ p ∈ Q.primeFactors.filter (fun p => 8 * e < p),
      (p : ℝ) * (Q.factorization p : ℝ) * Real.log (p : ℝ) ≤
        8 * (m : ℝ) * Real.log (2 * (m : ℝ))) :
    Real.log (Q : ℝ) ≤
      (8 * (e : ℝ) + 9 * Real.sqrt (m : ℝ)) * Real.log (2 * (m : ℝ)) := by
  classical
  let L := Real.log (2 * (m : ℝ))
  let F : ℕ → ℝ := fun p => (Q.factorization p : ℝ) * Real.log (p : ℝ)
  let W : ℕ → ℝ := fun p => (p : ℝ) * F p
  let P := Q.primeFactors
  let Psmall := P.filter (fun p => p ≤ 8 * e)
  let Pbig := P.filter (fun p => 8 * e < p)
  let Pmid : Finset ℕ := Pbig.filter (fun (p : ℕ) => (p : ℝ) ≤ Real.sqrt (m : ℝ))
  let Plarge : Finset ℕ := Pbig.filter (fun (p : ℕ) => Real.sqrt (m : ℝ) < (p : ℝ))
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
  have hsqrt : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt hmR.le
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    linarith
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hsmallcard : (Psmall.card : ℝ) ≤ 8 * (e : ℝ) := by
    apply prime_finset_card_le_real Psmall (8 * (e : ℝ)) (by positivity)
    · intro p hp
      exact hPprime p (Finset.mem_filter.mp hp).1
    · intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2
  have hmidcard : (Pmid.card : ℝ) ≤ Real.sqrt (m : ℝ) := by
    apply prime_finset_card_le_real Pmid (Real.sqrt (m : ℝ)) hsqrt.le
    · intro p hp
      exact hPprime p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  have hsmall : (∑ p ∈ Psmall, F p) ≤ 8 * (e : ℝ) * L := by
    calc
      (∑ p ∈ Psmall, F p) ≤ ∑ p ∈ Psmall, L := by
        apply Finset.sum_le_sum
        intro p hp
        exact hlocal p (Finset.mem_filter.mp hp).1
      _ = (Psmall.card : ℝ) * L := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 8 * (e : ℝ) * L := mul_le_mul_of_nonneg_right hsmallcard hL
  have hmid : (∑ p ∈ Pmid, F p) ≤ Real.sqrt (m : ℝ) * L := by
    calc
      (∑ p ∈ Pmid, F p) ≤ ∑ p ∈ Pmid, L := by
        apply Finset.sum_le_sum
        intro p hp
        exact hlocal p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      _ = (Pmid.card : ℝ) * L := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt (m : ℝ) * L := mul_le_mul_of_nonneg_right hmidcard hL
  have hlargeScaled : Real.sqrt (m : ℝ) * (∑ p ∈ Plarge, F p) ≤
      ∑ p ∈ Pbig, W p := by
    calc
      Real.sqrt (m : ℝ) * (∑ p ∈ Plarge, F p) =
          ∑ p ∈ Plarge, Real.sqrt (m : ℝ) * F p := by
        rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ Plarge, W p := by
        apply Finset.sum_le_sum
        intro p hp
        have hplarge : Real.sqrt (m : ℝ) ≤ (p : ℝ) :=
          (Finset.mem_filter.mp hp).2.le
        have hFnonneg : 0 ≤ F p := by
          dsimp [F]
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
        exact mul_le_mul_of_nonneg_right hplarge hFnonneg
      _ ≤ ∑ p ∈ Pbig, W p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp _
        dsimp [W, F]
        positivity
  have hlarge : (∑ p ∈ Plarge, F p) ≤ 8 * Real.sqrt (m : ℝ) * L := by
    have hscaled : Real.sqrt (m : ℝ) * (∑ p ∈ Plarge, F p) ≤
        Real.sqrt (m : ℝ) * (8 * Real.sqrt (m : ℝ) * L) := by
      calc
        _ ≤ ∑ p ∈ Pbig, W p := hlargeScaled
        _ ≤ 8 * (m : ℝ) * L := by
          simpa only [Pbig, P, W, F, L, mul_assoc] using hcharge
        _ = Real.sqrt (m : ℝ) * (8 * Real.sqrt (m : ℝ) * L) := by
          calc
            _ = 8 * (Real.sqrt (m : ℝ) ^ 2) * L := by rw [hsqrt_sq]
            _ = _ := by ring
    exact (mul_le_mul_iff_of_pos_left hsqrt).mp hscaled
  have hsplit : (∑ p ∈ P, F p) =
      (∑ p ∈ Psmall, F p) + (∑ p ∈ Pmid, F p) +
        (∑ p ∈ Plarge, F p) := by
    have hfirst := Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ 8 * e) F
    have hsecond := Finset.sum_filter_add_sum_filter_not Pbig
      (fun p => (p : ℝ) ≤ Real.sqrt (m : ℝ)) F
    have hnot : P.filter (fun p => ¬ p ≤ 8 * e) = Pbig := by
      ext p
      simp [Pbig, not_le]
    rw [hnot] at hfirst
    change (∑ p ∈ Psmall, F p) + (∑ p ∈ Pbig, F p) = ∑ p ∈ P, F p at hfirst
    have hnot2 : Pbig.filter (fun (p : ℕ) => ¬ (p : ℝ) ≤ Real.sqrt (m : ℝ)) = Plarge := by
      ext p
      simp [Plarge, not_le]
    rw [hnot2] at hsecond
    change (∑ p ∈ Pmid, F p) + (∑ p ∈ Plarge, F p) = ∑ p ∈ Pbig, F p at hsecond
    rw [← hfirst, ← hsecond]
    ring
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ P, F p) ≤
      (8 * (e : ℝ) + 9 * Real.sqrt (m : ℝ)) * L
  rw [hsplit]
  nlinarith [hsmall, hmid, hlarge]

/-- 论文第 619–653 行，引理 `lem:denominator` 中的共同分母结论。
在论文的有限正整数速度、不可约 Bohr 覆盖、`gcd(V)=1`、核心 `C`、
例外集合 `E`、`2mδ=1+ε` 与非例外分母 `q_v≤2m` 的条件下，
`Q=lcm_{v∈V\E} q_v` 整除 `G`，且满足式 `eq:Qbound`。
`V\E=∅`、`E=∅`、`Q=1` 均包含在命题中。 -/
theorem denominator_divides_and_log_bound
    (V C E : Finset ℕ) (m e G : ℕ) (δ ε : ℝ)
    (hm : m = V.card) (he : e = E.card)
    (hVpos : ∀ v ∈ V, 0 < v)
    (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2)
    (hirr : IrreducibleCover V δ) (hgcd : V.gcd id = 1)
    (hCV : C ⊆ V) (hCcard : (m : ℝ) / 2 ≤ (C.card : ℝ))
    (hGpos : 0 < G) (hGdiv : ∀ v ∈ C, G ∣ v)
    (_hEV : E ⊆ V) (_hEC : Disjoint E C)
    (hδeq : 2 * (m : ℝ) * δ = 1 + ε)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hqbound : ∀ v ∈ V \ E, reducedDenominator G v ≤ 2 * m) :
    commonDenominator V E G ∣ G ∧
      Real.log (commonDenominator V E G : ℝ) ≤
        (8 * (e : ℝ) + 9 * Real.sqrt (m : ℝ)) *
          Real.log (2 * (m : ℝ)) := by
  classical
  have hmpos : 0 < m := by
    obtain ⟨v, hv, _⟩ := hirr.1 0
    exact hm ▸ Finset.card_pos.mpr ⟨v, hv⟩
  obtain ⟨hQpos, hQdvdG⟩ := commonDenominator_pos_dvd V E G hGpos
  have hlocal : ∀ p ∈ (commonDenominator V E G).primeFactors,
      ((commonDenominator V E G).factorization p : ℝ) * Real.log (p : ℝ) ≤
        Real.log (2 * (m : ℝ)) := by
    intro p hpQ
    exact commonDenominator_localValuation_bound V E m G p hmpos hGpos
      hqbound (Nat.prime_of_mem_primeFactors hpQ)
      (Nat.dvd_of_mem_primeFactors hpQ)
  have hlarge : ∀ p ∈ largePrimeFactors V E e G,
      (p : ℝ) / 8 ≤ ((survivingNondivisible V E p).card : ℝ) ∧
      ∀ v ∈ survivingNondivisible V E p,
        (reducedDenominator G v).factorization p =
          (commonDenominator V E G).factorization p := by
    intro p hpLarge
    have hpQmem : p ∈ (commonDenominator V E G).primeFactors :=
      (Finset.mem_filter.mp hpLarge).1
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpQmem
    have hpQ : p ∣ commonDenominator V E G :=
      Nat.dvd_of_mem_primeFactors hpQmem
    have hpG : p ∣ G := hpQ.trans hQdvdG
    have hr := (prime_size_and_nondivisible_lower V C m G p δ ε hm hVpos
      hδ0 hδhalf hirr hgcd hCV hCcard hGpos hGdiv hp hpG hδeq hε0 hεhalf).2
    exact large_prime_survivors_full_valuation V E e G p he hGpos hp hpQ
      (Finset.mem_filter.mp hpLarge).2 hr
  have hcharge := finite_prime_charge_bound V E m e G hm hmpos hGpos hqbound hlarge
  refine ⟨hQdvdG, ?_⟩
  exact log_bound_from_local_and_charge (commonDenominator V E G) m e
    hQpos hmpos hlocal hcharge

end LonelyRunner

#print axioms LonelyRunner.denominator_divides_and_log_bound
