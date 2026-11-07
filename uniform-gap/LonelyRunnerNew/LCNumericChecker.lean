import LonelyRunnerNew.LCNumericCell

noncomputable section
open scoped BigOperators
namespace LonelyRunnerNew.LCNumeric

def GridValid (boxes : List Box) : Prop :=
  boxes.length=256 ∧ (∀ b ∈ boxes,b.Valid) ∧
  ∀ i ∈ Finset.range 256,(boxes[i]!).lo=(i:ℚ)/512 ∧ (boxes[i]!).hi=((i:ℚ)+1)/512

theorem grid_box {boxes : List Box} (hg : GridValid boxes) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    ∃ b ∈ boxes,(b.lo:ℝ) ≤ u ∧ u ≤ (b.hi:ℝ) := by
  obtain ⟨i,hi,hl,hh⟩ := grid_cover hu hu1
  have hilen : i < boxes.length := by rw [hg.1]; exact hi
  have hmem : boxes[i]! ∈ boxes := by
    simpa only [getElem!_pos boxes i hilen] using List.getElem_mem hilen
  have hshape := hg.2.2 i (Finset.mem_range.mpr hi)
  have he1 := congrArg (fun r : ℚ => (r:ℝ)) hshape.1
  have he2 := congrArg (fun r : ℚ => (r:ℝ)) hshape.2
  push_cast at he1 he2
  exact ⟨boxes[i]!,hmem,by rwa [he1],by rwa [he2]⟩

theorem CellStep.grid_sound (c : Scale) (d : CellStep) (boxes : List Box)
    (hc : c.Valid) (hd : d.Valid c) (hg : GridValid boxes)
    (hacc : ∀ b ∈ boxes,d.Accepts b) {lam u : ℝ}
    (hl0 : 0 ≤ lam) (hlU : lam ≤ (c.lambdaUpper:ℝ)) (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    LCDirection.B d.S lam u ≤ (d.bUpper:ℝ) ∧
      (LCDirection.B d.S lam u)^6*LCDirection.h0 u ≤ (d.eUpper:ℝ) := by
  obtain ⟨b,hb,hlo,hhi⟩ := grid_box hg hu hu1
  exact d.box_sound c b hc hd (hg.2.1 b hb) (hacc b hb) hl0 hlU hlo hhi

theorem CellStep.apply_endpoint (c : Scale) (d : CellStep) (boxes : List Box)
    (hc : c.Valid) (hd : d.Valid c) (hg : GridValid boxes) (hacc : ∀ b ∈ boxes,d.Accepts b)
    {lam z u E : ℝ} (hl0 : 0 ≤ lam) (hlU : lam ≤ (c.lambdaUpper:ℝ))
    (hu : 0 ≤ u) (hu1 : u ≤ 1/2) (hz : 0 < z) (hzS : z ≤ (d.S:ℝ))
    (hit : LCDirection.normalizedInequality lam z u) (hE : E ≤ z^(3/2:ℝ)*LCDirection.h0 u) :
    z ≤ (d.nextS:ℝ) ∧ E ≤ lam^6*(d.eUpper:ℝ) := by
  have hL : (c.lambdaUpper:ℝ) ≤ 1/3 := by
    have h : (3:ℚ)*c.lambdaUpper ≤ 1 := by linarith [hc.2.1]
    have hR : (3:ℝ)*(c.lambdaUpper:ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  have hS : (d.S:ℝ) ≤ 1/8 := by
    have h : (8:ℚ)*d.S ≤ 1 := by linarith [hd.2.1]
    have hR : (8:ℝ)*(d.S:ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  have hgB := d.grid_sound c boxes hc hd hg hacc hl0 hlU hu hu1
  have hB0 : 0 ≤ LCDirection.B d.S lam u := by
    unfold LCDirection.B
    have hl1 : lam < 1 := by linarith
    have hl4 : lam^4 < 1 := by simpa using pow_lt_pow_left₀ hl1 hl0 (by decide : (4:ℕ)≠0)
    have hDen := LCDirection.denominator_pos (LCDirection.h_nonneg (lam := lam) hu (by linarith))
      (LCDirection.h_upper hl0 (hlU.trans hL) hu (by linarith)) (show (0:ℝ) < d.S by exact_mod_cast hd.1) hS
    have hf0 : 0 ≤ LCDirection.f u := add_nonneg (Real.rpow_nonneg hu _) (Real.rpow_nonneg (by linarith) _)
    apply div_nonneg _ hDen.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by positivity) _)) hf0) (LCDirection.C_pos (by linarith)).le
  have hzb := LCDirection.endpoint_bound hl0 (hlU.trans hL) hu (by linarith) hz hzS hS hit
  have heb := LCDirection.endpoint_exception_bound hl0 (hlU.trans hL) hu (by linarith) hz hzS hS hit hE
  refine ⟨?_,?_⟩
  · calc
      z ≤ lam^4*(LCDirection.B d.S lam u)^4 := hzb
      _ ≤ (c.lambdaUpper:ℝ)^4*(d.bUpper:ℝ)^4 :=
        mul_le_mul (pow_le_pow_left₀ hl0 hlU 4) (pow_le_pow_left₀ hB0 hgB.1 4) (by positivity) (by positivity)
      _ ≤ (d.nextS:ℝ) := by exact_mod_cast hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · calc
      E ≤ lam^6*(LCDirection.B d.S lam u)^6*LCDirection.h0 u := heb
      _ ≤ lam^6*(d.eUpper:ℝ) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgB.2 (pow_nonneg hl0 6)

/-- Only strict improvements are taken before the last row. All rows are
checked for the SAME fixed z,u,lambda, hence for the same actual center. -/
def Chain (initial : ℚ) : List CellStep → Prop
  | [] => False
  | [d] => d.S=initial
  | d::e::rest => d.S=initial ∧ d.nextS < d.S ∧ Chain d.nextS (e::rest)

instance (initial : ℚ) (steps : List CellStep) : Decidable (Chain initial steps) := by
  induction steps generalizing initial with
  | nil => exact isFalse id
  | cons d rest ih =>
    cases rest with
    | nil => exact inferInstanceAs (Decidable (d.S=initial))
    | cons e rest =>
      change Decidable (d.S=initial ∧ d.nextS < d.S ∧ Chain d.nextS (e::rest))
      letI : Decidable (Chain d.nextS (e::rest)) := ih d.nextS
      infer_instance

def lastCoefficient : List CellStep → ℚ
  | [] => 0
  | [d] => d.eUpper
  | _::e::rest => lastCoefficient (e::rest)

theorem chain_sound (c : Scale) (boxes : List Box) (hc : c.Valid) (hg : GridValid boxes)
    (steps : List CellStep) (initial : ℚ) (hchain : Chain initial steps)
    (hv : ∀ d ∈ steps,d.Valid c) (ha : ∀ d ∈ steps,∀ b ∈ boxes,d.Accepts b)
    {lam z u E : ℝ} (hl0 : 0 ≤ lam) (hlU : lam ≤ (c.lambdaUpper:ℝ))
    (hu : 0 ≤ u) (hu1 : u ≤ 1/2) (hz : 0 < z) (hzS : z ≤ (initial:ℝ))
    (hit : LCDirection.normalizedInequality lam z u) (hE : E ≤ z^(3/2:ℝ)*LCDirection.h0 u) :
    E ≤ lam^6*(lastCoefficient steps:ℝ) := by
  induction steps generalizing initial with
  | nil => exact False.elim hchain
  | cons d rest ih =>
    have hd : d ∈ d::rest := List.mem_cons_self
    cases rest with
    | nil =>
      have heq : d.S=initial := hchain
      exact (d.apply_endpoint c boxes hc (hv d hd) hg (ha d hd) hl0 hlU hu hu1 hz
        (by simpa only [heq] using hzS) hit hE).2
    | cons e rest =>
      obtain ⟨heq,hlt,hnext⟩ := hchain
      have hstep := d.apply_endpoint c boxes hc (hv d hd) hg (ha d hd) hl0 hlU hu hu1 hz
        (by simpa only [heq] using hzS) hit hE
      exact ih d.nextS hnext (fun x hx => hv x (List.mem_cons_of_mem _ hx))
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) hstep.1

structure Band where
  lower : ℕ
  scale : Scale
  steps : List CellStep
  deriving Inhabited,DecidableEq

def Band.Valid (boxes : List Box) (b : Band) : Prop :=
  0 < b.lower ∧ b.scale.Valid ∧ 0 < b.scale.lambdaUpper ∧
  1 ≤ b.scale.lambdaUpper^201*(b.lower:ℚ)^50 ∧
  Chain (121/1000) b.steps ∧ (∀ d ∈ b.steps,d.Valid b.scale) ∧
  (∀ d ∈ b.steps,∀ box ∈ boxes,d.Accepts box)
instance (boxes : List Box) (b : Band) : Decidable (b.Valid boxes) := by
  unfold Band.Valid; infer_instance

theorem Band.lambda_bound (b : Band) (boxes : List Box) (hb : b.Valid boxes)
    {p : ℕ} (hp : b.lower ≤ p) : (p:ℝ)^(-1/q) ≤ (b.scale.lambdaUpper:ℝ) := by
  have hP : (0:ℝ) < b.lower := by exact_mod_cast hb.1
  have hL : (0:ℝ) < b.scale.lambdaUpper := by exact_mod_cast hb.2.2.1
  have hroot := negative_power_upper hP hL 50 201 (by decide)
    (by exact_mod_cast hb.2.2.2.1)
  have hh := Real.rpow_le_rpow_of_nonpos (y := (p:ℝ)) hP (by exact_mod_cast hp)
    (by norm_num : (-(50:ℝ)/201) ≤ 0)
  norm_num only [Nat.cast_ofNat] at hroot
  have heq : (-1/q:ℝ)=-(50:ℝ)/201 := by norm_num [q]
  rw [heq]
  exact hh.trans (by simpa only [neg_div] using hroot)

theorem Band.sound (b : Band) (boxes : List Box) (hg : GridValid boxes) (hb : b.Valid boxes)
    {p : ℕ} (hp : Nat.Prime p) (hpB : b.lower ≤ p) {z u E : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1/2) (hz : 0 < z) (hzS : z ≤ (121/1000:ℝ))
    (hit : LCDirection.normalizedInequality ((p:ℝ)^(-1/q)) z u)
    (hE : E ≤ z^(3/2:ℝ)*LCDirection.h0 u) :
    E ≤ (p:ℝ)^(-(100:ℝ)/67)*(lastCoefficient b.steps:ℝ) := by
  have hh := chain_sound b.scale boxes hb.2.1 hg b.steps (121/1000) hb.2.2.2.2.1
    hb.2.2.2.2.2.1 hb.2.2.2.2.2.2
    (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _) (b.lambda_bound boxes hb hpB)
    hu hu1 hz (by norm_num; exact hzS) hit hE
  rw [TaggedState.prime_lambda_power p hp 6] at hh
  norm_num [q] at hh ⊢
  exact hh

end LonelyRunnerNew.LCNumeric
