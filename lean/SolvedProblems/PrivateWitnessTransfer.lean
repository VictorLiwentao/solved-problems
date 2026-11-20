module

public import SolvedProblems.PrivateWitnessIID
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecificLimits.Basic

public section
namespace PrivateWitness
open scoped NNReal ENNReal
open Set Filter

/-- A full-support discrete law on any nonempty language, by normalizing geometric weights. -/
theorem supported {L : Set Nat} (hne : L.Nonempty) : ∃ p : Law, p.support = L := by
  classical
  let w (n : Nat) := if n ∈ L then ((1/2 : ℝ≥0∞)^n) else 0
  have nonzero : ∑' n, w n ≠ 0 := by
    obtain ⟨x,hx⟩ := hne
    intro hz
    have h := (ENNReal.tsum_eq_zero.mp hz) x
    simp [w,hx] at h
  have finite : ∑' n, w n ≠ ∞ := by
    have h : ∑' n, w n ≤ ∑' n : Nat, (1/2 : ℝ≥0∞)^n :=
      ENNReal.tsum_le_tsum (fun n => by by_cases hn : n ∈ L <;> simp [w,hn])
    exact ne_of_lt (lt_of_le_of_lt h (tsum_geometric_lt_top.mpr (by norm_num)))
  let p : Law := ⟨fun x => w x * (∑' i, w i)⁻¹, by
    rw [ENNReal.tsum_mul_right,ENNReal.mul_inv_cancel nonzero finite]⟩
  refine ⟨p,?_⟩
  ext x
  change w x * (∑' i, w i)⁻¹ ≠ 0 ↔ x ∈ L
  by_cases h : x ∈ L
  · exact ⟨fun _ => h, fun _ => mul_ne_zero (by simp [w,h]) (ENNReal.inv_ne_zero.mpr finite)⟩
  · simp [w,h]

private theorem partition (p : Law) (F : Finset Nat) : mass p F + mass p (F:Set Nat)ᶜ = 1 := by
  classical
  unfold mass
  rw [← ENNReal.tsum_add, ← p.total]
  exact tsum_congr (fun x => by by_cases hx : x ∈ F <;> simp [hx])

/-- Keep all old atoms in F, using the remaining mass for an entire new target. -/
private noncomputable def replaceTail (p q : Law) (F : Finset Nat) : Law := by
  classical
  let t := mass p (F:Set Nat)ᶜ
  refine ⟨fun x => (if x ∈ F then p x else 0) + t*q x, ?_⟩
  rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,q.total,mul_one]
  convert partition p F using 1
  unfold mass
  congr 1
  exact tsum_congr fun x => by by_cases hx : x ∈ F <;> simp [hx]

private theorem replace_apply (p q : Law) (F : Finset Nat) (x : Nat) :
    (replaceTail p q F) x = (if x ∈ F then p x else 0) + mass p (F:Set Nat)ᶜ*q x := by
  classical
  by_cases h : x ∈ F <;> simp [replaceTail,h]

private noncomputable def avg (p : Law) (g : Nat → ℝ≥0∞) := ∑' x, p x * g x

private theorem singleTransfer (p q : Law) (F : Finset Nat) (k : ℝ≥0∞) (g : Nat → ℝ≥0∞)
    (priv : ∀ x y, g x ≤ k*g y) :
    avg (replaceTail p q F) g ≤ (1 + mass p (F:Set Nat)ᶜ*k)*avg p g := by
  classical
  let t := mass p (F:Set Nat)ᶜ
  have each (x) : g x ≤ k*avg p g := by
    calc
      _ = ∑' y, p y * g x := by rw [ENNReal.tsum_mul_right,p.total,one_mul]
      _ ≤ ∑' y, p y * (k*g y) := ENNReal.tsum_le_tsum (fun y => mul_le_mul_right (priv x y) _)
      _ = _ := by unfold avg; rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun y => mul_left_comm ..)
  have hQ : avg q g ≤ k * avg p g := by
    calc
      _ ≤ ∑' y, q y * (k*avg p g) := ENNReal.tsum_le_tsum fun y => mul_le_mul_right (each y) _
      _ = _ := by rw [ENNReal.tsum_mul_right,q.total,one_mul]
  have trunc : (∑' y, (if y ∈ F then p y else 0)*g y) ≤ avg p g :=
    ENNReal.tsum_le_tsum (fun y => by by_cases hy : y ∈ F <;> simp [hy])
  unfold avg at *
  simp only [replace_apply]
  simp only [add_mul,ENNReal.tsum_add,one_mul,mul_assoc,ENNReal.tsum_mul_left]
  exact add_le_add trunc (mul_le_mul_right hQ _)

private theorem transfer {G : Rule} {k : ℝ≥0} (priv : Private G k) (p q : Law) (F : Finset Nat)
    (E : Set Nat) (n : Nat) (h : List Nat) :
    iid (replaceTail p q F) (fun h => mass (G h) E) n h ≤
      (1+mass p (F:Set Nat)ᶜ*(k:ℝ≥0∞))^n * iid p (fun h => mass (G h) E) n h := by
  let d := 1+mass p (F:Set Nat)ᶜ*(k:ℝ≥0∞)
  let f := fun h => mass (G h) E
  induction n generalizing h with
  | zero => simp [iid]
  | succ n ih =>
    let g := fun x => iid p f n (x::h)
    let q' := replaceTail p q F
    calc
      _ ≤ ∑' x, q' x * (d^n*g x) := ENNReal.tsum_le_tsum fun x => mul_le_mul_right (ih _) _
      _ = d^n * avg q' g := by unfold avg; rw [← ENNReal.tsum_mul_left]; exact tsum_congr (fun _ => mul_left_comm ..)
      _ ≤ d^n * (d * avg p g) := mul_le_mul_right (singleTransfer p q F k g (fun a b => iid_private priv p E n a b h)) _
      _ = _ := by change d^n*(d*avg p g) = d^(n+1)*avg p g; rw [pow_succ,mul_assoc]

private theorem tail_lt (p : Law) {δ : ℝ≥0} (hd : 0 < δ) :
    ∃ F : Finset Nat, mass p (F:Set Nat)ᶜ < (δ:ℝ≥0∞) := by
  classical
  have h := ENNReal.tendsto_tsum_compl_atTop_zero (p.total ▸ ENNReal.one_ne_top)
  obtain ⟨F,hF⟩ := (h.eventually_lt_const (show 0 < (δ:ℝ≥0∞) by exact_mod_cast hd)).exists
  refine ⟨F,?_⟩
  let S : Set Nat := (F:Set Nat)ᶜ
  change (∑' b : S, p ↑b) < (δ:ℝ≥0∞) at hF
  rw [tsum_subtype S (fun x => p x)] at hF
  exact hF

/-- Transfer an exponential output-event bound to a law whose support contains the
new language, with only finitely many atoms outside it. The loss per coordinate can
be made arbitrarily small by keeping sufficiently many old atoms. -/
theorem transferSupport {G : Rule} {k : ℝ≥0} (priv : Private G k) (p : Law)
    (infinite : p.support.Infinite) (L E : Set Nat) (nonempty : L.Nonempty)
    (small : Exponential (output G p E)) :
    ∃ q : Law, L ⊆ q.support ∧ (q.support \ L).Finite ∧ Exponential (output G q E) := by
  classical
  obtain ⟨c,r,hr,H⟩ := small
  obtain ⟨q,hq⟩ := supported nonempty
  have hrr : (r:ℝ) < 1 := by exact_mod_cast hr
  obtain ⟨v,hv,room⟩ := exists_pos_mul_lt (show 0 < 1-(r:ℝ) by linarith) ((k:ℝ)*(r:ℝ))
  let δ : ℝ≥0 := ⟨v,hv.le⟩
  obtain ⟨F,hF⟩ := tail_lt p (show 0 < δ from hv)
  let t := mass p (F:Set Nat)ᶜ
  have tpos : t ≠ 0 := by
    obtain ⟨x,hx,away⟩ := infinite.exists_notMem_finset F
    apply ne_of_gt
    calc
      0 < p x := pos_iff_ne_zero.mpr hx
      _ = mass p {x} := (mass_singleton ..).symm
      _ ≤ t := mass_mono _ (by simpa using away)
  refine ⟨replaceTail p q F,?_,?_,?_⟩
  · intro x hx
    change (replaceTail p q F) x ≠ 0
    rw [replace_apply]
    have hz : q x ≠ 0 := (show x ∈ q.support from hq ▸ hx)
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero tpos hz)) le_add_self)
  · apply F.finite_toSet.subset
    rintro x ⟨hx,notL⟩
    by_contra away
    have zero : q x = 0 := not_ne_iff.mp (show x ∉ q.support from hq ▸ notL)
    change (replaceTail p q F) x ≠ 0 at hx
    rw [replace_apply] at hx
    exact hx (by simp_all)
  · let b := 1+δ*k
    have rate : b*r < 1 := by
      change ((1+v*(k:ℝ))*(r:ℝ)) < 1
      linarith only [room]
    refine ⟨c,b*r,rate,fun n => ?_⟩
    have le : 1 + t*(k:ℝ≥0∞) ≤ (b:ℝ≥0∞) := by
      simp only [b,ENNReal.coe_add,ENNReal.coe_one,ENNReal.coe_mul]
      exact add_le_add_right (mul_le_mul_left hF.le _) _
    calc
      _ ≤ (1+t*(k:ℝ≥0∞))^n * output G p E n := transfer priv p q F E n []
      _ ≤ (b:ℝ≥0∞)^n * ((c:ℝ≥0∞)*(r:ℝ≥0∞)^n) := mul_le_mul' (pow_le_pow_left' le _) (H n)
      _ = _ := by simp only [ENNReal.coe_mul,mul_pow]; ac_rfl

end PrivateWitness
