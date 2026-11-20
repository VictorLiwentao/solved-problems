module

public import SolvedProblems.PrivateWitnessModel
import Mathlib.Analysis.SpecificLimits.Basic

public section
namespace PrivateWitness
open scoped NNReal ENNReal

@[expose] noncomputable def output (G : Rule) (p : Law) (E : Set Nat) (n : Nat) :=
  iid p (fun h => mass (G h) E) n []

theorem mass_mono (p : Law) {E F : Set Nat} (sub : E ⊆ F) : mass p E ≤ mass p F := by
  classical
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ E
  · simp [hx,sub hx]
  · simp [hx]

@[simp] theorem mass_univ (p : Law) : mass p Set.univ = 1 := by simp [mass,p.total]
@[simp] theorem mass_empty (p : Law) : mass p ∅ = 0 := by simp [mass]
@[simp] theorem mass_singleton (p : Law) (x : Nat) : mass p {x} = p x := by simp [mass]

theorem mass_union (p : Law) (E F : Set Nat) : mass p (E ∪ F) ≤ mass p E + mass p F := by
  classical
  unfold mass
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp [he,hf]

theorem mass_le_one (p : Law) (E : Set Nat) : mass p E ≤ 1 :=
  (mass_mono p (Set.subset_univ E)).trans_eq (mass_univ p)

theorem iid_const (p : Law) (c : ℝ≥0∞) (n h) : iid p (fun _ => c) n h = c := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [iid,ih,ENNReal.tsum_mul_right,p.total,one_mul]

theorem iid_add (p : Law) (f g : List Nat → ℝ≥0∞) (n h) :
    iid p (fun x => f x + g x) n h = iid p f n h + iid p g n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [iid,ih,mul_add,ENNReal.tsum_add]

theorem iid_scale (p : Law) (f : List Nat → ℝ≥0∞) (c) (n h) :
    iid p (fun x => c*f x) n h = c*iid p f n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [iid,ih]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun _ => mul_left_comm ..

theorem iid_context (p : Law) {f g : List Nat → ℝ≥0∞} {u v : List Nat}
    (le : ∀ z : List Nat, f (z++u) ≤ g (z++v)) (n) : iid p f n u ≤ iid p g n v := by
  induction n generalizing u v with
  | zero => exact le []
  | succ n ih =>
    apply ENNReal.tsum_le_tsum
    intro x
    exact mul_le_mul_right (ih (fun z => by simpa [List.append_assoc] using le (z++[x]))) _

theorem iid_mono (p : Law) {f g : List Nat → ℝ≥0∞} (le : ∀ x, f x ≤ g x) (n h) :
    iid p f n h ≤ iid p g n h := iid_context p (fun _ => le _) n

theorem iid_private {G : Rule} {k : ℝ≥0} (priv : Private G k) (p : Law) (E : Set Nat)
    (n : Nat) (a b : Nat) (v : List Nat) :
    iid p (fun h => mass (G h) E) n (a::v) ≤ (k:ℝ≥0∞)*iid p (fun h => mass (G h) E) n (b::v) := by
  rw [← iid_scale]
  exact iid_context p (fun u => priv u v a b E) _

theorem exponential_mono {f g : Nat → ℝ≥0∞} (h : ∀ n, f n ≤ g n) :
    Exponential g → Exponential f := by
  rintro ⟨c,r,hr,H⟩
  exact ⟨c,r,hr,fun n => (h n).trans (H n)⟩

theorem exponential_add {f g : Nat → ℝ≥0∞} (hf : Exponential f) (hg : Exponential g) :
    Exponential (fun n => f n + g n) := by
  obtain ⟨c,r,hr,H⟩ := hf
  obtain ⟨d,s,hs,J⟩ := hg
  refine ⟨c+d,max r s,max_lt hr hs,fun n => ?_⟩
  simp only [ENNReal.coe_add,add_mul]
  apply add_le_add
  · exact (H n).trans (mul_le_mul_right (pow_le_pow_left' (ENNReal.coe_le_coe.mpr (le_max_left ..)) _) _)
  · exact (J n).trans (mul_le_mul_right (pow_le_pow_left' (ENNReal.coe_le_coe.mpr (le_max_right ..)) _) _)

theorem exp_union {G : Rule} {p : Law} {E F : Set Nat}
    (a : Exponential (output G p E)) (b : Exponential (output G p F)) :
    Exponential (output G p (E∪F)) := by
  apply exponential_mono _ (exponential_add a b)
  intro n
  unfold output
  rw [← iid_add]
  exact iid_mono _ (fun h => mass_union _ _ _) _ _

theorem exp_empty (G : Rule) (p : Law) : Exponential (output G p ∅) := by
  exact ⟨0,0,zero_lt_one,fun n => by simp [output,iid_const]⟩

theorem subevent {G : Rule} {p : Law} {E F : Set Nat} (h : E ⊆ F)
    (small : Exponential (output G p F)) : Exponential (output G p E) :=
  exponential_mono (fun n => iid_mono p (fun s => mass_mono (G s) h) n []) small

end PrivateWitness
