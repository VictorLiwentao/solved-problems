module

public import SolvedProblems.AtomicGrowthBlocks
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

open List

namespace AtomicGrowth

theorem products_card {Q : ℕ → Finset Word} {L : ℝ} (hL : 0<L)
    (hw : ∀ n, (∑ i : Fin n, ((Q (i.val+1)).card : ℝ)/L^(i.val+1)) ≤ 1) (n : ℕ) :
    ((products Q n).card : ℝ) ≤ L^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [products]
    | succ n =>
      let t (i : Fin (n+1)) := ((Q (i.val+1)) ×ˢ products Q (n-i.val)).image (fun z => direct z.1 z.2)
      have hsum : (products Q (n+1)).card ≤ ∑ i : Fin (n+1), (Q (i.val+1)).card * (products Q (n-i.val)).card := by
        rw [products]
        exact (Finset.card_biUnion_le (s:=Finset.univ) (t:=t)).trans (Finset.sum_le_sum fun i _ =>
          Finset.card_image_le.trans (Finset.card_product _ _).le)
      apply (show ((products Q (n+1)).card : ℝ) ≤ ∑ i : Fin (n+1), ((Q (i.val+1)).card:ℝ) * (products Q (n-i.val)).card by
        exact_mod_cast hsum).trans
      calc _ ≤ ∑ i : Fin (n+1), ((Q (i.val+1)).card:ℝ)*L^(n-i.val) := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (ih _ (by omega)) (Nat.cast_nonneg _)
           _ = (∑ i : Fin (n+1), ((Q (i.val+1)).card:ℝ)/L^(i.val+1))*L^(n+1) := by
             rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _
             rw [show L^(n+1)=L^(i.val+1)*L^(n-i.val) by rw [←pow_add]; congr 1; omega]
             field_simp
           _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right (hw (n+1)) (pow_nonneg hL.le (n+1))

theorem joint_valley {s : ℕ → List Word} (hp : ∀ i, ∀ w ∈ s i, IsPerm w) (i m : ℕ)
    (Q : ℕ → Finset Word) (hq : ∀ j ≥ i, ∀ b ∈ s j, ∀ z, z.Sublist b → z.length≤m → z ≠ [] → standard z ∈ Q z.length)
    (L : ℝ) (hL : 1≤L) (hw : ∀ n, (∑ k : Fin n, ((Q (k.val+1)).card : ℝ)/L^(k.val+1))≤1) :
    ((level (jointClass s) m).card : ℝ) ≤ 2^(blocks (stages s i)).length * L^m := by
  classical
  let pre := blocks (stages s i)
  let choices := pre.sublists.toFinset
  let after (u : Word) := (products Q (m-u.length)).image fun v => direct (standard u) v
  have incl : level (jointClass s) m ⊆ choices.biUnion after := by
    intro w hwm
    obtain ⟨_,hlen,j,hwj⟩ := mem_level.mp hwm
    have hsub : Contains w (blocks (stages s (i+j))) := by
      rw [Nat.add_comm,stages_add]
      exact prefix_contains hwj
    obtain ⟨z,hz,rfl⟩ := hsub
    rw [stages_add,blocks_append] at hz
    obtain ⟨u,v,rfl,hu,hv⟩ := List.sublist_append_iff.mp hz
    obtain ⟨v,hv',rfl⟩ := (List.sublist_map_iff (f:=(pre.length+·))).mp hv
    change u.Sublist pre at hu
    have hm : u.length+v.length=m := by simpa using hlen
    let bs := (List.range j).flatMap fun k => s (i+k)
    have hper : ∀ t ∈ bs, IsPerm t := by
      rintro t ht
      obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp ht
      exact hp _ _ hk
    have hlocal : ∀ t ∈ bs, ∀ z, z.Sublist t → z.length≤m → z ≠ [] → standard z ∈ Q z.length := by
      intro t ht
      obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp ht
      exact hq (i+k) (by omega) t hk
    have hvs := products_suffix bs hper hlocal v hv' (by omega)
    have sep : ∀ x ∈ u, ∀ y ∈ v.map (pre.length+·), x<y := by
      rintro x hx y hy
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hy
      have hl := List.mem_range.mp ((stages_perm hp i).mem_iff.mp (hu.subset hx))
      change x<pre.length at hl
      omega
    change standard (u ++ v.map (pre.length+·)) ∈ _
    rw [standard_append _ _ sep,standard_shift]
    exact Finset.mem_biUnion.mpr ⟨u,List.mem_toFinset.mpr (List.mem_sublists.mpr hu),
      Finset.mem_image.mpr ⟨standard v,(show m-u.length=v.length by omega) ▸ hvs,rfl⟩⟩
  have hc := (Finset.card_le_card incl).trans (Finset.card_biUnion_le (s:=choices) (t:=after))
  apply (show ((level (jointClass s) m).card : ℝ) ≤ ∑ u ∈ choices, ((after u).card : ℝ) by exact_mod_cast hc).trans
  calc _ ≤ ∑ _u ∈ choices, L^m := by
         apply Finset.sum_le_sum
         intro u _
         have hh : ((after u).card : ℝ) ≤ ((products Q (m-u.length)).card : ℝ) := by exact_mod_cast Finset.card_image_le
         exact hh.trans ((products_card (by linarith) hw _).trans (pow_le_pow_right₀ hL (Nat.sub_le ..)))
       _ = (choices.card : ℝ)*L^m := by simp
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
         exact_mod_cast (List.toFinset_card_le pre.sublists).trans (List.length_sublists pre).le

end AtomicGrowth
