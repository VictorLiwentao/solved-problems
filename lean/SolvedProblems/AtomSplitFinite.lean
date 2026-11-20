module

public import SolvedProblems.AtomSplitGeneration
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

namespace AtomSplit
open Set Equiv

theorem homogeneous {V : Set ℕ} (hv : V.Infinite) (Q : List (Set ℕ)) :
    ∃ D ⊆ V, D.Infinite ∧ ∀ p : Perm ℕ, p ∈ Inside D → Preserves Q p := by
  induction Q generalizing V with
  | nil => exact ⟨V,Subset.rfl,hv,by simp [Preserves]⟩
  | cons S Q ih =>
    have choice : ∃ W ⊆ V, W.Infinite ∧ (W ⊆ S ∨ ∀ w ∈ W, w ∉ S) := by
      by_cases h : (V ∩ S).Infinite
      · exact ⟨V ∩ S,inter_subset_left,h,.inl inter_subset_right⟩
      · refine ⟨V \ S,sdiff_subset,?_,.inr (fun _ h => h.2)⟩
        exact (hv.sdiff (Classical.not_not.mp h)).mono (by grind)
    obtain ⟨W,hw,wi,flat⟩ := choice
    obtain ⟨D,hd,di,keep⟩ := ih wi
    refine ⟨D,hd.trans hw,di,fun p hp E hE x => ?_⟩
    rcases List.mem_cons.mp hE with rfl|hE
    · by_cases h : x ∈ D
      · have h' := (inside_preserves hp x).mpr h
        rcases flat with flat|flat
        · exact iff_of_true (flat (hd h')) (flat (hd h))
        · exact iff_of_false (flat _ (hd h')) (flat _ (hd h))
      · rw [hp x h]
    · exact keep p hp _ hE x

/-- A permutation confined to part of a partition cell belongs to the stabilizer. -/
theorem inside_in_stabilizer {k} {block : ℕ → Fin k} {B : Set ℕ} {i : Fin k}
    (hb : ∀ x ∈ B, block x = i) : Inside B ≤ stabilizer block := by
  intro p hp x
  by_cases hx : x ∈ B
  · exact (hb _ ((inside_preserves hp x).mpr hx)).trans (hb _ hx).symm
  · rw [hp x hx]

abbrev localAction {k} {block : ℕ → Fin k} {X : Type u} (act : stabilizer block →* Perm X)
    {B : Set ℕ} (h : Inside B ≤ stabilizer block) : Inside B →* Perm X :=
  act.comp (Subgroup.inclusion h)

private theorem finite_support {B : Set ℕ} {X : Type u} (act : Inside B →* Perm X)
    (localPts : ∀ x, ∃ Q : List (Set ℕ), ∀ g : Inside B, Preserves Q g.val → act g x = x)
    {E : Set X} (fin : E.Finite) :
    ∃ Q : List (Set ℕ), ∀ g : Inside B, Preserves Q g.val → ∀ x ∈ E, act g x = x := by
  induction E, fin using Set.Finite.induction_on with
  | empty => exact ⟨[],by simp⟩
  | @insert a t _ _ ih =>
    obtain ⟨Q,hQ⟩ := localPts a
    obtain ⟨R,hR⟩ := ih
    refine ⟨Q++R,fun g fix x hx => ?_⟩
    rcases Set.mem_insert_iff.mp hx with rfl|hin
    · exact hQ g (fun D hd => fix D (List.mem_append.mpr (.inl hd)))
    · exact hR g (fun D hd => fix D (List.mem_append.mpr (.inr hd))) _ hin

/-- An invariant finite set of supported objects is fixed pointwise by the
symmetric group of an infinite cell. Intersect the finitely many local supports
and normally generate with permutations confined to a single infinite subcell. -/
theorem finite_fixed {B : Set ℕ} (bi : B.Infinite) {X : Type u} (act : Inside B →* Perm X)
    (localPts : ∀ x, ∃ Q : List (Set ℕ), ∀ g : Inside B, Preserves Q g.val → act g x = x)
    {E : Set X} (fin : E.Finite) (stable : ∀ g : Inside B, ∀ x, act g x ∈ E ↔ x ∈ E) :
    ∀ g : Inside B, ∀ x ∈ E, act g x = x := by
  obtain ⟨Q,support⟩ := finite_support act localPts fin
  obtain ⟨V,hV,vi,vr⟩ := split_region bi
  obtain ⟨D,hD,di,flat⟩ := homogeneous vi Q
  let rho : Inside B →* Perm E := {
    toFun := fun g => (act g).subtypePerm (stable g)
    map_one' := by ext x; simp
    map_mul' := by intro g h; apply Equiv.ext; intro x; apply Subtype.ext; change act (g*h) x.val = act g (act h x.val); rw [map_mul,Perm.mul_apply] }
  have kills (v : Inside B) (hc : v.val ∈ Inside D) : v ∈ rho.ker := by
    apply MonoidHom.mem_ker.mpr
    exact Equiv.ext fun x => Subtype.ext (support v (flat _ hc) x x.property)
  intro g x hx
  have all := normal_generation (hD.trans hV) di (vr.mono fun y hy => ⟨hy.1,fun hd => hy.2 (hD hd)⟩)
    rho.ker inferInstance kills g
  exact congrArg (fun f : Perm E => (f ⟨x,hx⟩).val) (MonoidHom.mem_ker.mp all)

theorem local_pts {k} {block : ℕ → Fin k} {X : Type u} {act : stabilizer block →* Perm X}
    (hs : LocallySupported act) {B : Set ℕ} (h : Inside B ≤ stabilizer block) (x : X) :
    ∃ Q : List (Set ℕ), ∀ g : Inside B, Preserves Q g.val → localAction act h g x = x := by
  obtain ⟨Q,hQ⟩ := hs x
  exact ⟨Q,fun g hg => hQ _ hg⟩

end AtomSplit
