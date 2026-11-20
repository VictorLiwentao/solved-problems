module

public import SolvedProblems.AtomSplitRegions
import SolvedProblems.ClosureSupportPerm

public section

namespace AtomSplit
open Set Equiv

/-- The orbits of an involution have one or two elements. Their least elements
can therefore be split into two infinite sets, giving two invariant regions. -/
private theorem split_involution {B : Set ℕ} (inf : B.Infinite) (v : Inside B)
    (inv : ∀ x, v.val (v.val x) = x) :
    ∃ U : Set ℕ, U ⊆ B ∧ U.Infinite ∧ (B \ U).Infinite ∧ ∀ x, v.val x ∈ U ↔ x ∈ U := by
  let q (x : ℕ) := min x (v.val x)
  let C := q '' B
  have stable (x : ℕ) : q (v.val x) = q x := by simp [q,inv,min_comm]
  have cases' (x : ℕ) : q x = x ∨ q x = v.val x := min_choice _ _
  have cB : C ⊆ B := by
    rintro _ ⟨x,hx,rfl⟩
    rcases cases' x with e|e
    · simpa [e] using hx
    · rw [e]; exact (inside_preserves v.property x).mpr hx
  have rep : ∀ x ∈ C, q x = x := by
    rintro _ ⟨x,hx,rfl⟩
    rcases cases' x with e|e
    · rw [e]; exact e
    · rw [e,stable]; exact e
  have cinf : C.Infinite := by
    intro fin
    apply inf
    apply (fin.union (fin.image v.val)).subset
    intro x hx
    have hmem : q x ∈ C := ⟨x,hx,rfl⟩
    rcases cases' x with e|e
    · exact .inl (e ▸ hmem)
    · exact .inr ⟨q x,hmem,by rw [e,inv]⟩
  obtain ⟨T,hT,ti,rest⟩ := split_region cinf
  let U := B ∩ q ⁻¹' T
  refine ⟨U,inter_subset_left,ti.mono ?_,rest.mono ?_,fun x => ?_⟩
  · intro x hx
    exact ⟨cB (hT hx), show q x ∈ T by rwa [rep x (hT hx)]⟩
  · rintro x ⟨hc,ht⟩
    exact ⟨cB hc,fun h => ht (rep x hc ▸ h.2)⟩
  · change (v.val x ∈ B ∧ q (v.val x) ∈ T) ↔ (x ∈ B ∧ q x ∈ T)
    rw [inside_preserves v.property,stable]

private theorem factors_inside {B : Set ℕ} (g : Inside B) :
    ∃ a b : Inside B, (∀ x, a.val (a.val x) = x) ∧ (∀ x, b.val (b.val x) = x) ∧ g = a*b := by
  have gp : g.val ∈ ClosureSupport.stabilizer [B] := by
    intro S hs x
    obtain rfl := List.mem_singleton.mp hs
    exact inside_preserves g.property x
  obtain ⟨a,b,ha,hb,hab⟩ := ClosureSupport.factors [B] ⟨g.val,gp⟩
  have keep (p : ClosureSupport.stabilizer [B]) := fun x => p.property B (by simp) x
  let cut (p : ClosureSupport.stabilizer [B]) : Inside B :=
    ⟨cutPerm p.val B (keep p), cutPerm_outside _ _ _⟩
  have is_inv (p : ClosureSupport.stabilizer [B]) (hp : p*p=1) : ∀ x, (cut p).val ((cut p).val x) = x := by
    intro x
    change cutPerm p.val B _ (cutPerm p.val B _ x) = x
    by_cases hx : x ∈ B
    · rw [cutPerm_of_mem _ _ _ hx, cutPerm_of_mem _ _ _ ((keep p x).mpr hx)]
      exact congrArg (fun v : ClosureSupport.stabilizer [B] => v.val x) hp
    · rw [cutPerm_outside p.val B _ x hx, cutPerm_outside p.val B _ x hx]
  refine ⟨cut a,cut b,is_inv a ha,is_inv b hb, Subtype.ext (Equiv.ext fun x => ?_)⟩
  change g.val x = cutPerm a.val B _ (cutPerm b.val B _ x)
  by_cases hx : x ∈ B
  · rw [cutPerm_of_mem _ _ _ hx,cutPerm_of_mem _ _ _ ((keep b x).mpr hx)]
    exact congrArg (fun p : ClosureSupport.stabilizer [B] => p.val x) hab
  · rw [cutPerm_outside b.val B _ x hx,cutPerm_outside a.val B _ x hx,g.property x hx]

/-- Permutations confined to an infinite co-infinite subregion normally generate
the entire symmetric group on its countable block. -/
theorem normal_generation {D B : Set ℕ} (hd : D ⊆ B) (di : D.Infinite) (dr : (B \ D).Infinite)
    (K : Subgroup (Inside B)) (normal : K.Normal) (kills : ∀ v : Inside B, v.val ∈ Inside D → v ∈ K) :
    ∀ g : Inside B, g ∈ K := by
  have on_region {T : Set ℕ} (ht : T ⊆ B) (ti : T.Infinite) (tr : (B \ T).Infinite)
      (v : Inside B) (hv : v.val ∈ Inside T) : v ∈ K := by
    obtain ⟨p,moves⟩ := move_region ht hd ti di tr dr
    have cong : p*v*p⁻¹ ∈ K := kills _ (by
      intro x hx
      have ht : p.val.symm x ∉ T := fun bad => hx (by simpa using (moves (p.val.symm x)).mpr bad)
      change p.val (v.val (p.val.symm x)) = x
      rw [hv _ ht,Equiv.apply_symm_apply])
    simpa [mul_assoc] using normal.conj_mem (p*v*p⁻¹) cong p⁻¹
  have involution (v : Inside B) (inv : ∀ x, v.val (v.val x) = x) : v ∈ K := by
    obtain ⟨T,ht,ti,tr,keep⟩ := split_involution (di.mono hd) v inv
    let l : Inside B := ⟨cutPerm v.val T keep,cutPerm_same v.property⟩
    let r : Inside B := ⟨cutPerm v.val Tᶜ (fun x => not_congr (keep x)),cutPerm_same v.property⟩
    have hl : l ∈ K := on_region ht ti tr l (cutPerm_outside _ _ _)
    have hr : r ∈ K := on_region sdiff_subset tr (ti.mono (fun x hx => ⟨ht hx,fun h => h.2 hx⟩)) r (by
      intro x hx
      by_cases hB : x ∈ B
      · have hT : x ∈ T := Classical.byContradiction fun hn => hx ⟨hB,hn⟩
        exact cutPerm_outside v.val Tᶜ _ x (fun e => e hT)
      · exact r.property x hB)
    have eq : l*r=v := Subtype.ext (cutPerm_factor keep)
    exact eq ▸ K.mul_mem hl hr
  intro g
  obtain ⟨a,b,ha,hb,h⟩ := factors_inside g
  exact h ▸ K.mul_mem (involution a ha) (involution b hb)

end AtomSplit
