module

public import SolvedProblems.FactorPackingModel
public import SolvedProblems.FactorProfiles
public import SolvedProblems.FactorMerge

@[expose] public section

namespace PackingFactorization

def seamMark {n} (i : Fin n) := 3*i.val+1

theorem seamMark_inj {n} : Function.Injective (@seamMark n) := by
  intro i j eq; unfold seamMark at eq; exact Fin.ext (by omega)

theorem hue_mark {n} (i : Fin n) : hue (seamMark i) = 1 := Fin.ext (by simp [hue,seamMark])

theorem hue_fresh (K r n i) : hue (fresh K r n i) = (if r then 2 else 0) := by
  apply Fin.ext
  cases r <;> simp [fresh,hue]

theorem hue_cases (x) : hue x=0 ∨ hue x=1 ∨ hue x=2 := by
  have := (hue x).isLt
  rcases (show (hue x).val=0 ∨ (hue x).val=1 ∨ (hue x).val=2 by omega)
    with h|h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

private theorem frameProp {K} {p : Pattern K} (r) (P : Nat → Prop)
    (freshOk : ∀ n i, P (fresh K r n i)) (w : List (Overlap p)) (v : Fin K → Nat)
    (n) (prev : ∀ i, P (v i)) : ∀ f ∈ framesAux r v n w, ∀ i, P (f i) := by
  induction w generalizing v n with
  | nil => simpa [framesAux] using prev
  | cons a w ih =>
    intro f mem i
    rcases List.mem_cons.mp mem with eq|mem
    · subst f; exact prev i
    · apply ih _ _ _ f mem i
      intro j
      unfold attach
      split
      · exact prev _
      · exact freshOk _ _

theorem sideTag {K} {p : Pattern K} {r} {m : Overlap p} {w xs}
    (hp : Packs (orders r m w) xs) {x} (hx : x∈xs) :
    hue x = (if r then 2 else 0) ∨ ∃ i : Fin m.size, seamMark i = x := by
  obtain ⟨ww,mem,occ⟩ := (hp.2.1 x).mp hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (show ww ∈ (frames r m w).map (rankOrder p) from mem)
  obtain ⟨i,rfl⟩ := (rank_mem p v x).mp occ
  apply frameProp r (fun t => hue t = (if r then 2 else 0) ∨ ∃ i : Fin m.size, seamMark i=t)
    (fun n t => Or.inl (hue_fresh K r n t)) w (initial r m) 1 _ v hv i
  intro t
  unfold initial
  split
  · exact Or.inr ⟨_,rfl⟩
  · exact Or.inl (hue_fresh ..)

theorem side_has_mark {K} {p : Pattern K} {r} {m : Overlap p} {w xs}
    (hp : Packs (orders r m w) xs) (i : Fin m.size) : seamMark i ∈ xs := by
  have mem : initial r m ∈ frames r m w := by cases w <;> simp [frames,framesAux]
  simpa only [initial_shared,seamMark] using nonempty_support mem (slot m (!r) i) hp

theorem side_mark_iff {K} {p : Pattern K} {r} {m : Overlap p} {w xs}
    (hp : Packs (orders r m w) xs) {x} (hx : x∈xs) :
    hue x=1 ↔ ∃ i : Fin m.size, seamMark i = x := by
  constructor
  · intro h
    rcases sideTag hp hx with cols|ok
    · cases r <;> simp_all
    · exact ok
  · rintro ⟨i,rfl⟩; exact hue_mark i

noncomputable def seamMass (n : Nat) (P : Nat → Prop) : Nat := by
  classical
  exact (Finset.univ.filter (fun i : Fin n => P (seamMark i))).card

theorem prefix_mass {K} {p : Pattern K} {r} {m : Overlap p} {w xs}
    (hp : Packs (orders r m w) xs) {u : List Nat} (nd : u.Nodup) (sub : u ⊆ xs) :
    (PackingFactor.shared hue u).length = seamMass m.size (fun x => x ∈ u) := by
  classical
  let s := Finset.univ.filter (fun i : Fin m.size => seamMark i ∈ u)
  have eq : (PackingFactor.shared hue u).toFinset = s.image seamMark := by
    ext x
    simp only [s,PackingFactor.shared,List.mem_toFinset,List.mem_filter,beq_iff_eq,
      Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨mem,col⟩
      obtain ⟨i,rfl⟩ := (side_mark_iff hp (sub mem)).mp col
      exact ⟨i,mem,rfl⟩
    · rintro ⟨i,mem,rfl⟩
      exact ⟨mem,hue_mark i⟩
  have ndu : (PackingFactor.shared hue u).Nodup := nd.filter _
  rw [←List.toFinset_card_of_nodup ndu,eq,Finset.card_image_of_injective _ seamMark_inj]
  unfold seamMass
  congr 1
  ext i
  simp [s]

theorem initial_mass {K} {p : Pattern K} {r} {m : Overlap p} {P c}
    (aligned : Aligned p P (initial r m) c) :
    seamMass m.size P = anchorCount m (!r) c := by
  classical
  unfold seamMass anchorCount
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have z := aligned (slot m (!r) i)
  rw [initial_shared] at z
  exact z

end PackingFactorization
