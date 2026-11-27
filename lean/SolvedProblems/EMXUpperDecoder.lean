module

public import SolvedProblems.EMXUpperCycle
import SolvedProblems.EMXCounting
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Positivity

@[expose] public section

namespace EMX

open scoped Classical

def project (j : ℕ) (x : Point) : Cell j :=
  if h : x.1 = j then h ▸ x.2 else (0,0)

theorem project_mk (j) (x : Cell j) : project j ⟨j,x⟩ = x := by simp [project]

noncomputable def restore : List Point → Hyp
  | [] => baseline
  | x::xs =>
    let j := x.1
    let c := project j x
    if xs = [] then ⟨j, omittedRow j (cycle Finset.univ c.1)⟩
    else let holes := grow (List.map (project j) (x::xs))
         if h : holes.card = width j then ⟨j,⟨holes,h⟩⟩ else baseline

noncomputable def decoder {d : ℕ} (_ : Fin 1) (w : Message Point d) : Hyp := restore (List.ofFn w.2)

theorem restore_one {j : ℕ} (x : Cell j) :
    restore [Sigma.mk j x] = ⟨j,omittedRow j (cycle Finset.univ x.1)⟩ := by
  simp [restore,project_mk]

theorem restore_many {j : ℕ} {w : List (Cell j)} (hle : 2 ≤ w.length)
    (hsize : (grow w).card = width j) :
    restore (w.map (Sigma.mk j)) = ⟨j,⟨grow w,hsize⟩⟩ := by
  cases w with
  | nil => simp at hle
  | cons x w =>
    have hw : w ≠ [] := by intro eq; simp [eq] at hle
    simp [restore, List.map_map, Function.comp_def, project_mk, hw, hsize]

theorem choose_anchors {j : ℕ} (S : Finset (Cell j)) (ne : S.Nonempty)
    (realizable : ∃ h : Holes j, S ⊆ h.valᶜ) :
    ∃ w : List (Cell j), (∀ x ∈ w, x ∈ S) ∧
      (w.length = 1 ∨ (w.length = width j ∧ 2^width j ≤ S.card)) ∧
      ∀ x ∈ S, Sigma.mk j x ∈ support (restore (w.map (Sigma.mk j))) := by
  let touched := S.image Prod.fst
  have hne : touched.Nonempty := ne.image _
  by_cases full : touched = Finset.univ
  · obtain ⟨h,hh⟩ := realizable
    have enough : width j ≤ Sᶜ.card := by
      apply h.property.ge.trans
      exact Finset.card_le_card (fun x hx => Finset.mem_compl.mpr (fun hxS => Finset.mem_compl.mp (hh hxS) hx))
    obtain ⟨w,hw,inside,count,sub⟩ := encode_holes S ne (width j) enough
    have hcard : 2^width j ≤ S.card := by
      have hc := Finset.card_image_le (s := S) (f := Prod.fst)
      change touched.card ≤ _ at hc
      simpa [full,Row] using hc
    refine ⟨w,inside,Or.inr ⟨hw,hcard⟩, ?_⟩
    intro x hx
    rw [restore_many (by rw [hw]; simp [width]) count]
    apply Finset.mem_map.mpr
    exact ⟨x, Finset.mem_compl.mpr (fun bad => Finset.mem_compl.mp (sub bad) hx), rfl⟩
  · have gap : ((Finset.univ : Finset (Row j)) \ touched).Nonempty := by
      by_contra! hg
      apply full
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hn
      have hx : i ∈ Finset.univ \ touched := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩
      rw [hg] at hx
      exact Finset.notMem_empty _ hx
    obtain ⟨i,hi,hnext⟩ := escapes hne (Finset.subset_univ _) gap
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    refine ⟨[x], by simpa, Or.inl rfl, ?_⟩
    intro y hy
    rw [List.map_cons, List.map_nil, restore_one]
    apply Finset.mem_map.mpr
    refine ⟨y, Finset.mem_compl.mpr ?_, rfl⟩
    intro hy'
    obtain ⟨k, _, eq⟩ := Finset.mem_image.mp hy'
    apply (Finset.mem_sdiff.mp hnext).2
    rw [show cycle Finset.univ x.1 = y.1 from congrArg Prod.fst eq]
    exact Finset.mem_image_of_mem _ hy

end EMX
