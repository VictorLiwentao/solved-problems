module

public import SolvedProblems.FactorWindows
public import Mathlib.Data.List.Permutation

@[expose] public section

namespace PackingFactorization

def hue (x : Nat) : Fin 3 := ⟨x%3,Nat.mod_lt _ (by decide)⟩

/-- Finite enumeration of all permutations of the physical union that realize every window. -/
noncomputable def packings (windows : List (List Nat)) : Finset (List Nat) := by
  classical
  exact (windows.flatten.toFinset.toList.permutations.toFinset).filter (Packs windows)

/-- The two physical sides are listed outwards from their common seam. The
left-hand word in the usual reading direction is the reverse of u. -/
def Factors {K} {p : Pattern K} (m : Overlap p) (u v : List (Overlap p)) :=
  let L := orders false m u
  let R := orders true m v
  (packings (L++R)).card = (packings L).card * (packings R).card

theorem mem_packings {ws xs} : xs ∈ packings ws ↔ Packs ws xs := by
  classical
  simp only [packings,Finset.mem_filter,List.mem_toFinset,List.mem_permutations]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  apply (List.perm_ext_iff_of_nodup h.1 (Finset.nodup_toList _)).mpr
  intro x
  simpa only [Finset.mem_toList,List.mem_toFinset,List.mem_flatten] using h.2.1 x

theorem rank_mem {K} (p : Pattern K) (v : Fin K → Nat) (x) :
    x ∈ rankOrder p v ↔ ∃ i, v i=x := by
  simp only [rankOrder,List.mem_ofFn]
  exact ⟨fun ⟨r,h⟩ => ⟨_,h⟩,fun ⟨i,h⟩ => ⟨p i,by simpa using h⟩⟩

theorem rank_nodup {K} (p : Pattern K) (v : Fin K → Nat) (inj : Function.Injective v) :
    (rankOrder p v).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  simp only [rankOrder,List.getElem_ofFn] at eq
  exact congrArg Fin.val (p.symm.injective (inj eq))

theorem pack_sublist {ws xs} (h : Packs ws xs) {w} (hw : w∈ws) : w.Sublist xs := h.2.2 _ hw

theorem filter_window {xs w : List Nat} (h : w.Sublist xs) (nd : xs.Nodup) :
    xs.filter (fun x => x ∈ w) = w := by
  have sub : w.Sublist (xs.filter (fun x => x ∈ w)) := by
    have self : w.filter (fun x => x ∈ w) = w := List.filter_eq_self.mpr (by simp)
    rw [←self] at h ⊢
    simpa only [self] using h.filter (fun x => x ∈ w)
  apply (sub.eq_of_length_le _).symm
  apply (nd.filter _).length_le_of_subset
  intro x hx
  simpa using (List.mem_filter.mp hx).2

theorem nonempty_support {K} {p : Pattern K} {r : Bool} {m : Overlap p} {w : List (Overlap p)} {v : Fin K → Nat} (hv : v∈frames r m w)
    (i : Fin K) {xs} (pack : Packs (orders r m w) xs) : v i ∈ xs :=
  (pack.2.1 _).mpr ⟨_,List.mem_map.mpr ⟨v,hv,rfl⟩,(rank_mem p v _).mpr ⟨i,rfl⟩⟩

end PackingFactorization
