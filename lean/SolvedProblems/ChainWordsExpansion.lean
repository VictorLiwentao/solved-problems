module

public import SolvedProblems.ChainWordsMonomials

@[expose] public section

namespace ChainWords

noncomputable def extensions (α : Type*) [Fintype α] [PartialOrder α] (n : ℕ) :
    Finset (List.Vector α n) := by
  classical exact Finset.univ.filter fun l => IsExtension Set.univ l.val

noncomputable def admissible {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ) (s : List Bool) :
    Finset (List.Vector α (s.length+1)) := by
  classical exact (extensions α _).filter fun l => Allows s (descWord f l.val)

theorem mem_extensions {α : Type*} [Fintype α] [PartialOrder α] {n} (l : List.Vector α n) :
    l ∈ extensions α n ↔ IsExtension Set.univ l.val := by classical simp [extensions]

theorem mem_admissible {α : Type*} [Fintype α] [PartialOrder α] (f : α → ℕ) {s} (l : List.Vector α (s.length+1)) :
    l ∈ admissible f s ↔ IsExtension Set.univ l.val ∧ Allows s (descWord f l.val) := by
  classical simp [admissible,mem_extensions]

theorem perm_univ {α : Type*} [Fintype α] [PartialOrder α] {l : List α} (he : IsExtension Set.univ l) :
    l.Perm (Finset.univ : Finset α).toList := by
  apply (List.perm_ext_iff_of_nodup he.1 (Finset.nodup_toList _)).mpr
  intro x
  simp [he.2.1 x]

private theorem sorted_vertices {α : Type*} [Fintype α] (f : α → ℕ) (hf : Function.Injective f)
    (t : α → ℕ) : ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l) ∧ l.Pairwise (fun x y => key f t x ≤ key f t y) := by
  classical
  let _ := LinearOrder.lift' (key f t) (key_injective hf t)
  exact ⟨Finset.univ.sort, Finset.sort_nodup .., by simp, Finset.pairwise_sort ..⟩

/-- Standardization identifies the order-preserving assignments with any fixed
monomial with the extensions whose descents are permitted at its level changes. -/
theorem fundamental_expansion {α : Type*} [Fintype α] [PartialOrder α] (f : α ↪ ℕ) (s : List Bool) :
    monomialCoefficient f (levels 0 s) = (admissible f s).card := by
  classical
  let C := Colorings f (levels 0 s)
  let E := ↥(admissible f s)
  let R (c : C) (e : E) := e.1.1.map c.1 = levels 0 s
  have toExtension (c : C) : ∃ e : E, R c e := by
    obtain ⟨l,hn,hm,hk⟩ := sorted_vertices f f.injective c.1
    have he : IsExtension Set.univ l := ⟨hn, fun x => by simp [hm x],key_sorted_extension c.2.1 hk⟩
    have hperm := ((perm_univ he).map c.1).trans c.2.2
    have sorted : (l.map c.1).Pairwise (· ≤ ·) := List.pairwise_map.mpr (hk.imp fun h =>
      (Prod.Lex.toLex_le_toLex.mp h).elim (fun h => h.le) (fun h => h.1.le))
    have eq := hperm.eq_of_pairwise' sorted (levels_sorted 0 s)
    have hl : l.length = s.length+1 := by simpa [levels_length] using congrArg List.length eq
    let v : List.Vector α (s.length+1) := ⟨l,hl⟩
    exact ⟨⟨v,(mem_admissible f v).mpr ⟨he,(keyed_iff f c.val l s 0 eq).mp hk⟩⟩,eq⟩
  have toColoring (e : E) : ∃ c : C, R c e := by
    obtain ⟨he,ha⟩ := (mem_admissible f e.val).mp e.property
    obtain ⟨t,ht⟩ := map_exists _ he.1 (levels 0 s) (e.1.2.trans (levels_length 0 s).symm)
    have hk := (keyed_iff f t e.val.val s 0 ht).mpr ha
    refine ⟨⟨t,partition_of_key_sorted f.injective he hk,?_⟩,ht⟩
    rw [← ht]
    exact (perm_univ he).symm.map _
  have uniq (c : C) (e e' : E) (h : R c e) (h' : R c e') : e = e' := by
    obtain ⟨he,ha⟩ := (mem_admissible f e.val).mp e.property
    obtain ⟨he',ha'⟩ := (mem_admissible f e'.val).mp e'.property
    have hk := (keyed_iff f c.val e.val.val s 0 h).mpr ha
    have hk' := (keyed_iff f c.val e'.val.val s 0 h').mpr ha'
    apply Subtype.ext
    apply Subtype.ext
    exact List.Perm.eq_of_pairwise (fun _ _ _ _ hxy hyx => key_injective f.injective c.val (le_antisymm hxy hyx))
      hk hk' ((perm_univ he).trans (perm_univ he').symm)
  let F (c : C) : E := (toExtension c).choose
  have hF (c : C) : R c (F c) := (toExtension c).choose_spec
  have inj : Function.Injective F := by
    intro c d h
    have eq := hF c
    rw [h] at eq
    have maps := List.map_inj_left.mp (eq.trans (hF d).symm)
    exact Subtype.ext (funext fun x => maps x (((mem_admissible f (F d).val).mp (F d).property).1.2.1 x |>.mpr trivial))
  have sur : Function.Surjective F := by
    intro e
    obtain ⟨c,hc⟩ := toColoring e
    exact ⟨c,uniq c (F c) e (hF c) hc⟩
  calc
    monomialCoefficient f (levels 0 s) = Nat.card E := Nat.card_congr (Equiv.ofBijective F ⟨inj,sur⟩)
    _ = _ := by simp [E,Nat.card_eq_fintype_card]

end ChainWords
