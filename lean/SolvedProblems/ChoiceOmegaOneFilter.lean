module

public import SolvedProblems.ChoiceOmegaOneCompare
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Filter

variable {I : Type u} {P : Type v} [Group P] {V : Type w} [MulAction (I → P) V]

/-- The stabilizer of a point gives a filter of sufficient supports. Splitting
a tuple into its coordinates inside and outside a set proves intersection closure. -/
def supportFilter (x : V) : Filter I where
  sets := {T | PointSupport (P := P) T x}
  univ_sets := by
    intro g hg; have eq : g = 1 := funext (fun i => hg i trivial)
    rw [eq,one_smul]
  sets_of_superset h sub := fun g hg => h g (fun i hi => hg i (sub hi))
  inter_sets {A B} hA hB := by
    classical
    intro g hg
    let f (i : I) := if i ∈ A then (1 : P) else g i
    let k (i : I) := if i ∈ A then g i else 1
    have e : g = f*k := by funext i; by_cases hi : i∈A <;> simp [f,k,hi]
    have hk : ∀ i ∈ B, k i = 1 := by
      intro i hi; by_cases ha : i∈A
      · simpa [k,ha] using hg i ⟨ha,hi⟩
      · simp [k,ha]
    rw [e,mul_smul,hB k hk,hA f (by intro i hi; simp [f,hi])]

/-- The clopen slice of all ultrafilter extensions of F containing A. -/
def extSlice (F : Filter I) (A : Set I) : Set (Ultrafilter I) := {U | U.toFilter ≤ F ∧ A ∈ U}

private theorem refine_slice (F : Filter I) (A : Set I) (many : (extSlice F A).Infinite) :
    ∃ B C : Set I, B ⊆ A ∧ C ⊆ A ∧ Disjoint B C ∧ (extSlice F B).Infinite ∧ (extSlice F C).Nonempty := by
  classical
  obtain ⟨U,hU⟩ := many.nonempty
  obtain ⟨V,hV,neq⟩ := many.exists_notMem_finset {U}
  have ne : U ≠ V := fun e => neq (by simp [e])
  have sep : ∃ t : Set I, t ∈ U ∧ t ∉ V := by
    by_contra! h
    apply ne
    exact (Ultrafilter.eq_of_le (show V.toFilter ≤ U.toFilter from fun _ ht => h _ ht)).symm
  obtain ⟨t,ut,vt⟩ := sep
  let B := A ∩ t
  let C := A ∩ tᶜ
  have ub : U ∈ extSlice F B := ⟨hU.1,inter_mem hU.2 ut⟩
  have vc : V ∈ extSlice F C := ⟨hV.1,inter_mem hV.2 (Ultrafilter.compl_mem_iff_notMem.mpr vt)⟩
  have dis : Disjoint B C := Set.disjoint_left.2 (fun _ hb hc => hc.2 hb.2)
  have cover : extSlice F A ⊆ extSlice F B ∪ extSlice F C := by
    intro W h
    rcases W.mem_or_compl_mem t with p | p
    · exact Or.inl ⟨h.1,inter_mem h.2 p⟩
    · exact Or.inr ⟨h.1,inter_mem h.2 p⟩
  rcases Set.infinite_union.mp (many.mono cover) with inf | inf
  · exact ⟨B,C,inter_subset_left,inter_subset_left,dis,inf,⟨V,vc⟩⟩
  · exact ⟨C,B,inter_subset_left,inter_subset_left,dis.symm,inf,⟨U,ub⟩⟩

/-- A filter with no countably infinite disjoint sequence of positive sets is
the intersection of finitely many ultrafilters. This includes the improper
filter, represented by the empty family. -/
theorem finite_descriptors (F : Filter I)
    (noSeq : ¬ ∃ s : ℕ → Set I, Pairwise (fun i j => Disjoint (s i) (s j)) ∧ ∀ n, (s n)ᶜ ∉ F) :
    ∃ family : Finset (Ultrafilter I), ∀ T : Set I, T ∈ F ↔ ∀ U ∈ family, T ∈ U := by
  classical
  let all := {U : Ultrafilter I | U.toFilter ≤ F}
  have finite : all.Finite := by
    by_contra inf
    let State := {A : Set I // (extSlice F A).Infinite}
    have init : (extSlice F univ).Infinite := by
      apply Set.Infinite.mono (s := all) _ inf
      exact fun U hU => ⟨hU,Filter.univ_mem⟩
    choose next out subNext subOut dis infinite pos using fun a : State => refine_slice F a.val a.property
    let state : ℕ → State := Nat.rec ⟨univ,init⟩ (fun _ a => ⟨next a,infinite a⟩)
    have down (n : ℕ) : (state (n+1)).val ⊆ (state n).val := subNext _
    have nested {n m : ℕ} (h : n ≤ m) : (state m).val ⊆ (state n).val := by
      induction h with
      | refl => exact Subset.rfl
      | step _ ih => exact (down _).trans ih
    have apart {n m : ℕ} (h : n < m) : Disjoint (out (state n)) (out (state m)) :=
      (dis _).symm.mono_right ((subOut _).trans (nested (show n+1 ≤ m from h)))
    apply noSeq
    refine ⟨fun n => out (state n),fun n m h => (lt_or_gt_of_ne h).elim (fun l => apart l) (fun l => (apart l).symm),?_⟩
    intro n bad
    obtain ⟨U,hU,mem⟩ := pos (state n)
    exact (Ultrafilter.compl_mem_iff_notMem.mp (hU bad)) mem
  refine ⟨finite.toFinset,fun T => ?_⟩
  simpa [all,Set.Finite.mem_toFinset] using (Filter.mem_iff_ultrafilter (f := F) (s := T))

end ChoiceOmegaOne
