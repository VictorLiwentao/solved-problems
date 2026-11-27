module

public import SolvedProblems.UniversalWadgeThreshold
public import Mathlib.Topology.Separation.PerfectlyNormal
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Logic.Encodable.Basic

@[expose] public section

namespace UniversalWadge

open Set
open scoped Classical Topology

def Reduces {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (S : Set X) (T : Set Y) : Prop :=
  ∃ f : X → Y, Continuous f ∧ f ⁻¹' T = S

def allRows (I : Ideal) : Set Tests := {a | ∀ j,a j∈cantors I}

theorem reduces_trans {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {S : Set X} {T : Set Y} {R : Set Z} (f : Reduces S T) (g : Reduces T R) : Reduces S R := by
  obtain ⟨a,ca,ea⟩ := f;obtain ⟨b,cb,eb⟩ := g
  exact ⟨b ∘ a,cb.comp ca,by rw [preimage_comp,eb,ea]⟩

theorem rows_to_circle (I : Ideal) : Reduces (allRows I) (locus I character) :=
  ⟨code,productReduction.1,Set.ext (productReduction.2 I)⟩

theorem one_to_rows (I : Ideal) : Reduces (cantors I) (allRows I) :=
  ⟨fun x _ => x,continuous_pi (fun _ => continuous_id),by ext x; simp [allRows]⟩

/-- Countably many independent continuous reductions to the same ideal can be
combined into a single reduction to its countable power, including an empty family. -/
theorem combine {X J : Type} [TopologicalSpace X] [Countable J] (I : Ideal) (S : J → Set X)
    (h : ∀ j, Reduces (S j) (cantors I)) : Reduces (⋂ j,S j) (allRows I) := by
  let _ := Encodable.ofCountable J
  choose f cf eq using h
  let g (x : X) (n : ℕ) : Cantor := match Encodable.decode (α := J) n with
    | some j => f j x
    | none => fun _ => false
  have emp : (fun _ : ℕ => false)∈cantors I := by simpa [cantors,support] using I.finite ∅ finite_empty
  refine ⟨g,continuous_pi (fun n => ?_),Set.ext (fun x => ?_)⟩
  · dsimp [g];cases Encodable.decode (α := J) n with | some j => exact cf j | none => exact continuous_const
  · change (∀ n, g x n ∈ cantors I) ↔ _
    constructor
    · intro hx;apply mem_iInter.mpr;intro j
      have := hx (Encodable.encode j)
      rw [← eq j];simpa only [g,Encodable.encodek,Set.mem_preimage] using this
    · intro hs n;dsimp [g];cases Encodable.decode (α := J) n with
      | none => exact emp
      | some j => exact (Set.ext_iff.mp (eq j) x).mpr (mem_iInter.mp hs j)

theorem combine_rows {X J : Type} [TopologicalSpace X] [Countable J] (I : Ideal) (S : J → Set X)
    (h : ∀ j, Reduces (S j) (allRows I)) : Reduces (⋂ j,S j) (allRows I) := by
  choose f cf eq using h
  let P (p : J×ℕ) := (fun x => f p.1 x p.2) ⁻¹' cantors I
  have flat : (⋂ p, P p) = ⋂ j, S j := by
    ext x;simp only [P,mem_iInter,mem_preimage,Prod.forall]
    exact forall_congr' fun j => Set.ext_iff.mp (eq j) x
  rw [← flat];apply combine;intro p
  exact ⟨_,(continuous_apply _).comp (cf _),rfl⟩

theorem lower_classes_suffice {X : Type} [TopologicalSpace X] [PerfectlyNormalSpace X] (I : Ideal) {α : Ordinal.{0}}
    (gt : 1<α) (hard : ∀ β<α, ∀ S : Set X, AdditiveClass X β S → Reduces S (cantors I))
    {S : Set X} (h : MultiplicativeClass X α S) : Reduces S (locus I character) := by
  have aux {P : Set X} {γ} (p : AdditiveClass X γ P) : γ=α → Reduces Pᶜ (allRows I) := by
    induction p with
    | @basic γ U pos ho =>
      intro _
      obtain ⟨V,hV,eq⟩ := ho.isClosed_compl.isGδ.eq_iInter_nat
      rw [eq];exact combine I V (fun j => hard 1 gt _ (.basic zero_lt_one (hV j)))
    | unions pos u hs ih =>
      intro e;rw [compl_iUnion];exact combine_rows I _ (fun i => ih i e)
    | lowerCompl low hs _ =>
      rintro rfl;rw [compl_compl];exact reduces_trans (hard _ low _ hs) (one_to_rows I)
  apply reduces_trans _ (rows_to_circle I)
  simpa only [compl_compl] using aux h rfl

end UniversalWadge
