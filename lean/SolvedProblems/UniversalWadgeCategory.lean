module

public import SolvedProblems.UniversalWadgeHierarchy
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace UniversalWadge

open Set Filter TopologicalSpace
open scoped Classical Topology

abbrev Window {J : Type} [TopologicalSpace J] [SecondCountableTopology J] (U : Set J) :=
  {V : countableBasis J // V.val ⊆ U}

theorem nonmeagre_iff_window {J : Type} [TopologicalSpace J] [SecondCountableTopology J] [BaireSpace J]
    {S U : Set J} (Sbp : BaireMeasurableSet S) (Uo : IsOpen U) :
    ¬IsMeagre (S∩U) ↔ ∃ V : Window U, IsMeagre (Sᶜ ∩ V.val.val) := by
  constructor
  · intro nm
    obtain ⟨O,Oo,eq⟩ := Sbp.residualEq_isOpen
    obtain ⟨x,hx⟩ : (O∩U).Nonempty := by
      by_contra h;apply nm
      change ∀ᵇ t, t∉S∩U
      filter_upwards [eq] with t same
      exact fun ht => h ⟨t,same.mp ht.1,ht.2⟩
    obtain ⟨V,base,_,sub⟩ := (isBasis_countableBasis J).exists_subset_of_mem_open hx (Oo.inter Uo)
    refine ⟨⟨⟨V,base⟩,sub.trans inter_subset_right⟩,?_⟩
    change ∀ᵇ t, t∉Sᶜ∩V
    filter_upwards [eq] with t same
    exact fun ht => ht.1 (same.mpr (sub ht.2).1)
  · rintro ⟨V,me⟩ m
    have small : IsMeagre (S∩V.val.val) := m.mono (inter_subset_inter_right _ V.property)
    apply not_isMeagre_of_isOpen (isOpen_of_mem_countableBasis V.val.property) (nonempty_of_mem_countableBasis V.val.property)
    apply (small.union me).mono
    intro x hx;by_cases h : x∈S
    · exact Or.inl ⟨h,hx⟩
    · exact Or.inr ⟨h,hx⟩

def fiber {X J : Type} (E : Set (X×J)) (x : X) : Set J := (fun t => (x,t)) ⁻¹' E

def nonmeagreSection {X J : Type} [TopologicalSpace J] (E : Set (X×J)) (U : Set J) : Set X :=
  {x | ¬IsMeagre (fiber E x ∩ U)}

def comeagerSection {X J : Type} [TopologicalSpace J] (E : Set (X×J)) (U : Set J) : Set X :=
  (nonmeagreSection Eᶜ U)ᶜ

theorem section_open {X J : Type} [TopologicalSpace X] [TopologicalSpace J] [BaireSpace J]
    {E : Set (X×J)} (hE : IsOpen E) {U : Set J} (hU : IsOpen U) : IsOpen (nonmeagreSection E U) := by
  have eq : nonmeagreSection E U = Prod.fst '' (E ∩ Prod.snd ⁻¹' U) := by
    ext x; constructor
    · intro h
      have ne : (fiber E x ∩ U).Nonempty := by
        by_contra hn;exact h ((not_nonempty_iff_eq_empty.mp hn) ▸ IsMeagre.empty)
      obtain ⟨t,he,hu⟩ := ne;exact ⟨(x,t),⟨he,hu⟩,rfl⟩
    · rintro ⟨⟨x',t⟩,⟨he,hu⟩,rfl⟩
      exact not_isMeagre_of_isOpen ((hE.preimage (continuous_const.prodMk continuous_id)).inter hU) ⟨t,he,hu⟩
  rw [eq];exact isOpenMap_fst _ (hE.inter (hU.preimage continuous_snd))

theorem section_iUnion {X J I : Type} [TopologicalSpace J] [Countable I] (E : I → Set (X×J)) (U : Set J) :
    nonmeagreSection (⋃ i,E i) U = ⋃ i,nonmeagreSection (E i) U := by
  ext x; constructor
  · intro h;by_contra hn;apply h
    have me (i) : IsMeagre (fiber (E i) x ∩ U) := of_not_not (fun h => hn (mem_iUnion.mpr ⟨i,h⟩))
    simpa only [fiber,preimage_iUnion,iUnion_inter] using isMeagre_iUnion me
  · rintro hx;obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact fun h => hi (h.mono (inter_subset_inter_left _ (preimage_mono (subset_iUnion E i))))

/-- The nonmeager-section operation preserves every additive Borel class. -/
theorem section_additive {X J : Type} [TopologicalSpace X] [TopologicalSpace J]
    [SecondCountableTopology J] [BaireSpace J] {α E} (h : AdditiveClass (X×J) α E) :
    ∀ U : Set J, IsOpen U → AdditiveClass X α (nonmeagreSection E U) := by
  induction h with
  | basic pos ho => exact fun _ Uo => .basic pos (section_open ho Uo)
  | unions pos u _ ih => intro U ho;rw [section_iUnion];exact .unions pos _ (fun i => ih i U ho)
  | @lowerCompl α β E low h ih =>
    intro U ho
    have eq : nonmeagreSection Eᶜ U = ⋃ V : Window U,(nonmeagreSection E V.val.val)ᶜ := by
      ext x
      have bp := (additive_baire (additive_preimage (continuous_const.prodMk continuous_id) h)).compl (s := fiber E x)
      change (¬IsMeagre ((fiber E x)ᶜ∩U)) ↔ _
      rw [nonmeagre_iff_window bp ho]
      simp only [compl_compl,mem_iUnion,mem_compl_iff,nonmeagreSection,mem_ofPred_eq,not_not]
    rw [eq];exact .unions ((additive_positive h).trans low) _ (fun V => .lowerCompl low (ih _ (isOpen_of_mem_countableBasis V.val.property)))

/-- The comeager-section operation preserves multiplicative Borel rank. -/
theorem section_multiplicative {X J : Type} [TopologicalSpace X] [TopologicalSpace J]
    [SecondCountableTopology J] [BaireSpace J] {α E} (h : MultiplicativeClass (X×J) α E)
    (U : Set J) (hU : IsOpen U) : MultiplicativeClass X α (comeagerSection E U) := by
  simpa only [MultiplicativeClass,comeagerSection,compl_compl] using section_additive h U hU

end UniversalWadge
