module

public import SolvedProblems.ProjectiveGraph

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ} {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]

private def MatchesMaps (f : Codes A k → Codes A k) (g : Codes B k → Codes B k) : Prop :=
  ∀ {ι : Type} [Finite ι] {a : ι → A} {b : ι → B},
    tupleType (graphLanguage k) a = tupleType _ b → ∀ p q : Codes ι k,
      f (decode a p) = decode a q ↔ g (decode b p) = decode b q

private theorem lift_surjective {f : Codes A k → Codes A k} {g : Codes B k → Codes B k}
    (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    (graphs : MatchesMaps f g) (surj : Surjective f) : Surjective g := by
  intro x
  obtain ⟨n,p,b,rfl⟩ := present x
  obtain ⟨a,m⟩ := match_from_right eq fin b
  obtain ⟨pre,hpre⟩ := surj (decode a p)
  obtain ⟨l,q,z,rfl⟩ := present pre
  obtain ⟨w,joint⟩ := extendTuple (graphLanguage k) eq (fin (Fin n ⊕ Fin l)) m z
  have t := graphs joint (decode Sum.inr q) (decode Sum.inl p)
  simp only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] at t
  exact ⟨_,t.mp hpre⟩

private theorem lift_injective {f : Codes A k → Codes A k} {g : Codes B k → Codes B k}
    (eq : A ≅[graphLanguage k] B) (finB : FiniteTypes (graphLanguage k) B)
    (graphs : MatchesMaps f g) (inj : Injective g) : Injective f := by
  intro x y h
  obtain ⟨n,p,a,rfl⟩ := present x
  obtain ⟨m,q,b,rfl⟩ := present y
  obtain ⟨l,r,z,hz⟩ := present (f (decode a p))
  let v := Sum.elim a (Sum.elim b z)
  let X := decode (Sum.inl : Fin n → Fin n ⊕ (Fin m ⊕ Fin l)) p
  let Y := decode (fun j : Fin m => Sum.inr (Sum.inl j) : Fin m → Fin n ⊕ (Fin m ⊕ Fin l)) q
  let Z := decode (fun j : Fin l => Sum.inr (Sum.inr j) : Fin l → Fin n ⊕ (Fin m ⊕ Fin l)) r
  have ex : decode v X = decode a p := by simp only [X,decode_comp]; rfl
  have ey : decode v Y = decode b q := by simp only [Y,decode_comp]; rfl
  have ez : decode v Z = decode z r := by simp only [Z,decode_comp]; rfl
  obtain ⟨w,mw⟩ := match_from_right (Eq.symm eq) finB v
  have hx := (graphs mw.symm X Z).mp (by rw [ex,ez,hz])
  have hy := (graphs mw.symm Y Z).mp (by rw [ey,ez,hz,h])
  exact ex.symm.trans (((match_codes mw X Y).mp (inj (hx.trans hy.symm))).trans ey)

/-- In any elementarily equivalent structure, the graph predicates of a map on
coded finite/cofinite sets define a unique self-map. Surjectivity and injectivity
are both preserved and reflected. Finite type spectra are only required of the
source structure, and there is no uniform bound assumption on output lengths. -/
theorem transferGraph (k : ℕ) {M N : Type*} (f : Codes M k → Codes M k)
    [(graphLanguage k).Structure N] :
    letI := graphStructure f
    M ≅[graphLanguage k] N → FiniteTypes (graphLanguage k) M →
      ∃ g : Codes N k → Codes N k,
        (∀ x y, g x = y ↔ recorded x y) ∧
        (Surjective f ↔ Surjective g) ∧ (Injective f ↔ Injective g) := by
  let := graphStructure f
  intro eq fin
  have src : Records f := by intro n p q t; rfl
  have fin' : FiniteTypes (graphLanguage k) N := fun ι _ =>
    (realizedTypes_eq _ eq (fin ι)) ▸ fin ι
  let g (x : Codes N k) := Classical.choose (graph_total src eq fin x)
  have prop (x y : Codes N k) : g x = y ↔ recorded x y := by
    have chosen := Classical.choose_spec (graph_total src eq fin x)
    exact ⟨fun h => h ▸ chosen, graph_functional src eq fin chosen⟩
  have graphs : MatchesMaps f g := fun {_ _ _ _} h p q =>
    (compareGraph src eq fin h p q).trans (prop _ _).symm
  have reverse : MatchesMaps g f := fun {_ _ _ _} h p q => (graphs h.symm p q).symm
  exact ⟨g,prop,⟨lift_surjective eq fin graphs, lift_surjective (Eq.symm eq) fin' reverse⟩,
    ⟨lift_injective (Eq.symm eq) fin reverse, lift_injective eq fin' graphs⟩⟩

end ProjectiveTransfer
