module

public import SolvedProblems.ProjectiveCodeMatch

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ} {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]

/-- The source structure's predicates record exactly the given map, even when the
coordinate masks overlap. This property holds by definition in `graphStructure f`. -/
@[expose] def Records (f : Codes A k → Codes A k) : Prop :=
  ∀ {n : ℕ} (p q : Codes (Fin n) k) (v : Fin n → A),
    Structure.RelMap (L := graphLanguage k) (p,q) v ↔ f (decode v p) = decode v q

private theorem record_of_match {ι : Type} [Finite ι] {f : Codes A k → Codes A k}
    (hf : Records f) {a : ι → A} {b : ι → B}
    (m : tupleType (graphLanguage k) a = tupleType _ b) (p q : Codes ι k)
    (h : f (decode a p) = decode a q) : recorded (decode b p) (decode b q) := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have ma := match_subtuple m e.symm
  refine ⟨_, decode e p, decode e q, b ∘ e.symm, ?_, ?_, ?_⟩
  · simp [Function.comp_assoc]
  · simp [Function.comp_assoc]
  apply (match_relation ma _ _).mp
  apply (hf _ _ _).mpr
  simpa [Function.comp_assoc] using h

/-- Moving the enumeration of the finite parts, or its shape, preserves the
value of the recorded graph. Matching a larger tuple on the first side verifies
all potential other presentations without assuming a fixed output size. -/
theorem compareGraph {ι : Type} [Finite ι] {f : Codes A k → Codes A k}
    (hf : Records f) (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    {a : ι → A} {b : ι → B} (m : tupleType (graphLanguage k) a = tupleType _ b) (p q : Codes ι k) :
    f (decode a p) = decode a q ↔ recorded (decode b p) (decode b q) := by
  refine ⟨record_of_match hf m p q, ?_⟩
  rintro ⟨n,u,v,b',hu,hv,r⟩
  have sameTypes := realizedTypes_eq (graphLanguage k) eq (fin (ι ⊕ Fin n))
  obtain ⟨a',joint⟩ := extendTuple (graphLanguage k) (Eq.symm eq) (sameTypes ▸ fin _) m.symm b'
  have sub := match_subtuple joint (Sum.inr : Fin n → ι ⊕ Fin n)
  simp only [Sum.elim_comp_inr] at sub
  have rel := (hf u v a').mp ((match_relation sub u v).mp r)
  have h₁ := (match_cross joint p u).mp hu.symm
  have h₂ := (match_cross joint q v).mp hv.symm
  rwa [h₁,h₂]

/-- Interpret a pair whose masks use disjoint lists of entries. -/
theorem comparePair {ι κ : Type} [Finite ι] [Finite κ] {f : Codes A k → Codes A k}
    (hf : Records f) (eq : A ≅[graphLanguage k] B) (fin : FiniteTypes (graphLanguage k) A)
    {a : ι → A} {b : ι → B} {u : κ → A} {v : κ → B}
    (m : tupleType (graphLanguage k) (Sum.elim a u) = tupleType _ (Sum.elim b v))
    (p : Codes ι k) (q : Codes κ k) : f (decode a p) = decode u q ↔ recorded (decode b p) (decode v q) := by
  have h := compareGraph hf eq fin m (decode Sum.inl p) (decode Sum.inr q)
  simpa only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] using h

/-- Every tuple on the second side can first be matched on the first. -/
theorem match_from_right {ι : Type} [Finite ι] (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) (b : ι → B) :
    ∃ a : ι → A, tupleType (graphLanguage k) a = tupleType _ b := by
  have hs := realizedTypes_eq (graphLanguage k) eq (fin ι)
  change tupleType (graphLanguage k) b ∈ typesIn (graphLanguage k) A ι
  rw [hs]
  exact ⟨b,rfl⟩

/-- The graph interpreted on the second side is total. -/
theorem graph_total {f : Codes A k → Codes A k} (hf : Records f) (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) (x : Codes B k) : ∃ y, recorded x y := by
  obtain ⟨n,p,b,rfl⟩ := present x
  obtain ⟨a,m⟩ := match_from_right eq fin b
  obtain ⟨l,q,z,hz⟩ := present (f (decode a p))
  obtain ⟨w,joint⟩ := extendTuple (graphLanguage k) eq (fin (Fin n ⊕ Fin l)) m z
  exact ⟨_,(comparePair hf eq fin joint p q).mp hz.symm⟩

/-- The graph interpreted on the second side is single-valued. -/
theorem graph_functional {f : Codes A k → Codes A k} (hf : Records f) (eq : A ≅[graphLanguage k] B)
    (fin : FiniteTypes (graphLanguage k) A) {x y z : Codes B k} (hy : recorded x y)
    (hz : recorded x z) : y = z := by
  obtain ⟨n,p,q,b,rfl,rfl,r⟩ := hy
  obtain ⟨l,u,v,w,hu,rfl,t⟩ := hz
  obtain ⟨ab,m⟩ := match_from_right eq fin (Sum.elim b w)
  let a := ab ∘ Sum.inl
  let z := ab ∘ Sum.inr
  have joint : tupleType (graphLanguage k) (Sum.elim a z) = tupleType _ (Sum.elim b w) := by
    simpa [a,z] using m
  have m₁ := match_subtuple m (Sum.inl : Fin n → Fin n ⊕ Fin l)
  have m₂ := match_subtuple m (Sum.inr : Fin l → Fin n ⊕ Fin l)
  simp only [Sum.elim_comp_inl,Sum.elim_comp_inr] at m₁ m₂
  have h₁ := (hf p q a).mp ((match_relation m₁ p q).mpr r)
  have h₂ := (hf u v z).mp ((match_relation m₂ u v).mpr t)
  have h : decode a p = decode z u := (match_cross joint p u).mpr hu.symm
  exact (match_cross joint q v).mp (h₁.symm.trans ((congrArg f h).trans h₂))

end ProjectiveTransfer
