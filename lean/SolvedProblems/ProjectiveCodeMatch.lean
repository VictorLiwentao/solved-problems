module

public import SolvedProblems.ProjectiveTransferModel
import Mathlib.Data.Finset.Union

public section

namespace ProjectiveTransfer

open FirstOrder FirstOrder.Language ProjectiveTypes Function

variable {k : ℕ}

@[simp] theorem decode_comp {U V W : Type*} (f : U → V) (g : V → W) (p : Codes U k) :
    decode g (decode f p) = decode (g ∘ f) p := by
  classical
  funext j
  simp [decode, Finset.image_image, Function.comp_def]

/-- All finitely many finite parts fit on one finite tuple. -/
theorem present {A : Type*} (x : Codes A k) :
    ∃ (n : ℕ) (p : Codes (Fin n) k) (v : Fin n → A), decode v p = x := by
  classical
  let s := Finset.univ.biUnion fun j => (x j).2
  let u : Codes s k := fun j => ((x j).1, Finset.univ.filter fun a => a.val ∈ (x j).2)
  let e := s.equivFin
  refine ⟨s.card,decode e u, (fun i => (e.symm i).val), ?_⟩
  rw [decode_comp]
  funext j
  refine Prod.ext ?_ ?_
  · rfl
  apply Finset.ext
  intro a
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    simpa [e] using (Finset.mem_filter.mp hz).2
  · intro h
    have ha : a ∈ s := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _, h⟩
    exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,by simp⟩

variable {L : Language} {A B ι κ : Type*} [L.Structure A] [L.Structure B]

/-- Restriction/reordering retains equality of complete types. -/
theorem match_subtuple {a : ι → A} {b : ι → B}
    (m : tupleType L a = tupleType L b) (f : κ → ι) : tupleType L (a ∘ f) = tupleType L (b ∘ f) := by
  ext φ
  have h := Set.ext_iff.mp m (φ.relabel f)
  simpa only [tupleType,Set.mem_ofPred_eq,Formula.realize_relabel] using h

private theorem match_eq {a : ι → A} {b : ι → B} (m : tupleType L a = tupleType L b) (i j : ι) :
    a i = a j ↔ b i = b j := by
  have h := Set.ext_iff.mp m ((Term.var i).equal (Term.var j))
  simpa [tupleType] using h

private theorem image_eq_of_match {a : ι → A} {b : ι → B}
    (m : tupleType L a = tupleType L b) (p q : Finset ι) :
    letI := Classical.decEq A
    letI := Classical.decEq B
    p.image a = q.image a → p.image b = q.image b := by
  classical
  intro h
  apply Finset.Subset.antisymm
  · rintro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have mem : a i ∈ q.image a := h ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j,hj,(match_eq m j i).mp he⟩
  · rintro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have mem : a i ∈ p.image a := h.symm ▸ Finset.mem_image_of_mem _ hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j,hj,(match_eq m j i).mp he⟩

private theorem match_codes_one {x : ι → A} {y : ι → B}
    (same : tupleType L x = tupleType L y) (p q : Codes ι k)
    (h : decode x p = decode x q) : decode y p = decode y q := by
  funext j
  have flag := congrArg (fun a : Bool × Finset A => a.1) (congrFun h j)
  exact Prod.ext flag (image_eq_of_match same _ _ (congrArg Prod.snd (congrFun h j)))

/-- Equality of two decoded tuples of finite parts depends only on equality of entries. -/
theorem match_codes {a : ι → A} {b : ι → B} (m : tupleType L a = tupleType L b)
    (p q : Codes ι k) : decode a p = decode a q ↔ decode b p = decode b q :=
  ⟨match_codes_one m p q,match_codes_one m.symm p q⟩

/-- Different masks may be given on the two different parts of a joint tuple. -/
theorem match_cross {a : ι → A} {b : ι → B} {u : κ → A} {v : κ → B}
    (m : tupleType L (Sum.elim a u) = tupleType L (Sum.elim b v))
    (p : Codes ι k) (q : Codes κ k) : decode a p = decode u q ↔ decode b p = decode v q := by
  have h := match_codes m (decode Sum.inl p) (decode Sum.inr q)
  simpa only [decode_comp,Sum.elim_comp_inl,Sum.elim_comp_inr] using h

/-- Atomic graph predicates in matched tuples have identical truth values. -/
theorem match_relation {A B : Type*} [(graphLanguage k).Structure A] [(graphLanguage k).Structure B]
    {n : ℕ} {a : Fin n → A} {b : Fin n → B} (m : tupleType (graphLanguage k) a = tupleType _ b)
    (p q : Codes (Fin n) k) :
    Structure.RelMap (L := graphLanguage k) (p,q) a ↔ Structure.RelMap (L := graphLanguage k) (p,q) b := by
  let r : (graphLanguage k).Relations n := (p,q)
  have h := Set.ext_iff.mp m (r.formula fun i => Term.var i)
  change (r.formula fun i => Term.var i).Realize a ↔ (r.formula fun i => Term.var i).Realize b at h
  simpa only [Formula.realize_rel,Term.realize] using h

end ProjectiveTransfer
