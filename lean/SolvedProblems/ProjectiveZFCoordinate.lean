module

public import SolvedProblems.ProjectiveZFPatch

@[expose] public section

namespace ProjectiveZF

variable {V : Type*} [Membership V V]

/-- A noninjective self-surjection is an actual set of the membership model,
with a preimage for each internal element and a witnessed collision. -/
def DualInfinite (X : V) : Prop := ∃ f : V, IsMap X X f ∧
  (∀ y, y ∈ X → ∃ x, x ∈ X ∧ Edge f x y) ∧
  ∃ a, a ∈ X ∧ ∃ b, b ∈ X ∧ a ≠ b ∧ ∃ y, Edge f a y ∧ Edge f b y

/-- The coordinate operation composes the given internal map at `i`, leaving
all other coordinates fixed. -/
def Step (f i s t : V) : Prop := ∃ a b, Edge s i a ∧ Edge f a b ∧ Patch i b s t

private theorem defStep {ι : Type*} {f i s t : (ι → V) → V} (hf : Term f) (hi : Term i) (hs : Term s) (ht : Term t) :
    Definable (fun v => Step (f v) (i v) (s v) (t v)) := by
  unfold Step
  repeat' first | apply defPatch | apply defEdge | apply defAnd | apply defEx | zf_terms

/-- In every model of this fragment of pure ZF, dual Dedekind infinity of `X`
implies dual Dedekind infinity of its internal function space `X^I` for every
internally nonempty `I`. The graph of the lifted function is produced inside
the model by a first-order Separation instance. -/
theorem coordinateLift (M : Core V) (X I i : V) (hi : i ∈ I) (dual : DualInfinite X) :
    DualInfinite (exponential M X I) := by
  obtain ⟨f,hf,onto,a,ha,b,hb,ne,c,hac,hbc⟩ := dual
  let E := exponential M X I
  have mapmem (s : V) : s ∈ E ↔ IsMap I X s := mem_exponential M
  have total (s : V) (hs : s ∈ E) : ∃ t, t ∈ E ∧ Step f i s t := by
    have smap := (mapmem s).mp hs
    obtain ⟨x,hx⟩ := smap.2.1 _ hi
    obtain ⟨y,hy⟩ := hf.2.1 x (edge_typed M smap hx).2
    obtain ⟨t,ht,p⟩ := patchExists M smap hi (edge_typed M hf hy).2
    exact ⟨t,(mapmem t).mpr ht,x,y,hx,hy,p⟩
  have unique (s : V) (hs : s ∈ E) (t) (ht : t ∈ E) (u) (hu : u ∈ E) (st : Step f i s t) (su : Step f i s u) : t = u := by
    obtain ⟨x,y,hx,hy,pt⟩ := st
    obtain ⟨x',y',hx',hy',pu⟩ := su
    obtain rfl := ((mapmem s).mp hs).2.2 i x x' hx hx'
    obtain rfl := hf.2.2 _ _ _ hy hy'
    exact patchUnique M ((mapmem t).mp ht) ((mapmem u).mp hu) pt pu
  have form : Binary (Step f i) := defStep (termParam f) (termParam i) (termVar false) (termVar true)
  obtain ⟨F,map,rule⟩ := mapFrom M E E (Step f i) form total unique
  refine ⟨F,map,?_,?_⟩
  · intro t ht
    have tmap := (mapmem t).mp ht
    obtain ⟨y,hy⟩ := tmap.2.1 _ hi
    obtain ⟨x,hx,xy⟩ := onto _ (edge_typed M tmap hy).2
    obtain ⟨s,smap,p⟩ := patchExists M tmap hi hx
    have hs := (mapmem s).mpr smap
    exact ⟨s,hs,(rule s t).mpr ⟨hs,ht,x,y,(p i x).mpr (Or.inl ⟨rfl,rfl⟩),xy,patchBack tmap hy p⟩⟩
  · obtain ⟨s,sm,edge⟩ := constantGraph (I := I) M ha
    obtain ⟨t,tm,pt⟩ := patchExists M sm hi hb
    obtain ⟨u,um,pu⟩ := patchExists M sm hi (edge_typed M hf hac).2
    have hs := (mapmem s).mpr sm
    have ht := (mapmem t).mpr tm
    have hu := (mapmem u).mpr um
    have bt : Edge t i b := (pt i b).mpr (Or.inl ⟨rfl,rfl⟩)
    refine ⟨s,hs,t,ht,fun eq => ne (sm.2.2 i a b (edge i hi) (eq ▸ bt)),u,?_,?_⟩
    · exact (rule s u).mpr ⟨hs,hu,a,c,edge i hi,hac,pu⟩
    · exact (rule t u).mpr ⟨ht,hu,b,c,bt,hbc,patchAbsorb pt pu⟩

end ProjectiveZF
