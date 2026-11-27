module

public import SolvedProblems.ColourProbeHamming

@[expose] public section

namespace ColourProbe

open SimpleGraph

abbrev Palette (V : Type*) := V ⊕ Option V

/-- The support consists of at most two changed coordinates. They are required
to be nonadjacent so that their fresh colors may coincide. -/
def Allowed {V : Type*} (G : SimpleGraph V) := {S : Finset V // S.card ≤ 2 ∧ ∀ i ∈ S, ∀ j ∈ S, ¬G.Adj i j}

def Row {V : Type*} (G : SimpleGraph V) := (S : Allowed G) × (S.val → Option V)

noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype (Allowed G) := by
  classical unfold Allowed; infer_instance

noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype (Row G) := by
  classical unfold Row; infer_instance

noncomputable def word {V : Type*} {G : SimpleGraph V} (r : Row G) (i : V) : Palette V := by
  classical exact if h : i ∈ r.1.val then Sum.inr (r.2 ⟨i,h⟩) else Sum.inl i

theorem word_in {V : Type*} {G : SimpleGraph V} (r : Row G) (i : V) (h : i ∈ r.1.val) :
    word r i = Sum.inr (r.2 ⟨i,h⟩) := by classical simp [word,h]

theorem word_out {V : Type*} {G : SimpleGraph V} (r : Row G) (i : V) (h : i ∉ r.1.val) :
    word r i = Sum.inl i := by classical simp [word,h]

theorem word_injective {V : Type*} (G : SimpleGraph V) : Function.Injective (word (G := G)) := by
  rintro ⟨⟨S,hs⟩,v⟩ ⟨⟨T,ht⟩,w⟩ h
  classical
  have st : S = T := by
    ext i
    have hi := congrFun h i
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all [word]
  subst T
  congr 1
  funext i
  have hi := congrFun h i.val
  simpa [word,i.property] using hi

theorem proper_word {V : Type*} {G : SimpleGraph V} (r : Row G) : Proper G (word r) := by
  intro i j hij
  classical
  by_cases hi : i ∈ r.1.val <;> by_cases hj : j ∈ r.1.val
  · exact False.elim (r.1.property.2 i hi j hj hij)
  · simp [word,hi,hj]
  · simp [word,hi,hj]
  · simpa [word,hi,hj] using hij.ne

noncomputable def probe {V : Type*} (G : SimpleGraph V) : SimpleGraph (Row G) :=
  (hamming V (Palette V)).comap word

noncomputable def rainbow {V : Type*} (G : SimpleGraph V) : Row G :=
  ⟨⟨∅,by simp⟩,fun i => False.elim (Finset.notMem_empty i.val i.property)⟩

@[simp] theorem word_rainbow {V : Type*} (G : SimpleGraph V) (i : V) : word (rainbow G) i = Sum.inl i := by
  apply word_out
  simp [rainbow]

noncomputable def single {V : Type*} (G : SimpleGraph V) (i : V) (a : Option V) : Row G := by
  classical exact ⟨⟨{i},by simp⟩,fun _ => a⟩

@[simp] theorem word_single_at {V : Type*} (G : SimpleGraph V) (i : V) (a : Option V) :
    word (single G i a) i = Sum.inr a := by classical simp [word,single]

theorem word_single_other {V : Type*} (G : SimpleGraph V) (i j : V) (a : Option V) (h : j ≠ i) :
    word (single G i a) j = Sum.inl j := by classical simp [word,single,h]

theorem single_change {V : Type*} (G : SimpleGraph V) (i : V) (a : Option V) :
    OneAt i (word (rainbow G)) (word (single G i a)) :=
  ⟨by simp,fun j hj => by simp [word_single_other G i j a hj]⟩

theorem single_injective {V : Type*} (G : SimpleGraph V) (i : V) : Function.Injective (single G i) := by
  intro a b h
  have eq := congrArg (fun r => word r i) h
  simpa using eq

theorem single_distinct {V : Type*} (G : SimpleGraph V) {i j : V} (hij : i ≠ j) (a b : Option V) :
    single G i a ≠ single G j b := by
  intro h
  have eq := congrArg (fun r => word r i) h
  simp [word_single_other G j i b hij] at eq

noncomputable def double {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : Row G := by
  classical
  refine ⟨⟨{i,j},?_,?_⟩,fun k => if k.val=i then a else b⟩
  · simp [hij]
  · intro x hx y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | exact G.loopless.irrefl _ | exact hn | exact fun h => hn h.symm

theorem double_left {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : OneAt j (word (single G i a)) (word (double G i j hij hn a b)) := by
  classical
  refine ⟨by simp [word,single,double,hij.symm],?_⟩
  intro x hx
  by_cases h : x=i <;> simp [word,single,double,h,hx]

theorem double_right {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : OneAt i (word (single G j b)) (word (double G i j hij hn a b)) := by
  classical
  refine ⟨by simp [word,single,double,hij],?_⟩
  intro x hx
  by_cases h : x=j <;> simp [word,single,double,h,hx,hij.symm]

theorem double_ne_rainbow {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (hn : ¬G.Adj i j) (a b : Option V) : double G i j hij hn a b ≠ rainbow G := by
  intro h
  have hi := congrArg (fun r => word r i) h
  classical simp [word,double,rainbow] at hi

noncomputable def ownEmbedding {V : Type*} (G : SimpleGraph V) :
    probe G ↪g coloringGraph G (Palette V) where
  toFun r := ⟨word r,proper_word r⟩
  inj' _ _ h := word_injective G (congrArg Subtype.val h)
  map_rel_iff' := Iff.rfl

end ColourProbe
