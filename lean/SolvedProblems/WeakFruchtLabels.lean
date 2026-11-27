module

public import SolvedProblems.WeakFruchtRecords
public import SolvedProblems.WeakFrucht

@[expose] public section

namespace WeakFrucht

variable {S : Type u}

/-- A single type for all marked graphs, including their two triangle vertices. -/
abbrev Marked (S : Type u) := FiniteFrucht.Vertex (@paint S) ⊕ Bool

def holder (x : Record S) : FiniteFrucht.Vertex (@paint S) := .base ⟨.term,x⟩

def recordGraph (B : SimpleGraph S) (p : S) (u : Record S) : SimpleGraph (Marked S) :=
  addTriangle (FiniteFrucht.graph (skeleton B p) paint) (holder u)

theorem record_distinguishes (B : SimpleGraph S) (p : S) (rigid : PointRigid B p) {x y : Record S}
    (iso : Iso (recordGraph B p x).Adj (recordGraph B p y).Adj) : x = y := by
  let A := skeleton B p
  let U := FiniteFrucht.graph A paint
  have free := paths_no_triangle A paint side (fun h => skeleton_bipartite B p h)
  have hasNbr (t : Record S) : ∃ r, U.Adj (holder t) r :=
    ⟨.base ⟨.hub,⟨⟩⟩, Or.inr trivial⟩
  obtain ⟨f,hf,move⟩ := recover_mark U free (hasNbr x) (hasNbr y) iso
  let g := FiniteFrucht.oldPerm A paint f hf
  have fixed := skeleton_terms_fixed B p rigid g (FiniteFrucht.old_adj A paint f hf) (FiniteFrucht.old_color A paint f hf) x
  have e : f (holder x) = holder x := (FiniteFrucht.old_base A paint f hf ⟨.term,x⟩).trans (congrArg _ fixed)
  exact eq_of_heq (Sigma.mk.inj (FiniteFrucht.Vertex.base.inj (e.symm.trans move))).2

private def payloadCode (k : Role) : Payload S k → Record S :=
  match k with
  | .hub => fun _ => .num 0
  | .term | .wire₁ | .wire₂ | .left | .right | .edge | .point => id

private def cellCode (c : Skeleton S) : Record S := .pair (.num c.1.code) (payloadCode c.1 c.2)

private theorem cellCode_inj : Function.Injective (@cellCode S) := by
  rintro ⟨k,x⟩ ⟨t,y⟩ eq
  have h := Record.pair.inj eq
  obtain rfl : k=t := role_inj (Record.num.inj h.1)
  apply congrArg (Sigma.mk k)
  cases k <;> first | exact Subsingleton.elim x y | exact h.2

private def vertexCode : FiniteFrucht.Vertex (@paint S) → Record S
  | .base r => .pair (.num 0) (cellCode r)
  | .tip r b j _ => .pair (.num 1) (.pair (cellCode r) (.pair (.num b.val) (.num j)))

private theorem vertexCode_inj : Function.Injective (@vertexCode S) := by
  intro a z eq
  cases a <;> cases z
  rename_i r s
  · exact congrArg FiniteFrucht.Vertex.base (cellCode_inj (Record.pair.inj eq).2)
  · exact False.elim (Nat.noConfusion (Record.num.inj (Record.pair.inj eq).1))
  · exact False.elim (Nat.noConfusion (Record.num.inj (Record.pair.inj eq).1))
  · rename_i r b j hj s c k hk
    have h := Record.pair.inj (Record.pair.inj eq).2
    have e := Record.pair.inj h.2
    obtain rfl := cellCode_inj h.1
    obtain rfl : b=c := Fin.ext (Record.num.inj e.1)
    obtain rfl := Record.num.inj e.2
    rfl

private def labelCode : Marked S → Record S
  | .inl r => .pair (.num 0) (vertexCode r)
  | .inr false => .num 0
  | .inr true => .num 1

private theorem labelCode_inj : Function.Injective (@labelCode S) := by
  rintro (r|b) (s|c) eq
  · exact congrArg Sum.inl (vertexCode_inj (Record.pair.inj eq).2)
  · cases c <;> cases eq
  · cases b <;> cases eq
  · cases b <;> cases c <;> first | rfl | cases eq

private def code {V : Type v} (i : V → S) : Node V (Marked S) → Record S
  | .origin => .num 0
  | .fresh x c => .pair (.num 0) (.pair (code i x) (.atom (i c)))
  | .marker x c q => .pair (.num 1) (.pair (code i x) (.pair (.atom (i c)) (labelCode q)))
  | .joint x c a b z => .pair (.num 2) (.pair (code i x) (.pair (.atom (i c))
      (.pair (labelCode a) (.pair (labelCode b) (.atom (i z))))))

private theorem code_inj {V : Type v} {i : V → S} (inj : Function.Injective i) : Function.Injective (code i) := by
  intro x
  induction x with
  | origin => intro y h; cases y <;> simp_all [code]
  | fresh x c ih =>
    intro y h; cases y <;> simp [code] at h ⊢
    exact ⟨ih h.1,inj h.2⟩
  | marker x c q ih =>
    intro y h; cases y <;> simp [code] at h ⊢
    exact ⟨ih h.1,inj h.2.1,labelCode_inj h.2.2⟩
  | joint x c a b z ih =>
    intro y h; cases y <;> simp [code] at h ⊢
    exact ⟨ih h.1,inj h.2.1,labelCode_inj h.2.2.1,labelCode_inj h.2.2.2.1,inj h.2.2.2.2⟩

/-- A single pointed rigid graph containing the target supplies unpointed
connected graph labels for every finite record of the entire expansion. All
labels have a common carrier; no further choices at later stages are needed. -/
theorem labels_of_embedding {V : Type v} (i : V → S) (inj : Function.Injective i)
    (B : SimpleGraph S) (p : S) (rigid : PointRigid B p) : Nonempty (Labels V (Marked S)) := by
  let L (x : Node V (Marked S)) := recordGraph B p (code i x)
  have conn (x : Node V (Marked S)) (a b : Marked S) : Reach (L x).Adj a b :=
    mark_connected _ (paths_connected _ _ (skeleton_connected B p)) _ a b
  refine ⟨⟨L,⟨.inr false⟩,conn,?_,fun _ _ h => code_inj inj (record_distinguishes B p rigid h)⟩⟩
  intro x a
  obtain ⟨b,ne⟩ : ∃ b : Marked S, a ≠ b := by
    cases a with
    | inl _ => exact ⟨.inr false,fun eq => by cases eq⟩
    | inr c => exact ⟨.inr (!c),fun h => by cases c <;> cases h⟩
  have last (u : Marked S) (path : Reach (L x).Adj b u) : u=b ∨ ∃ z, (L x).Adj u z := by
    cases path with
    | refl => exact Or.inl rfl
    | tail _ e => exact Or.inr ⟨_,e.symm⟩
  exact (last a (conn x b a)).elim (fun h => (ne h).elim) id

/-- The global rigid-embedding principle entails the full CWFAFA₂ decoration
property, for all extensional accessible pointed digraphs. -/
theorem rigid_embeddings_imply_cwf (em : ∀ p : Prop, p ∨ ¬p)
    (embed : ∀ I : Type u, ∃ (S : Type u) (B : SimpleGraph S) (p : S) (i : I → S),
      PointRigid B p ∧ Function.Injective i) {V : Type u} (D : V → V → Prop) (o : V)
    (acc : AccessibleFrom D o) (extD : Extensional D) : Nonempty (Representation.{u,u} D o) := by
  apply reusable_labels_suffice em _ D o acc extD
  intro I
  obtain ⟨S,B,p,i,rigid,inj⟩ := embed I
  exact ⟨Marked S, labels_of_embedding i inj B p rigid⟩

end WeakFrucht
