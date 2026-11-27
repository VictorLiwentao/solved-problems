module

public import SolvedProblems.ColourProbeExtend

@[expose] public section

namespace ColourProbe

open SimpleGraph

def transportWord {V W C D : Type*} (d : V ≃ W) (f : V → C ↪ D) (p : V → C) (w : W) : D :=
  f (d.symm w) (p (d.symm w))

@[simp] theorem transport_word_at {V W C D : Type*} (d : V ≃ W) (f : V → C ↪ D) (p : V → C) (i : V) :
    transportWord d f p (d i) = f i (p i) := by simp [transportWord]

def transportGraph {V W C D : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W) (f : V → C ↪ D)
    (legal : ∀ p : Coloring G C, Proper K (transportWord d f p.val)) :
    coloringGraph G C ↪g coloringGraph K D where
  toFun p := ⟨transportWord d f p.val,legal p⟩
  inj' p q h := by
    apply Subtype.ext
    funext i
    apply (f i).injective
    simpa only [transport_word_at] using congrFun (congrArg Subtype.val h) (d i)
  map_rel_iff' := by
    intro p q
    change (hamming W D).Adj (transportWord d f p.val) (transportWord d f q.val) ↔ (hamming V C).Adj p.val q.val
    constructor
    · rintro ⟨w,hw,ho⟩
      obtain ⟨i,rfl⟩ := d.surjective w
      refine ⟨i,?_,fun j hj => (f j).injective ?_⟩
      · intro h
        exact hw (by simp [transport_word_at,h])
      · simpa only [transport_word_at] using ho (d j) (d.injective.ne hj)
    · rintro ⟨i,hi,ho⟩
      refine ⟨d i,?_,?_⟩
      · simpa only [transport_word_at] using (f i).injective.ne hi
      · intro w hw
        obtain ⟨j,rfl⟩ := d.surjective w
        simpa only [transport_word_at] using congrArg (f j) (ho j (fun h => hw (congrArg d h)))

def keepGraph {V W C : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W)
    (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) :
    coloringGraph G C ↪g coloringGraph K C := by
  apply transportGraph G K d (fun _ => Function.Embedding.refl C)
  intro p w w' h
  obtain ⟨i,rfl⟩ := d.surjective w
  obtain ⟨j,rfl⟩ := d.surjective w'
  rw [transport_word_at,transport_word_at]
  exact p.property (href i j h)

@[simp] theorem keep_at {V W C : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W)
    (href : ∀ i j, K.Adj (d i) (d j) → G.Adj i j) (p : Coloring G C) (i : V) :
    (keepGraph G K d href p).val (d i) = p.val i := by
  exact transport_word_at d (fun _ => Function.Embedding.refl C) p.val i

def Token (V : Type*) := Option (V × Palette V)

noncomputable instance {V : Type*} [Fintype V] : Fintype (Token V) := by unfold Token; infer_instance

/-- Each coordinate has a disjoint palette except for the two base-color
entries deliberately merged into the common symbol `none`. -/
noncomputable def encode {V : Type*} (x y i : V) : Palette V ↪ Token V := by
  classical
  let pred (a : Palette V) := (i=x ∨ i=y) ∧ a=Sum.inl i
  refine ⟨fun a => if pred a then none else some (i,a),?_⟩
  intro a b h
  change (if pred a then none else some (i,a)) = (if pred b then none else some (i,b)) at h
  split_ifs at h with ha hb hb <;> first | exact ha.2.trans hb.2.symm | exact congrArg Prod.snd (Option.some.inj h)

theorem encoding_proper {V W : Type*} (K : SimpleGraph W) (d : V ≃ W) (x y : V) (hxy : ¬K.Adj (d x) (d y))
    (p : V → Palette V) : Proper K (transportWord d (encode x y) p) := by
  classical
  intro w w' he
  obtain ⟨i,rfl⟩ := d.surjective w
  obtain ⟨j,rfl⟩ := d.surjective w'
  have hne : i ≠ j := fun h => he.ne (congrArg d h)
  rw [transport_word_at,transport_word_at]
  change (if (i=x ∨ i=y) ∧ p i=Sum.inl i then none else some (i,p i)) ≠
    (if (j=x ∨ j=y) ∧ p j=Sum.inl j then none else some (j,p j))
  split_ifs with hi hj hj
  · rcases hi.1 with rfl | rfl <;> rcases hj.1 with rfl | rfl <;>
      first | exact False.elim (hne rfl) | exact False.elim (hxy he) | exact False.elim (hxy he.symm)
  · simp
  · simp
  · exact fun h => hne (congrArg Prod.fst (Option.some.inj h))

noncomputable def merged {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W) (x y : V)
    (hxy : ¬K.Adj (d x) (d y)) : probe G ↪g coloringGraph K (Token V) :=
  (transportGraph G K d (encode x y) (fun p => encoding_proper K d x y hxy p.val)).comp (ownEmbedding G)

theorem merged_at {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W) (d : V ≃ W) (x y : V)
    (hxy : ¬K.Adj (d x) (d y)) :
    (merged G K d x y hxy (rainbow G)).val (d x) = (merged G K d x y hxy (rainbow G)).val (d y) := by
  change transportWord d (encode x y) (word (rainbow G)) (d x) = transportWord d (encode x y) (word (rainbow G)) (d y)
  rw [transport_word_at,transport_word_at,word_rainbow,word_rainbow]
  classical simp [encode,Function.Embedding.coeFn_mk]
  rfl

end ColourProbe
