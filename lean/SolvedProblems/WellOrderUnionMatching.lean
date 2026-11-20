module

public import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.NormNum

public section

namespace WellOrderUnion
open Set Cardinal

/-- In an uncountable set with countably many colors, there are as many
disjoint monochromatic triples as there are elements, even at singular cardinals. -/
theorem coloredTriples {B : Type u} [Uncountable B] (Q : B → ℕ) :
    ∃ e : B × Fin 3 ↪ B, ∀ x : B, Q (e (x,0)) = Q (e (x,1)) := by
  classical
  let F (j : ℕ) : Set B := {x | Q x = j}
  let bad : Set B := ⋃ j : {n : ℕ // (F n).Finite}, F j.val
  have cb : bad.Countable := countable_iUnion fun j => j.property.countable
  have : Countable bad := countable_coe_iff.mpr cb
  have small : #bad < #B := mk_le_aleph0.trans_lt (aleph0_lt_mk (α := B))
  obtain ⟨g⟩ := Cardinal.eq.mp (mk_compl_of_infinite bad small).symm
  let J := {n : ℕ // (F n).Infinite}
  let cells (j : J) := ↥(F j.val)
  have good (x : ↑badᶜ) : (F (Q x.val)).Infinite := by
    intro h
    exact x.property (mem_iUnion.mpr ⟨⟨Q x.val,h⟩,rfl⟩)
  let encode (x : B) : Σ j : J, cells j :=
    ⟨⟨Q (g x).val,good (g x)⟩, ⟨(g x).val,rfl⟩⟩
  have encInj : Function.Injective encode := by
    intro a b h
    apply g.injective
    exact Subtype.ext (congrArg (fun z : Σ j : J, cells j => z.2.val) h)
  let decode : (Σ j : J, cells j) ↪ B :=
    ((Function.Embedding.subtype _).sigmaMap (fun j : J => Function.Embedding.refl (cells j))).trans
      (Equiv.sigmaFiberEquiv Q).toEmbedding
  have triple (j : J) : Nonempty ((cells j × Fin 3) ↪ cells j) := by
    have : Infinite (cells j) := j.property.to_subtype
    apply (Cardinal.le_def _ _).mp
    rw [Cardinal.mk_prod]
    simpa using (Cardinal.mul_eq_left (Cardinal.aleph0_le_mk (cells j))
      ((Cardinal.natCast_le_aleph0 (n := 3)).trans (Cardinal.aleph0_le_mk (cells j)))
      (show (3 : Cardinal.{u}) ≠ 0 by norm_num)).le
  let trip (j : J) := (triple j).some
  let pack := ((⟨encode,encInj⟩ : B ↪ Σ j : J, cells j).prodMap (Function.Embedding.refl (Fin 3))).trans
    ((Equiv.sigmaProdDistrib cells (Fin 3)).toEmbedding.trans
      (((Function.Embedding.refl J).sigmaMap trip).trans decode))
  refine ⟨pack, fun x => ?_⟩
  change Q (trip (encode x).1 ((encode x).2, 0)).val =
    Q (trip (encode x).1 ((encode x).2, 1)).val
  exact (trip _ ((encode x).2, 0)).property.trans (trip _ ((encode x).2, 1)).property.symm

end WellOrderUnion
