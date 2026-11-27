module

public import SolvedProblems.PrivateListGridModel
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.Rev

@[expose] public section

namespace PrivateList

open scoped Classical

theorem valid_extension {I : Type} [Finite I] {k} (x : I → Point) (hx : Function.Injective x)
    (c : I → Label k) (blocks : ∀ i j, c i ≠ 0 → c i < c j → SW (x i) (x j))
    (inside : ∀ i j, i ≠ j → c i ≠ 0 → c i = c j → if (c i).val = 2 then
      opposed (x i) (x j) ∨ opposed (x j) (x i) else SW (x i) (x j) ∨ SW (x j) (x i)) :
    ∃ h : Hyp k, Valid h ∧ ∀ i, h (x i) = c i := by
  let h := Function.extend x c (fun _ => 0)
  have agrees (i) : h (x i) = c i := hx.extend_apply _ _ _
  have witnessed {u} (hu : h u ≠ 0) : ∃ i, x i = u := by
    by_contra hn; exact hu (Function.extend_apply' c _ _ hn)
  refine ⟨h, ⟨(Set.finite_range x).subset fun _ hu => witnessed hu, ?_, ?_⟩, agrees⟩
  · intro u v h₁ h₂
    obtain ⟨i,rfl⟩ := witnessed h₁
    obtain ⟨j,rfl⟩ := witnessed (ne_of_gt ((Fin.pos_iff_ne_zero.mpr h₁).trans h₂))
    simp only [agrees] at h₁ h₂
    exact blocks i j h₁ h₂
  · intro u v huv h₁ h₂
    obtain ⟨i,rfl⟩ := witnessed h₁
    obtain ⟨j,rfl⟩ := witnessed (h₂ ▸ h₁)
    simp only [agrees] at h₁ h₂ ⊢
    exact inside i j (fun e => huv (congrArg x e)) h₁ h₂

/-- Lexicographic positive-label blocks, reversing the vertical order exactly in color two. -/
def turn {k n} (p : Label k × Fin n) : Label k × Fin n :=
  (p.1, if p.1.val = 2 then p.2.rev else p.2)

theorem turn_turn {k n} (p : Label k × Fin n) : turn (turn p) = p := by
  rcases p with ⟨y,j⟩; by_cases hy : y.val = 2 <;> simp [turn,hy]

def balancedTemplate (k n : ℕ) : Template k ((k+1)*n) where
  xRank := Equiv.refl _
  yRank := (finProdFinEquiv.symm.trans (Equiv.mk turn turn turn_turn turn_turn)).trans finProdFinEquiv
  label i := (finProdFinEquiv.symm i).1

theorem balanced_counts (k n) (y : Label k) :
    (Finset.univ.filter fun i => (balancedTemplate k n).label i = y).card = n := by
  let f (j : Fin n) := finProdFinEquiv (y,j)
  have injective : Function.Injective f := fun _ _ h => congrArg Prod.snd (finProdFinEquiv.injective h)
  have eq : (Finset.univ.filter fun i => (balancedTemplate k n).label i = y) = Finset.univ.image f := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro h
      exact ⟨(finProdFinEquiv.symm i).2, by change (finProdFinEquiv.symm i).1 = y at h; change finProdFinEquiv (_,_) = _; rw [← h]; exact finProdFinEquiv.apply_symm_apply i⟩
    · rintro ⟨j,rfl⟩; exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (y,j))
  rw [eq,Finset.card_image_of_injective _ injective];simp

private theorem block_lt {k n} {y z : Label k} {i j : Fin n} (lt : y < z) :
    finProdFinEquiv (y,i) < finProdFinEquiv (z,j) := by
  change i.val+n*y.val < j.val+n*z.val
  have bound := Nat.mul_le_mul_left n (show y.val+1 ≤ z.val from lt)
  rw [Nat.mul_succ] at bound
  have := i.isLt
  omega

private theorem same_lt {k n} {y : Label k} {i j : Fin n} (lt : i < j) :
    finProdFinEquiv (y,i) < finProdFinEquiv (y,j) := by
  change i.val+n*y.val < j.val+n*y.val
  exact Nat.add_lt_add_right lt _

theorem balanced_fits (k n) (a b : Fin ((k+1)*n) → ℕ) (ha : StrictMono a) (hb : StrictMono b) :
    Consistent (place (balancedTemplate k n) a b) := by
  let e : Label k × Fin n ≃ Fin ((k+1)*n) := finProdFinEquiv
  let x (p : Label k × Fin n) : Point := (a (e p), b (e (turn p)))
  have inj : Function.Injective x := fun _ _ h => e.injective (ha.injective (congrArg Prod.fst h))
  have blocks (p q : Label k × Fin n) (_ : p.1 ≠ 0) (hpq : p.1 < q.1) : SW (x p) (x q) :=
    ⟨ha (block_lt hpq), hb (block_lt hpq)⟩
  have inside (p q : Label k × Fin n) (ne : p ≠ q) (_ : p.1 ≠ 0) (eq : p.1 = q.1) :
      if p.1.val = 2 then opposed (x p) (x q) ∨ opposed (x q) (x p)
      else SW (x p) (x q) ∨ SW (x q) (x p) := by
    rcases p with ⟨y,i⟩; rcases q with ⟨z,j⟩; change y=z at eq; subst z
    have ij : i ≠ j := fun h => ne (h ▸ rfl)
    by_cases hy : y.val = 2
    · simp only [hy, ↓reduceIte]
      rcases lt_or_gt_of_ne ij with lt|gt
      · left; exact ⟨ha (same_lt lt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ (Fin.rev_lt_rev.mpr lt))⟩
      · right; exact ⟨ha (same_lt gt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ (Fin.rev_lt_rev.mpr gt))⟩
    · simp only [hy, ↓reduceIte]
      rcases lt_or_gt_of_ne ij with lt|gt
      · left; exact ⟨ha (same_lt lt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ lt)⟩
      · right; exact ⟨ha (same_lt gt), by simpa [x,turn,hy,e] using hb (@same_lt k n y _ _ gt)⟩
  obtain ⟨h,hv,hit⟩ := valid_extension x inj Prod.fst blocks inside
  refine ⟨h,hv,fun i => ?_⟩
  have hi := hit (e.symm i)
  change h (a (e (e.symm i)), b (e (turn (e.symm i)))) = _ at hi
  rw [e.apply_symm_apply] at hi
  exact hi

end PrivateList
