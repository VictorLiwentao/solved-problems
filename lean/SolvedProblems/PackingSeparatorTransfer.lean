module

public import SolvedProblems.PackingSeparatorModel
public import SolvedProblems.PackingSeparatorSpan

public section

namespace PackingSeparator

/-- Directed distances between the two windows agree up to the saturation bound. -/
private def matchDist (b x y x' y' : Nat) :=
  min b (y'-x') = min b (y-x) ∧ min b (x'-y') = min b (x-y)

private theorem sameRankTest {k m j j'} (p : Pattern k m) (x y : Mark k j) (x' y' : Mark k j')
    (hr : x.2 = x'.2) (hs : y.2 = y'.2)
    (h : matchDist (m+1) x.1.val y.1.val x'.1.val y'.1.val) :
    RankTest p x y ↔ RankTest p x' y' := by
  rcases h with ⟨h₁,h₂⟩
  unfold RankTest
  by_cases lo : x.1.val ≤ y.1.val
  · have lo' : x'.1.val ≤ y'.1.val := by omega
    simp only [ite_eq_left lo, ite_eq_left lo', Nat.sub_eq_zero_of_le lo,
      Nat.sub_eq_zero_of_le lo', Nat.add_zero, hr, hs, h₁]
  · have lo' : ¬ x'.1.val ≤ y'.1.val := by omega
    simp only [ite_eq_right lo, ite_eq_right lo', Nat.sub_eq_zero_of_le (Nat.le_of_not_ge lo),
      Nat.sub_eq_zero_of_le (Nat.le_of_not_ge lo'), Nat.zero_add, hr, hs, h₂]

private theorem align {b S T x x' y' : Nat} (hx : x ≤ S) (hx' : x' ≤ T) (hy' : y' ≤ T)
    (L : min b x' = min b x) (R : min b (T-x') = min b (S-x)) :
    ∃ y ≤ S, matchDist b x y x' y' := by
  by_cases h : x' ≤ y'
  · refine ⟨x + min b (y'-x'), by omega, ?_⟩
    unfold matchDist
    constructor <;> omega
  · refine ⟨x - min b (x'-y'), by omega, ?_⟩
    unfold matchDist
    constructor <;> omega

private theorem move {k m} (p : Pattern k m)
    (rankIff : ∀ {n} (x y : Mark k n), LEPos p x y ↔ RankTest p x y)
    {S T} (source : 6*(m+1) ≤ S) (target : 6*(m+1) ≤ T) :
    HasSeparator p (S+1) → HasSeparator p (T+1) := by
  rintro ⟨x,a,b,c,d,allx,ax,bx,ab,xc,xd,cd⟩
  let marks : Fin 5 → Mark k (S+1) := fun i => [x,a,b,c,d][i.val]'(by have := i.isLt; simp)
  let slots := fun i => (marks i).1.val
  have bound (i) : slots i ≤ S := by have := (marks i).1.isLt; change (marks i).1.val ≤ S; omega
  obtain ⟨f,f0,fs,fbound,keep⟩ := PackingSeparatorSpan.transferFive (by omega : 0<m+1)
    source target slots bound
  let lift (v : Mark k (S+1)) : Mark k (T+1) :=
    (⟨f v.1.val, Nat.lt_succ_of_le (fbound _ (Nat.le_of_lt_succ v.1.isLt))⟩, v.2)
  let marked (v : Mark k (S+1)) := v.1.val = 0 ∨ v.1.val = S ∨ ∃ i, slots i = v.1.val
  have mx : marked x := Or.inr (Or.inr ⟨0,rfl⟩)
  have ma : marked a := Or.inr (Or.inr ⟨1,rfl⟩)
  have mb : marked b := Or.inr (Or.inr ⟨2,rfl⟩)
  have mc : marked c := Or.inr (Or.inr ⟨3,rfl⟩)
  have md : marked d := Or.inr (Or.inr ⟨4,rfl⟩)
  have pair (v z : Mark k (S+1)) (mv : marked v) (mz : marked z) :
      LEPos p (lift v) (lift z) ↔ LEPos p v z := by
    rw [rankIff,rankIff]
    exact (sameRankTest p v z (lift v) (lift z) rfl rfl
      ⟨keep _ _ mv mz, keep _ _ mz mv⟩).symm
  refine ⟨lift x,lift a,lift b,lift c,lift d,?_,?_,?_,?_,?_,?_,?_⟩
  · intro y'
    have left := keep 0 x.1.val (Or.inl rfl) mx
    have right := keep x.1.val S mx (Or.inr (Or.inl rfl))
    rw [f0, Nat.sub_zero, Nat.sub_zero] at left
    rw [fs] at right
    obtain ⟨w,hw,matchXY⟩ := align (Nat.le_of_lt_succ x.1.isLt)
      (fbound _ (Nat.le_of_lt_succ x.1.isLt)) (Nat.le_of_lt_succ y'.1.isLt) left right
    let y : Mark k (S+1) := (⟨w,Nat.lt_succ_of_le hw⟩,y'.2)
    rcases allx y with h|h
    · exact Or.inl ((rankIff _ _).mpr ((sameRankTest p x y (lift x) y' rfl rfl matchXY).mp
        ((rankIff _ _).mp h)))
    · exact Or.inr ((rankIff _ _).mpr ((sameRankTest p y x y' (lift x) rfl rfl ⟨matchXY.2, matchXY.1⟩).mp
        ((rankIff _ _).mp h)))
  · simpa only [pair a x ma mx, pair x a mx ma] using ax
  · simpa only [pair b x mb mx, pair x b mx mb] using bx
  · simpa only [pair a b ma mb, pair b a mb ma] using ab
  · simpa only [pair x c mx mc, pair c x mc mx] using xc
  · simpa only [pair x d mx md, pair d x md mx] using xd
  · simpa only [pair c d mc md, pair d c md mc] using cd

theorem cutoff_of_rankTest {k m j} (p : Pattern k m)
    (rankIff : ∀ {n} (x y : Mark k n), LEPos p x y ↔ RankTest p x y) :
    HasSeparator p j ↔ HasSeparator p (min j (6*(m+1)+1)) := by
  rcases Nat.le_total j (6*(m+1)+1) with small|large
  · rw [Nat.min_eq_left small]
  · rw [Nat.min_eq_right large]
    obtain ⟨S,rfl⟩ : ∃ s, j=s+1 := ⟨j-1,by omega⟩
    exact ⟨move p rankIff (by omega) (Nat.le_refl _),
      move p rankIff (Nat.le_refl _) (by omega)⟩

end PackingSeparator
