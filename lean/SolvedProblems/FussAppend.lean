module

public import SolvedProblems.FussModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

public section

namespace FussDyck

private def appendEast (v : Word n b) : Word n (b+1) := Fin.snoc v 0

private theorem snoc_values (v : Word n b) (c : Fin (n+1)) :
    (List.ofFn (fun i => (Fin.snoc (α := fun _ => Fin (n+1)) v c i).val)) =
      (List.ofFn (fun i => (v i).val)) ++ [c.val] := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

private theorem append_prefix (v : Word n b) {t : Nat} (h : t ≤ b) :
    prefixN (appendEast v) t = prefixN v t := by
  simp only [prefixN,appendEast,snoc_values]
  rw [List.take_append_of_le_length (by simpa using h)]

private theorem total_snoc (v : Word n b) (c : Fin (n+1)) :
    prefixN (Fin.snoc v c) (b+1) = prefixN v b + c.val := by
  unfold prefixN
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp), snoc_values]
  simp

private theorem append_card (v : Word n b) (h : Nat) :
    (positions (appendEast v) h).card = (positions v h).card := by
  unfold positions
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp [appendEast]

private theorem append_stats (v : Word n b) :
    Stats (appendEast v) k j ↔ Stats v k j := by
  unfold Stats
  rw [append_card,append_card]
  simp only [appendEast,total_snoc,Fin.val_zero,Nat.add_zero]

private theorem prefix_le (v : Word n b) (t : Nat) : prefixN v t ≤ prefixN v b := by
  let l := List.ofFn (fun i => (v i).val)
  have h : (l.take t).sum + (l.drop t).sum = l.sum := by rw [← List.sum_append,List.take_append_drop]
  change (l.take t).sum ≤ (l.take b).sum
  have hb : l.take b = l := List.take_of_length_le (by simp [l])
  rw [hb]
  omega

private theorem slope_iff {n m t y : Nat} (ht : t ≤ m*n) (hy : y ≤ n) :
    n*t ≤ (m*n+1)*y ↔ t ≤ m*y := by
  constructor
  · intro h
    by_contra! hbad
    have hmult := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hbad)
    have hstrict : y < n := lt_of_le_of_ne hy (fun e => by subst y; omega)
    nlinarith only [h,hstrict,hmult]
  · intro h
    have hmult := Nat.mul_le_mul_left n h
    nlinarith only [hmult,Nat.zero_le y]

private theorem append_good {v : Word n (m*n)} (hv : prefixN v (m*n) = n) :
    RationalPath (appendEast v) ↔ FussPath m v := by
  constructor
  · intro hr t ht
    have h := hr t (by omega)
    rw [append_prefix _ ht] at h
    exact (slope_iff ht ((prefix_le v t).trans_eq hv)).mp h
  · intro hf t ht
    by_cases h : t ≤ m*n
    · rw [append_prefix _ h]
      exact (slope_iff h ((prefix_le v t).trans_eq hv)).mpr (hf t h)
    · have e : t = m*n+1 := by omega
      subst t
      unfold appendEast
      rw [total_snoc,Fin.val_zero,hv,Nat.mul_comm]
      simp

private theorem last_zero {v : Word n (m*n+1)} (hm : 0 < m) (h : prefixN v (m*n+1) = n)
    (hr : RationalPath v) : v (Fin.last (m*n)) = 0 := by
  let u : Word n (m*n) := fun i => v i.castSucc
  let c := v (Fin.last (m*n))
  have eq : Fin.snoc u c = v := Fin.snoc_init_self _
  have ht := hr (m*n) (by omega)
  rw [← eq,total_snoc] at h
  have pref : prefixN v (m*n) = prefixN u (m*n) := by
    rw [← eq]
    simp only [prefixN,snoc_values]
    rw [List.take_append_of_le_length (by simp)]
  rw [pref] at ht
  change c = 0
  apply Fin.ext
  change c.val = 0
  by_contra! hc
  have hc' : prefixN u (m*n)+1 ≤ n := by omega
  have big := Nat.mul_le_mul_left (m*n+1) hc'
  have mn : n ≤ m*n := by simpa using (Nat.mul_le_mul_right n (show 1 ≤ m from hm))
  nlinarith only [big,ht,mn]

/-- Append one final east step. The rational slope forces this step to have
no preceding north steps, giving deletion as an inverse and preserving both statistics. -/
theorem append_count (hm : 0 < m) (n k j : Nat) :
    pathCount m n k j = rationalCount n (m*n+1) k j := by
  classical
  apply Fintype.card_congr
  let f (v : {v : Word n (m*n) // Stats v k j ∧ FussPath m v}) :
      {v : Word n (m*n+1) // Stats v k j ∧ RationalPath v} :=
    ⟨appendEast v.val,(append_stats _).mpr v.property.1,(append_good v.property.1.1).mpr v.property.2⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro v w he
    apply Subtype.ext
    funext i
    have hi := congrArg (fun z : {v : Word n (m*n+1) // Stats v k j ∧ RationalPath v} =>
      z.val i.castSucc) he
    change (Fin.snoc (α := fun _ => Fin (n+1)) v.val 0 i.castSucc) =
      (Fin.snoc (α := fun _ => Fin (n+1)) w.val 0 i.castSucc) at hi
    simpa only [Fin.snoc_castSucc] using hi
  · rintro ⟨w,hw,hr⟩
    let u : Word n (m*n) := fun i => w i.castSucc
    have eq : appendEast u = w := by
      unfold appendEast
      rw [← last_zero hm hw.1 hr]
      exact Fin.snoc_init_self _
    have hu : Stats u k j := (append_stats _).mp (eq ▸ hw)
    have good := (append_good hu.1).mp (eq ▸ hr)
    exact ⟨⟨u,hu,good⟩,Subtype.ext eq⟩

end FussDyck
