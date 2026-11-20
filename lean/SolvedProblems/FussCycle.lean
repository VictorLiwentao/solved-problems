module

public import SolvedProblems.FussModel
import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace FussDyck

private def shift {n b : Nat} (c : Fin b) (v : Word n b) : Word n b :=
  fun i => v (i + c)

private def entries (v : Word n b) := List.ofFn (fun i => (v i).val)

private theorem entries_shift (v : Word n b) (c : Fin b) :
    entries (shift c v) = (entries v).rotate c.val := by
  apply List.ext_getElem
  · simp [entries]
  · intro i hi hj
    rw [List.getElem_rotate]
    simp only [entries, List.getElem_ofFn, List.length_ofFn, shift]
    congr 2

private theorem stats_shift [NeZero b] (v : Word n b) (c : Fin b) (k j : Nat) :
    Stats (shift c v) k j ↔ Stats v k j := by
  classical
  have total : prefixN (shift c v) b = prefixN v b := by
    change ((entries (shift c v)).take b).sum = ((entries v).take b).sum
    rw [entries_shift]
    rw [List.take_of_length_le (by simp [entries]), List.take_of_length_le (by simp [entries])]
    exact (List.rotate_perm (entries v) c.val).sum_eq
  have num (t : Nat) : (positions (shift c v) t).card = (positions v t).card := by
    let e := (Equiv.addRight c).subtypeEquiv (p := fun i => t < (shift c v i).val)
      (q := fun i => t < (v i).val) (fun _ => Iff.rfl)
    simpa only [positions, ← Fintype.card_subtype] using Fintype.card_congr e
  simp only [Stats,total,num]

private def ht (v : Word n b) (t : Nat) : ℤ :=
  (b : ℤ)*prefixN v t - (n : ℤ)*t

/-- After cutting a word at c, its prefix heights are the old heights translated
by the height at c. The endpoint is identified with the starting point. -/
private theorem ht_shift (v : Word n b) (endpt : prefixN v b = n) (c : Fin b) (t : Nat)
    (htb : t ≤ b) :
    ht (shift c v) t = ht v (if c.val+t < b then c.val+t else c.val+t-b) - ht v c.val := by
  let xs := entries v
  have len : xs.length = b := by simp [xs,entries]
  have sum : xs.sum = n := by
    change (xs.take b).sum = n at endpt
    simpa [← len] using endpt
  change (b : ℤ) * (((entries (shift c v)).take t).sum : ℕ) - (n : ℤ)*t = _
  rw [entries_shift, List.rotate_eq_drop_append_take (by simp [entries])]
  change (b : ℤ)*((((xs.drop c.val ++ xs.take c.val).take t).sum : Nat) : ℤ) - n*t = _
  by_cases h : c.val+t < b
  · rw [ite_eq_left h, List.take_append_of_le_length (by simp [len]; omega)]
    have add : (xs.take (c.val+t)).sum = (xs.take c.val).sum + ((xs.drop c.val).take t).sum := by
      rw [List.take_add, List.sum_append]
    unfold ht prefixN
    change _ = (b : ℤ) * ((xs.take (c.val+t)).sum : ℤ) - _ - ((b : ℤ)*((xs.take c.val).sum : ℤ)-_)
    rw [add]
    push_cast
    ring
  · rw [ite_eq_right h, List.take_append, List.take_of_length_le (by simp [len]; omega),
        List.length_drop, len, List.take_take, List.sum_append]
    have sub : t-(b-c.val) = c.val+t-b := by omega
    have small : c.val+t-b ≤ c.val := by omega
    rw [sub, min_eq_left small]
    have rest : (xs.take c.val).sum + (xs.drop c.val).sum = n := by
      rw [← List.sum_append, List.take_append_drop, sum]
    have restZ : ((xs.take c.val).sum : ℤ) + ((xs.drop c.val).sum : ℤ) = n := by exact_mod_cast rest
    unfold ht prefixN
    change _ = (b : ℤ)*((xs.take (c.val+t-b)).sum : ℤ) - (n : ℤ)*(c.val+t-b : Nat) -
      ((b : ℤ)*((xs.take c.val).sum : ℤ) - n*c.val)
    push_cast [Nat.cast_sub (by omega : b ≤ c.val+t)]
    rw [← restZ]
    ring

private theorem good_iff_min (v : Word n b) (endpt : prefixN v b = n) (c : Fin b) :
    RationalPath (shift c v) ↔ ∀ d : Fin b, ht v c.val ≤ ht v d.val := by
  have good (t : Nat) : n*t ≤ b*prefixN (shift c v) t ↔ 0 ≤ ht (shift c v) t := by
    unfold ht
    rw [sub_nonneg]
    exact_mod_cast Iff.rfl
  constructor
  · intro hg d
    by_cases h : c.val ≤ d.val
    · have q := (good _).mp (hg (d.val-c.val) (by omega))
      rw [ht_shift v endpt c _ (by omega), ite_eq_left (by omega), show c.val+(d.val-c.val)=d.val by omega] at q
      omega
    · have q := (good _).mp (hg (b-c.val+d.val) (by omega))
      rw [ht_shift v endpt c _ (by omega), ite_eq_right (by omega), show c.val+(b-c.val+d.val)-b=d.val by omega] at q
      omega
  · intro h t le
    apply (good t).mpr
    rw [ht_shift v endpt c _ le, sub_nonneg]
    split
    · next hlt => exact h ⟨_,hlt⟩
    · exact h ⟨_,by omega⟩

private theorem ht_injective (v : Word n b) (cop : Nat.Coprime n b) :
    Function.Injective (fun c : Fin b => ht v c.val) := by
  have ordered {x y : Fin b} (hle : x.val ≤ y.val) (eq : ht v x.val = ht v y.val) : x = y := by
    have dz : (b : ℤ) ∣ (n * (y.val-x.val) : Nat) := by
      refine ⟨(prefixN v y.val : ℤ)-prefixN v x.val, ?_⟩
      unfold ht at eq
      push_cast [Nat.cast_sub hle]
      linarith only [eq]
    have dv := cop.symm.dvd_of_dvd_mul_left (Int.natCast_dvd_natCast.mp dz)
    have z := Nat.eq_zero_of_dvd_of_lt dv (by omega)
    exact Fin.ext (by omega)
  intro x y e
  rcases le_total x.val y.val with le|le
  · exact ordered le e
  · exact (ordered le e.symm).symm

private theorem unique_good (v : Word n b) (endpt : prefixN v b = n) (hb : 0 < b)
    (cop : Nat.Coprime n b) : ∃! c : Fin b, RationalPath (shift c v) := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin b))
    (fun i => ht v i.val) ⟨⟨0,hb⟩,Finset.mem_univ _⟩
  refine ⟨c,(good_iff_min v endpt c).mpr (fun d => hc d (Finset.mem_univ _)),?_⟩
  intro d hd
  exact ht_injective v cop (le_antisymm ((good_iff_min v endpt d).mp hd c) (hc d (Finset.mem_univ _)))

/-- Cutting immediately after the minimum gives exactly one rational path among the b
marked cuts of every word of the specified run type. -/
theorem cycle_count {n b : Nat} (_hn : 0 < n) (hb : 0 < b) (cop : Nat.Coprime n b) (k j : Nat) :
    b * rationalCount n b k j = freeCount n b k j := by
  classical
  let _ : NeZero b := ⟨hb.ne'⟩
  let X := {v : Word n b // Stats v k j}
  let Y := {v : Word n b // Stats v k j ∧ RationalPath v}
  let join (p : Fin b × Y) : X :=
    ⟨shift (-p.1) p.2.val, (stats_shift ..).mpr p.2.property.1⟩
  have undo (u : Word n b) (c : Fin b) : shift c (shift (-c) u) = u := by
    funext i; simp [shift]
  have undo' (u : Word n b) (c : Fin b) : shift (-c) (shift c u) = u := by
    funext i; simp [shift]
  have onto : Function.Surjective join := by
    intro x
    obtain ⟨c, good, _⟩ := unique_good x.val x.property.1 hb cop
    exact ⟨(c,⟨shift c x.val, (stats_shift ..).mpr x.property, good⟩), Subtype.ext (undo' _ _)⟩
  have inj : Function.Injective join := by
    rintro ⟨c,x⟩ ⟨d,y⟩ eq
    have e : shift (-c) x.val = shift (-d) y.val := congrArg Subtype.val eq
    obtain ⟨_,_,uniq⟩ := unique_good (shift (-c) x.val) ((stats_shift ..).mpr x.property.1).1 hb cop
    have hc : RationalPath (shift c (shift (-c) x.val)) := by rw [undo]; exact x.property.2
    have hd : RationalPath (shift d (shift (-c) x.val)) := by rw [e,undo]; exact y.property.2
    have cd := (uniq c hc).trans (uniq d hd).symm
    subst d
    have xy := congrArg (shift c) e
    simp only [undo] at xy
    exact Prod.ext rfl (Subtype.ext xy)
  have card := Fintype.card_congr (Equiv.ofBijective join ⟨inj,onto⟩)
  simpa [X,Y,rationalCount,freeCount,Fintype.card_prod] using card

end FussDyck
