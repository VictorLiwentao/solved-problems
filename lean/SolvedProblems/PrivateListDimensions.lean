module

public import SolvedProblems.PrivateListModel
import Mathlib.Data.Fin.Basic

@[expose] public section

namespace PrivateList

open scoped Classical

def spike {k} (x : Point) (y : Label k) : Hyp k :=
  fun z => if z = x then y else 0

theorem spike_valid {k} (x : Point) (y : Label k) : Valid (spike x y) := by
  have loc {z} (hz : spike x y z ≠ 0) : z = x := by
    by_contra h
    exact hz (by simp [spike,h])
  refine ⟨(Set.finite_singleton x).subset (fun _ h => loc h), ?_, ?_⟩
  · intro z w nz lt
    have nw : spike x y w ≠ 0 := by
      intro hf
      rw [hf] at lt
      exact (Nat.not_lt_zero _ lt)
    have eq := (loc nz).trans (loc nw).symm
    rw [eq] at lt; exact (lt_irrefl _ lt).elim
  · intro z w ne nz eq
    exact (ne ((loc nz).trans (loc (eq ▸ nz)).symm)).elim

def first {k} (hk : 2 ≤ k) : Label k := ⟨1, by omega⟩
def second {k} (hk : 2 ≤ k) : Label k := ⟨2, by omega⟩

/-- After the first mistaken prediction of a list excluding 2, omit 2 strictly
southwest of its point and omit 1 at all other points. -/
noncomputable def omittedAfter {k} (hk : 2 ≤ k) (z x : Point) : Label k :=
  if SW x z then second hk else first hk

theorem safe_after {k} (hk : 2 ≤ k) {h : Hyp k} (hv : Valid h) {z}
    (hz : h z = second hk) (x : Point) : h x ≠ omittedAfter hk z x := by
  classical
  unfold omittedAfter
  by_cases sw : SW x z
  · rw [ite_eq_left sw]
    intro hx
    have nx : x ≠ z := by rintro rfl; exact (Nat.lt_irrefl _ sw.1)
    have comp := hv.2.2 x z nx (by simp [hx,second,Fin.ext_iff]) (hx.trans hz.symm)
    simp only [hx,second,ite_true] at comp
    obtain ⟨h1,h2⟩ := sw
    rcases comp with ⟨_,h⟩ | ⟨h,_⟩ <;> omega
  · rw [ite_eq_right sw]
    intro hx
    exact sw (hv.2.1 x z (by simp [hx,first,Fin.ext_iff]) (by rw [hx,hz]; exact Nat.lt_succ_self 1))

theorem littlestone_upper {k} (hk : 2 ≤ k) (n : ℕ) : ¬LittlestoneDepth k (n+2) := by
  classical
  rintro ⟨T, ht⟩
  let z := T []
  let v := T [second hk]
  let path : Fin (n+2) → Label k := Fin.cases (second hk) (fun _ => omittedAfter hk z v)
  obtain ⟨h,hv,ans⟩ := ht path
  have root : h z = second hk := by simpa [z,path] using ans 0
  have child : h v = omittedAfter hk z v := by
    have h1 := ans (Fin.succ (0 : Fin (n+1)))
    rw [show path (Fin.succ (0 : Fin (n+1))) = omittedAfter hk z v from rfl] at h1
    simpa [v,path,List.ofFn_succ] using h1
  exact safe_after hk hv root v child

theorem monotone_upper {k} (hk : 2 ≤ k) (n : ℕ) : ¬MonotoneLength k (n+2) := by
  classical
  rintro ⟨x, hi, π, hπ⟩
  let i : Fin (n+2) := 0
  let j : Fin (n+2) := (0 : Fin (n+1)).succ
  have ne : x i ≠ x j := fun he => (by decide : 0 ≠ 1) (congrArg Fin.val (hi he))
  have constant (v : Label k) : ∃ h : Hyp k, Valid h ∧ ∀ i, h (x i) = v := by
    obtain ⟨h, hv, h'⟩ := hπ (fun _ => π.symm v) monotone_const
    exact ⟨h,hv,by simpa using h'⟩
  obtain ⟨a,ha,fa⟩ := constant (first hk)
  obtain ⟨b,hb,fb⟩ := constant (second hk)
  have s := ha.2.2 _ _ ne (by simp [fa,first,Fin.ext_iff]) ((fa i).trans (fa j).symm)
  have o := hb.2.2 _ _ ne (by simp [fb,second,Fin.ext_iff]) ((fb i).trans (fb j).symm)
  simp [fa,first] at s
  simp [fb,second] at o
  rcases s with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases o with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;> omega

/-- Both list dimensions on the finite-support planar class are exactly one. -/
theorem dimensionOne (k : ℕ) (hk : 2 ≤ k) : ∀ n : ℕ,
    (LittlestoneDepth k n ↔ n ≤ 1) ∧ (MonotoneLength k n ↔ n ≤ 1) := by
  intro n
  have small {n} (hn : n ≤ 1) : LittlestoneDepth k n ∧ MonotoneLength k n := by
    let x : Point := (0,0)
    have doFit (f : Fin n → Label k) : ∃ h : Hyp k, Valid h ∧ ∀ i, h x = f i := by
      cases n with
      | zero => exact ⟨spike x 0,spike_valid _ _,fun i => i.elim0⟩
      | succ a =>
        have h0 : a = 0 := by omega
        subst a
        exact ⟨spike x (f 0), spike_valid _ _, fun i => by have hi : i = 0 := Fin.ext (by omega); simp [spike,hi]⟩
    constructor
    · exact ⟨fun _ => x,fun f => doFit f⟩
    · refine ⟨fun _ => x, fun i j _ => Fin.ext (by omega), Equiv.refl _,fun f _ => doFit f⟩
  by_cases hn : n ≤ 1
  · exact ⟨iff_of_true (small hn).1 hn,iff_of_true (small hn).2 hn⟩
  · obtain ⟨q,rfl⟩ : ∃ q, n = q+2 := ⟨n-2,by omega⟩
    exact ⟨iff_of_false (littlestone_upper hk q) hn,iff_of_false (monotone_upper hk q) hn⟩

end PrivateList
