module

public import SolvedProblems.RationalReturnsBounds
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Multiset.Sort

@[expose] public section

namespace RationalReturns

def bag {t : ℕ} (w : Fin t → ℕ) : Multiset ℕ := ↑(List.ofFn w)

def less (s : Multiset ℕ) (c : ℕ) := (s.filter (· < c)).card

@[simp] theorem card_bag {t} (w : Fin t → ℕ) : (bag w).card = t := by simp [bag]
@[simp] theorem mem_bag {t} {w : Fin t → ℕ} {x : ℕ} : x ∈ bag w ↔ ∃ q, w q = x := by
  simp [bag, List.mem_ofFn']

theorem less_bag {t} (w : Fin t → ℕ) (c : ℕ) :
    less (bag w) c = (Finset.univ.filter (fun q => w q < c)).card := by
  unfold less bag
  rw [← Fin.univ_val_map, Multiset.filter_map, Multiset.card_map]
  rfl

theorem less_le_card (s : Multiset ℕ) (c : ℕ) : less s c ≤ s.card :=
  Multiset.card_le_card (Multiset.filter_le _ _)

@[simp] theorem less_add (s t : Multiset ℕ) (c : ℕ) : less (s+t) c = less s c + less t c := by
  simp [less]
theorem less_val (s : Finset ℕ) (c : ℕ) : less s.val c = before s c := rfl

/-- In a sorted word the steps before any given column form an initial interval. -/
theorem lt_less_iff {t} {w : Fin t → ℕ} (hw : Monotone w) (q : Fin t) (c : ℕ) :
    q.val < less (bag w) c ↔ w q < c := by
  rw [less_bag]
  let s := Finset.univ.filter (fun z => w z < c)
  constructor
  · intro h
    by_contra! hq
    have sub : s ⊆ Finset.Iio q := by
      intro z hz
      by_contra! hn
      have hqz : q ≤ z := by simpa using hn
      exact (not_lt.mpr ((hw hqz).trans' hq)) (Finset.mem_filter.mp hz).2
    have hc := Finset.card_le_card sub
    rw [Fin.card_Iio] at hc
    exact (not_lt.mpr hc) h
  · intro h
    have sub : Finset.Iic q ⊆ s := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hw (Finset.mem_Iic.mp hz)).trans_lt h⟩
    have hc := Finset.card_le_card sub
    rw [Fin.card_Iic] at hc
    exact hc

theorem less_bound {t} {w : Fin t → ℕ} (hw : Monotone w) {c h : ℕ} (hh : h ≤ t) :
    h ≤ less (bag w) c ↔ ∀ q : Fin t, q.val < h → w q < c := by
  constructor
  · exact fun e q hq => (lt_less_iff hw q c).mp (hq.trans_le e)
  · intro all
    by_contra! fail
    let q : Fin t := ⟨less (bag w) c,fail.trans_le hh⟩
    exact (Nat.lt_irrefl _) ((lt_less_iff hw q c).mpr (all q fail))

/-- The increasing listing of a multiset of prescribed size. -/
def sortedWord {t : ℕ} (s : Multiset ℕ) (hs : s.card = t) (q : Fin t) : ℕ :=
  (s.sort (· ≤ ·))[q.val]'(by simp [hs])

theorem sorted_mono {t} (s : Multiset ℕ) (hs : s.card = t) : Monotone (sortedWord s hs) := by
  intro a b h
  rcases lt_or_eq_of_le h with lt|rfl
  · exact (List.pairwise_iff_getElem.mp (s.pairwise_sort (· ≤ ·))) _ _ _ _ lt
  · rfl

@[simp] theorem bag_sorted {t} (s : Multiset ℕ) (hs : s.card = t) : bag (sortedWord s hs) = s := by
  subst t
  have eq : List.ofFn (sortedWord s rfl) = s.sort (· ≤ ·) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp [sortedWord]
  rw [bag,eq,Multiset.sort_eq]

theorem bag_inj {t} {v w : Fin t → ℕ} (hv : Monotone v) (hw : Monotone w)
    (eq : bag v = bag w) : v = w := by
  apply List.ofFn_injective
  exact (Multiset.coe_eq_coe.mp eq).eq_of_pairwise'
    (List.pairwise_ofFn.mpr (fun _ _ h => hv h.le)) (List.pairwise_ofFn.mpr (fun _ _ h => hw h.le))

end RationalReturns
