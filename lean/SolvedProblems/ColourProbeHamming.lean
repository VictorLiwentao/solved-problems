module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Push

@[expose] public section

namespace ColourProbe

open SimpleGraph

/-- A single recoloring with changed coordinate `i`. -/
def OneAt {V C : Type*} (i : V) (p q : V → C) : Prop :=
  p i ≠ q i ∧ ∀ j, j ≠ i → p j = q j

theorem OneAt.symm {V C : Type*} {i : V} {p q : V → C} (h : OneAt i p q) : OneAt i q p :=
  ⟨h.1.symm,fun j hj => (h.2 j hj).symm⟩

def hamming (V C : Type*) : SimpleGraph (V → C) where
  Adj p q := ∃ i, OneAt i p q
  symm := ⟨by rintro _ _ ⟨i,hi⟩; exact ⟨i,hi.symm⟩⟩
  loopless := ⟨fun _ ⟨_,h⟩ => h.1 rfl⟩

def Proper {V C : Type*} (G : SimpleGraph V) (p : V → C) : Prop :=
  ∀ ⦃i j⦄, G.Adj i j → p i ≠ p j

abbrev Coloring {V : Type*} (G : SimpleGraph V) (C : Type*) := {p : V → C // Proper G p}

noncomputable instance {V C : Type*} [Fintype V] [Fintype C] (G : SimpleGraph V) : Fintype (Coloring G C) := by
  classical unfold Coloring; infer_instance

def coloringGraph {V : Type*} (G : SimpleGraph V) (C : Type*) : SimpleGraph (Coloring G C) :=
  (hamming V C).comap Subtype.val

theorem neighbor_directions {V C : Type*} {i j : V} {p q r : V → C}
    (hq : OneAt i p q) (hr : OneAt j p r) (hne : q ≠ r) : (hamming V C).Adj q r ↔ i=j := by
  constructor
  · rintro ⟨k,hk⟩
    by_contra hij
    have hi : q i ≠ r i := fun h => hq.1 ((hr.2 i hij).trans h.symm)
    have hj : q j ≠ r j := fun h => hr.1 ((hq.2 j (Ne.symm hij)).trans h)
    have ik : i=k := by by_contra h; exact hi (hk.2 i h)
    have jk : j=k := by by_contra h; exact hj (hk.2 j h)
    exact hij (ik.trans jk.symm)
  · rintro rfl
    have other (a : V) (ha : a ≠ i) : q a = r a := (hq.2 a ha).symm.trans (hr.2 a ha)
    refine ⟨i,?_,other⟩
    intro h
    exact hne (funext fun a => by by_cases ha : a=i; exact ha ▸ h; exact other a ha)

/-- The two common neighbors of opposite endpoints of a two-coordinate
diagonal are its two rectangular corners. -/
theorem opposite_corner {V C : Type*} {i j : V} (hij : i ≠ j) {p q r t : V → C}
    (hq : OneAt i p q) (hr : OneAt j p r) (htq : (hamming V C).Adj q t)
    (htr : (hamming V C).Adj r t) (ht : t ≠ p) : t i = q i ∧ t j = r j := by
  obtain ⟨a,ha⟩ := htq
  obtain ⟨b,hb⟩ := htr
  have prove {i j a b} {p q r t : V → C} (hij : i ≠ j) (hq : OneAt i p q) (hr : OneAt j p r)
      (ha : OneAt a q t) (hb : OneAt b r t) (ht : t ≠ p) : t i = q i := by
    by_contra hne
    have ia : i=a := by by_contra h; exact hne (ha.2 i h).symm
    subst a
    have tj : t j = p j := (ha.2 j hij.symm).symm.trans (hq.2 j (Ne.symm hij)).symm
    have jb : j=b := by
      by_contra h
      exact hr.1 (tj.symm.trans (hb.2 j h).symm)
    subst b
    apply ht
    funext x
    by_cases hx : x=i
    · subst x
      exact (hb.2 i hij).symm.trans (hr.2 i hij).symm
    · exact (ha.2 x hx).symm.trans (hq.2 x hx).symm
  exact ⟨prove hij hq hr ha hb ht,prove hij.symm hr hq hb ha ht⟩

end ColourProbe
