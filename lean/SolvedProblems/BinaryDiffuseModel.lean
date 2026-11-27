module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

open Set MeasureTheory
open scoped unitInterval ENNReal

namespace BinaryDiffuse

/-- The second bandit uses all subsets of the unit interval as measurable sets. -/
def Coord : Type := unitInterval

instance : MeasurableSpace Coord := ⊤
instance : DiscreteMeasurableSpace Coord := inferInstanceAs (@DiscreteMeasurableSpace Coord ⊤)
instance : Uncountable Coord := by
  apply Cardinal.aleph0_lt_mk_iff.mp
  rw [show Cardinal.mk Coord = Cardinal.continuum from Cardinal.mk_unitInterval]
  exact Cardinal.aleph0_lt_continuum

/-- A separate type makes the power-set sigma algebra on arms explicit. -/
def Arm : Type := Coord × Bool

instance : MeasurableSpace Arm := ⊤
instance : DiscreteMeasurableSpace Arm := inferInstanceAs (@DiscreteMeasurableSpace Arm ⊤)

def first (a : Arm) : Coord := Prod.fst a

def winSet (f : Coord → Option Bool) : Set Arm := {a | f (first a) = some (Prod.snd a)}

def Eligible (U : Set Arm) : Prop :=
  U = ∅ ∨ ∃ f : Coord → Option Bool, {x | f x = none}.Countable ∧ U = winSet f

abbrev Strategy (Ω : Type*) := (t : ℕ) → (Fin t → Bool) → Ω → Arm

noncomputable def transcript {Ω : Type*} (A : Strategy Ω) (U : Set Arm) (ω : Ω) :
    (t : ℕ) → Fin t → Bool := by
  classical
  exact Nat.rec (motive := fun t => Fin t → Bool) Fin.elim0
    (fun t history => Fin.snoc history (decide (A t history ω ∈ U)))

def failure {Ω : Type*} (A : Strategy Ω) (m : ℕ) (U : Set Arm) : Set Ω :=
  {ω | U.Nonempty ∧ A m (transcript A U ω m) ω ∉ U}

def Learnable : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ (m : ℕ) (Ω : Type) (_s : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧ ∃ A : Strategy Ω,
        (∀ t h, Measurable (A t h)) ∧ ∀ U, Eligible U → μ (failure A m U) ≤ ε

/-- A countably additive probability on the entire powerset which vanishes
on every singleton. -/
def DiffuseExists : Prop :=
  ∃ μ : Measure Coord, IsProbabilityMeasure μ ∧ ∀ x : Coord, μ {x} = 0

end BinaryDiffuse
