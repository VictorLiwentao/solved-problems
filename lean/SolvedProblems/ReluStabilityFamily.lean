module

public import SolvedProblems.ReluStabilityOrdered
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

open Set

namespace ReluStability

abbrev Input (d : ℕ) := Fin d → ℝ

structure Family (B X : Type*) [TopologicalSpace B] [TopologicalSpace X] where
  map : B → X ≃ₜ X
  forward : Continuous (fun z : B×X => map z.1 z.2)
  backward : Continuous (fun z : B×X => (map z.1).symm z.2)

def Family.identity (B X : Type*) [TopologicalSpace B] [TopologicalSpace X] : Family B X :=
  ⟨fun _ => Homeomorph.refl _,continuous_snd,continuous_snd⟩

theorem inverse_continuous {B : Type*} [TopologicalSpace B] (G : B → ℝ ≃o ℝ)
    (hg : Continuous (fun z : B×ℝ => G z.1 z.2)) :
    Continuous (fun z : B×ℝ => (G z.1).symm z.2) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have hf : Continuous (fun z : B×ℝ => G z.1 a) := hg.comp (continuous_fst.prodMk continuous_const)
  constructor
  · convert isOpen_lt hf continuous_snd using 1
    ext z
    exact (G z.1).lt_symm_apply
  · convert isOpen_lt continuous_snd hf using 1
    ext z
    exact (G z.1).symm_apply_lt

theorem continuous_cons {B : Type*} [TopologicalSpace B] {d : ℕ} {f : B → ℝ} {g : B → Input d}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun z => Fin.cons (α:=fun _ => ℝ) (f z) (g z)) := by
  apply continuous_pi
  intro j
  induction j using Fin.cases with
  | zero => exact hf
  | succ i => exact (continuous_apply i).comp hg

theorem continuous_tail {d : ℕ} : Continuous (Fin.tail (α:=fun _ => ℝ) : Input (d+1) → Input d) :=
  continuous_pi fun i => continuous_apply i.succ

noncomputable def liftForward {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (b : B) (x : Input (d+1)) : Input (d+1) :=
  Fin.cons (G (b,Fin.tail x) (x 0)) (H.map b (Fin.tail x))

noncomputable def liftBackward {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (b : B) (x : Input (d+1)) : Input (d+1) :=
  let y := (H.map b).symm (Fin.tail x)
  Fin.cons ((G (b,y)).symm (x 0)) y

theorem liftForward_continuous {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (hG : Continuous (fun z : (B×Input d)×ℝ => G z.1 z.2)) :
    Continuous (fun z : B×Input (d+1) => liftForward H G z.1 z.2) := by
  have hy : Continuous (fun z : B×Input (d+1) => (z.1,Fin.tail z.2)) :=
    continuous_fst.prodMk (continuous_tail.comp continuous_snd)
  exact continuous_cons (hG.comp (hy.prodMk ((continuous_apply 0).comp continuous_snd))) (H.forward.comp hy)

theorem liftBackward_continuous {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (hG : Continuous (fun z : (B×Input d)×ℝ => G z.1 z.2)) :
    Continuous (fun z : B×Input (d+1) => liftBackward H G z.1 z.2) := by
  have hy : Continuous (fun z : B×Input (d+1) => (H.map z.1).symm (Fin.tail z.2)) :=
    H.backward.comp (continuous_fst.prodMk (continuous_tail.comp continuous_snd))
  exact continuous_cons ((inverse_continuous _ hG).comp ((continuous_fst.prodMk hy).prodMk
    ((continuous_apply 0).comp continuous_snd))) hy

noncomputable def Family.lift {B : Type*} [TopologicalSpace B] {d : ℕ} (H : Family B (Input d))
    (G : B×Input d → ℝ ≃o ℝ) (hG : Continuous (fun z : (B×Input d)×ℝ => G z.1 z.2)) :
    Family B (Input (d+1)) where
  map b :=
    { toFun := liftForward H G b
      invFun := liftBackward H G b
      left_inv := fun x => by simp [liftForward,liftBackward]
      right_inv := fun x => by simp [liftForward,liftBackward]
      continuous_toFun := (liftForward_continuous H G hG).comp (continuous_const.prodMk continuous_id)
      continuous_invFun := (liftBackward_continuous H G hG).comp (continuous_const.prodMk continuous_id) }
  forward := liftForward_continuous H G hG
  backward := liftBackward_continuous H G hG

end ReluStability
