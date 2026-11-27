module

public import SolvedProblems.PrivateListResample
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrivateList

open MeasureTheory Set
open scoped Classical

theorem avg_comm {I J : Type} [Fintype I] [Fintype J] (f : I → J → ℝ) :
    avg (fun i => avg (f i)) = avg (fun j => avg (fun i => f i j)) := by
  simp only [avg,div_eq_mul_inv,← Finset.sum_mul];rw [Finset.sum_comm];ring

theorem resample_empirical {k m s Ω} [MeasurableSpace Ω] [NeZero m] (A : Rule k s Ω)
    {α β : ℝ} (hα : 0 ≤ α) (pac : PopulationPAC A α β) :
    Empirical (resample (m := m) A) (α+β+s^2/m) := by
  intro t fit
  let E (i : Fin m) := omitted A (t i)
  let bad := {ω | α < risk A t ω}
  let B : Rule k m Ω := resample A
  have prob (t : Sample k s) := A.normalized t
  let q (u : Fin s → Fin m) (i : Fin m) := (A.law (subsample t u)).real (E i)
  have bound (u : Fin s → Fin m) : avg (q u) ≤
      α + (A.law (t ∘ u)).real bad + oneIf (¬Function.Injective u) := by
    by_cases h : Function.Injective u
    · simpa [q,subsample,h,oneIf,E,bad] using avg_omissions A t (A.law (t ∘ u)) hα
    · have le : avg (q u) ≤ 1 := (avg_mono (g := fun _ => (1:ℝ)) (fun i => measureReal_le_one)).trans_eq (avg_const _)
      simp only [oneIf,h,not_false_eq_true,↓reduceIte]
      linarith [measureReal_nonneg (μ := A.law (t ∘ u)) (s := bad)]
  have each (i : Fin m) : omission B t (t i).1 (t i).2 = avg (fun u => q u i) := resample_real A t (E i)
  have av : avg (fun i => omission B t (t i).1 (t i).2) ≤ α+β+s^2/m := by
    calc
      _ = avg (fun u => avg (q u)) := by simp only [each];exact avg_comm _
      _ ≤ _ := avg_mono bound
      _ ≤ _ := by
        rw [avg_add,avg_add,avg_const]
        exact add_le_add (add_le_add_right (pac m (NeZero.pos _) _ fit) α) avg_collision_bound
  change (∑ i, omission B t (t i).1 (t i).2) ≤ _
  simpa only [mul_comm (m:ℝ)] using (div_le_iff₀ (show (0:ℝ) < m by exact_mod_cast NeZero.pos m)).mp
    (show (∑ i, omission B t (t i).1 (t i).2) / m ≤ α+β+s^2/m by simpa [avg] using av)

end PrivateList
