module

public import SolvedProblems.ColourProbeFibers
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace ColourProbe

open SimpleGraph Polynomial

noncomputable def fullCount {U V : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (j : ℕ) :=
  Nat.card (Full H G (Fin j))

theorem no_full {U V : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V)
    {j : ℕ} (hj : Fintype.card U * Fintype.card V < j) : fullCount H G j = 0 := by
  have _ : IsEmpty (Full H G (Fin j)) := ⟨fun f => by
    let g (p : U × V) := (f.val p.1).val p.2
    have sur : Function.Surjective g := by
      intro c
      obtain ⟨u,i,h⟩ := f.property c
      exact ⟨(u,i),h⟩
    have bound := Fintype.card_le_of_surjective g sur
    simp at bound
    omega⟩
  simp [fullCount]

/-- Expansion in the binomial basis: first choose the set of colors actually
used, then a palette-surjective labeled embedding. No embedding uses more
colors than the number of entries in its matrix of colorings. -/
theorem labelled_binomial {U V : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V) (k : ℕ) :
    Nat.card (H ↪g coloringGraph G (Fin k)) =
      ∑ j ∈ Finset.range (Fintype.card U*Fintype.card V+1), k.choose j * fullCount H G j := by
  classical
  let n := Fintype.card U * Fintype.card V
  let _ := Fintype.ofFinite (H ↪g coloringGraph G (Fin k))
  let _ (S : Finset (Fin k)) := Fintype.ofFinite {e : H ↪g coloringGraph G (Fin k) // used e=S}
  have fibers (S : Finset (Fin k)) : Fintype.card {e : H ↪g coloringGraph G (Fin k) // used e=S} = fullCount H G S.card := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr ((usedFiber H G S).trans (fullEquiv H G (Fintype.equivFinOfCardEq (Fintype.card_coe S))))
  have base : Nat.card (H ↪g coloringGraph G (Fin k)) = ∑ S : Finset (Fin k), fullCount H G S.card := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun e : H ↪g coloringGraph G (Fin k) => used e)),
      Nat.card_eq_fintype_card,Fintype.card_sigma]
    exact Finset.sum_congr rfl fun S _ => fibers S
  let m := max k n+1
  have bound (S : Finset (Fin k)) : S.card ∈ Finset.range m :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.card_le_univ S).trans (by simp)))
  have card (j : ℕ) : ((Finset.univ : Finset (Finset (Fin k))).filter (fun S => S.card=j)).card = k.choose j := by
    have eq : (Finset.univ : Finset (Finset (Fin k))).filter (fun S => S.card=j) = Finset.univ.powersetCard j := by
      ext; simp
    simp [eq,Finset.card_powersetCard]
  rw [base,← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset (Fin k)))) (t := Finset.range m)
    (g := Finset.card) (fun S _ => bound S)]
  calc
    _ = ∑ j ∈ Finset.range m, k.choose j * fullCount H G j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← card j]
      exact Finset.sum_const_nat fun S h => by rw [(Finset.mem_filter.mp h).2]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (le_max_right k n)))
      intro j _ hj
      have gt : n < j := by simpa using hj
      simp [no_full H G gt]

/-- The induced-copy polynomial has rational coefficients because the labeled
binomial-basis count is divided by the finite automorphism count of the probe. -/
noncomputable def countPolynomial {U V : Type*} [Fintype U] [Fintype V]
    (H : SimpleGraph U) (G : SimpleGraph V) : ℚ[X] :=
  C (Nat.card (H ≃g H) : ℚ)⁻¹ * ∑ j ∈ Finset.range (Fintype.card U*Fintype.card V+1),
    C ((fullCount H G j : ℚ) / j.factorial) * descPochhammer ℚ j

theorem countPolynomial_eval {U V : Type*} [Fintype U] [Fintype V] (H : SimpleGraph U) (G : SimpleGraph V) (k : ℕ) :
    (countPolynomial H G).eval (k : ℚ) = inducedCount H (coloringGraph G (Fin k)) := by
  classical
  have _ : Finite (H ≃g H) := Finite.of_injective (fun e : H ≃g H => (e : U → U)) DFunLike.coe_injective
  have _ : Nonempty (H ≃g H) := ⟨RelIso.refl _⟩
  have nz : (Nat.card (H ≃g H) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h := (labelled_binomial H G k).symm.trans (embeddings_count H (coloringGraph G (Fin k)))
  have hq := congrArg (fun n : ℕ => (n : ℚ)) h
  push_cast at hq
  simp only [countPolynomial,eval_mul,eval_C,eval_finsetSum]
  calc
    _ = (Nat.card (H ≃g H) : ℚ)⁻¹ * ∑ j ∈ Finset.range (Fintype.card U*Fintype.card V+1),
        (k.choose j : ℚ) * fullCount H G j := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.cast_choose_eq_descPochhammer_div]
      ring
    _ = _ := by rw [hq]; field_simp

/-- The conjecture stated using literal polynomial equality, for all finite
simple targets and hosts and with the explicit connected probe size bound. -/
theorem polynomial_reconstruction {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ (U : Type) (_ : Fintype U) (H : SimpleGraph U), H.Connected ∧
      Fintype.card U ≤ 1 + Fintype.card V*(Fintype.card V+1) + (Fintype.card V).choose 2*(Fintype.card V+1)^2 ∧
      ∀ (W : Type) [Fintype W] (K : SimpleGraph W), countPolynomial H G = countPolynomial H K → Nonempty (G ≃g K) := by
  obtain ⟨U,fin,H,con,bnd,h⟩ := one_colouring_probe G
  refine ⟨U,fin,H,con,bnd,fun W _ K hk => h W K fun k => ?_⟩
  have e := congrArg (Polynomial.eval (k : ℚ)) hk
  rw [countPolynomial_eval,countPolynomial_eval] at e
  exact_mod_cast e

end ColourProbe
