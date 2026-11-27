module

public import SolvedProblems.SphericalEntropyBound
public import SolvedProblems.SphericalEntropyRate

@[expose] public section

open Filter Real

namespace SphericalEntropy

/-- The exact-cardinality existence theorem for spherical designs used by
Bondarenko, Radchenko and Viazovska, stated separately from the rate. -/
def DesignExistence (s : ℕ) : Prop :=
  ∃ C : ℕ, 0<C ∧ ∀ t N : ℕ, C*t^s≤N+1 → ∃ X : Fin (N+1) → Sphere s, IsDesign t X

theorem upper_rate {s : ℕ} (hs : 0<s) (designs : DesignExistence s) {α : ℝ} (ha : 0<α) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, ∃ X : Fin (N+1) → Sphere s,
      lossGap α X ≤ energyGap α X ∧
        |energyGap α X| ≤ exp (-c*(N+1:ℝ)^((s:ℝ)⁻¹)*log (N+1)) := by
  classical
  obtain ⟨C,hC,hex⟩ := designs
  obtain ⟨c,hc,hdeg⟩ := choose_degree hs hC
  obtain ⟨sample,_⟩ := hex 0 0 (by simp [Nat.zero_pow hs])
  let x := sample 0
  let B := 2*exp α/partition α x
  have hB : 0<B := div_pos (by positivity) (partition_pos _ _)
  obtain ⟨A,hfac⟩ := eventually_atTop.mp (factorial_rate ha hB)
  refine ⟨c,hc,?_⟩
  filter_upwards [hdeg A] with N hN
  obtain ⟨t,ht,hsize,hscale⟩ := hN
  obtain ⟨X,hd⟩ := hex t N hsize
  obtain ⟨hle,henergy⟩ := design_gaps ha.le X hd x
  refine ⟨X,hle,henergy.trans (le_trans ?_ (exp_le_exp.mpr hscale))⟩
  have h := hfac (t+1) ht
  have he : 2*(α^(t+1)/((t+1).factorial:ℝ)*exp α)/partition α x = B*α^(t+1)/((t+1).factorial:ℝ) := by
    unfold B
    ring
  simpa [he] using h

end SphericalEntropy
