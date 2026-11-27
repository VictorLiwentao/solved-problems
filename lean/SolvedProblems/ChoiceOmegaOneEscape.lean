module

public import SolvedProblems.ChoiceOmegaOneProduct
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Fintype.Perm

@[expose] public section

noncomputable section
namespace ChoiceOmegaOne

open Set Subgroup
open scoped commutatorElement

variable {G : Type u} [Group G] {V : Type v} [MulAction G V]

/-- Setwise stabilizer written with membership to make the restricted action
and its inverse explicit. -/
def respects (S : Set V) : Subgroup G where
  carrier := {g | ∀ v, g • v ∈ S ↔ v ∈ S}
  one_mem' _ := by rw [one_smul]
  mul_mem' {a b} ha hb v := by rw [mul_smul]; exact (ha _).trans (hb v)
  inv_mem' {a} ha v := by simpa only [smul_inv_smul] using (ha (a⁻¹ • v)).symm

def permOn (S : Set V) : respects (G := G) S →* Equiv.Perm S where
  toFun g := (MulAction.toPerm g.val).subtypeEquiv (p := fun v => v∈S) (q := fun v => v∈S) (fun v => (g.property v).symm)
  map_one' := Equiv.ext (fun v => Subtype.ext (one_smul G v.val))
  map_mul' a b := Equiv.ext (fun v => Subtype.ext (mul_smul a.val b.val v.val))

/-- If an image of a perfect group is nontrivial, two elements of that image
do not commute. This uses only generation by commutators. -/
theorem noncommuting_image {H : Type u} [Group H] {K : Type v} [Group K] (φ : H →* K)
    (perfect : commutator H = ⊤) (nontriv : ∃ p, φ p ≠ 1) : ∃ a b, ¬ Commute (φ a) (φ b) := by
  classical
  by_contra! comm
  have ker : commutator H ≤ φ.ker := by
    rw [commutator_eq_closure]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨a,b,rfl⟩
    exact (map_commutatorElement _ _ _).trans (commutatorElement_eq_one_iff_commute.mpr (comm a b))
  obtain ⟨p,hp⟩ := nontriv
  exact hp (ker (perfect ▸ (show p ∈ (⊤ : Subgroup H) from trivial)))

/-- Commuting with a finite subgroup transports membership in its orbit at the
base point to membership at every point of that orbit. -/
private theorem transports (L : Subgroup G) (x : V) {a : G}
    (comm : ∀ h ∈ L, Commute a h) (mem : a • x ∈ MulAction.orbit L x)
    {y : V} (hy : y ∈ MulAction.orbit L x) : a • y ∈ MulAction.orbit L x := by
  obtain ⟨h,rfl⟩ := MulAction.mem_orbit_iff.mp hy
  change a • (h.val • x) ∈ _
  rw [← mul_smul,(comm h.val h.property).eq,mul_smul]
  exact MulAction.mem_orbit_of_mem_orbit h mem

/-- Infinitely many commuting positive blocks of perfect groups cannot all
have their commutators confined to a preassigned finite orbit. -/
theorem escape {H : ℕ → Type w} [∀ n, Group (H n)] (φ : ∀ n, H n →* G)
    (perfect : ∀ n, commutator (H n) = ⊤)
    (cross : ∀ i j, i ≠ j → ∀ a b, Commute (φ i a) (φ j b)) (L : Subgroup G) [Finite L] (x : V)
    (pos : ∀ n, ∃ h, φ n h • x ≠ x) (central : ∀ n h k, k ∈ L → Commute (φ n h) k) :
    ∃ (n : ℕ) (a b : H n), φ n ⁅a,b⁆ • x ∉ MulAction.orbit L x := by
  classical
  by_contra! confined
  let S := MulAction.orbit L x
  have fin : Finite S := Finite.of_surjective (fun h : L => (⟨h • x,MulAction.mem_orbit x h⟩ : S)) (by
    intro y; obtain ⟨h,eq⟩ := MulAction.mem_orbit_iff.mp y.property; exact ⟨h,Subtype.ext eq⟩)
  have maps (n : ℕ) (h : H n) : φ n h ∈ respects (G := G) S := by
    have inc : commutator (H n) ≤ (respects (G := G) S).comap (φ n) := by
      rw [commutator_eq_closure]
      apply (Subgroup.closure_le _).2
      rintro _ ⟨a,b,rfl⟩
      intro v
      constructor
      · intro hv
        have back := transports L x (central n ⁅b,a⁆) (confined n b a) hv
        have e : φ n ⁅b,a⁆ = (φ n ⁅a,b⁆)⁻¹ := by rw [← map_inv,commutatorElement_inv]
        simpa only [e,inv_smul_smul] using back
      · exact transports L x (central n ⁅a,b⁆) (confined n a b)
    exact inc ((perfect n) ▸ (show h ∈ (⊤ : Subgroup (H n)) from trivial))
  let ψ (n : ℕ) := (permOn (G := G) S).comp ((φ n).codRestrict (respects S) (maps n))
  have nontriv (n : ℕ) : ∃ h, ψ n h ≠ 1 := by
    obtain ⟨h,move⟩ := pos n
    refine ⟨h,fun eq => move ?_⟩
    exact congrArg (fun e : Equiv.Perm S => (e ⟨x,MulAction.mem_orbit_self x⟩).val) eq
  choose a b ne using fun n => noncommuting_image (ψ n) (perfect n) (nontriv n)
  have collision : ¬ Function.Injective (fun n => ψ n (a n)) := by
    intro inj
    let _ := Finite.of_injective _ inj
    exact _root_.not_finite ℕ
  obtain ⟨i,j,same,diff⟩ := Function.not_injective_iff.mp collision
  apply ne j
  rw [← same]
  apply Equiv.ext
  intro y
  apply Subtype.ext
  change φ i (a i) • (φ j (b j) • y.val) = φ j (b j) • (φ i (a i) • y.val)
  rw [← mul_smul,← mul_smul,(cross i j diff (a i) (b j)).eq]

end ChoiceOmegaOne
