module

public import SolvedProblems.EMXModel
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace EMX

theorem in_block {h : Hyp} {x : Point} (hx : x ∈ support h) : x.1 = h.1 := by
  obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hx
  rfl

theorem support_card (h : Hyp) : (support h).card = 2^width h.1 * width h.1 - width h.1 := by
  simp [support, Finset.card_compl, h.2.property, Cell, Row, Col]

theorem support_nonempty (h : Hyp) : (support h).Nonempty := by
  apply Finset.card_pos.mp
  rw [support_card]
  have ht : 0 < width h.1 := by simp [width]
  have hpow : 1 < 2^width h.1 := Nat.one_lt_two_pow ht.ne'
  have := Nat.mul_lt_mul_of_pos_right hpow ht
  omega

theorem support_injective_subset {h k : Hyp} (sub : support h ⊆ support k) : h = k := by
  obtain ⟨x, hx⟩ := support_nonempty h
  have eq := (in_block hx).symm.trans (in_block (sub hx))
  rcases h with ⟨j,H⟩
  rcases k with ⟨i,K⟩
  change j = i at eq
  subst i
  have setEq := Finset.eq_of_subset_of_card_le sub (by rw [support_card, support_card])
  have hc : H.valᶜ = K.valᶜ := Finset.map_injective (Function.Embedding.sigmaMk j) setEq
  have hk : H = K := Subtype.ext (compl_injective hc)
  rw [hk]

/-- Independently choose one hole per column. These are t-tuples of rows from a
2^t-element row set. -/
def onePerColumn {j : ℕ} (f : Col j → Row j) : Holes j :=
  ⟨Finset.univ.image (fun k => (f k,k)), by
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
    simp⟩

theorem onePerColumn_injective (j : ℕ) : Function.Injective (@onePerColumn j) := by
  intro f g h
  have he := congrArg Subtype.val h
  funext i
  have hi : (f i, i) ∈ (onePerColumn (j := j) f).val := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [he] at hi
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
  obtain rfl := congrArg Prod.snd hk
  exact (congrArg Prod.fst hk).symm

def liftMessage {d} (j : ℕ) (v : Message (Cell j) d) : Message Point d :=
  ⟨v.1, fun i => Sigma.mk j (v.2 i)⟩

theorem message_bound (j d : ℕ) :
    Fintype.card (Message (Cell j) d) ≤ (d+1)*(2^width j * width j)^d := by
  classical
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin (d+1), (2^width j * width j)^d := by
      apply Finset.sum_le_sum
      intro l _
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]
      apply Nat.pow_le_pow_right (Nat.mul_pos (by positivity) (by simp [width]))
      omega
    _ = _ := by simp

/-- Counting for a single block, using the complete realizable samples of one
common length. -/
theorem counting_necessary (j d a : ℕ) (D : Fin a → Message Point d → Hyp)
    (hD : Reconstructs d a (2^width j * width j - width j) D) :
    2^(width j * width j) ≤ a*(d+1)*(2^width j * width j)^d := by
  classical
  let H (f : Col j → Row j) : Hyp := ⟨j, onePerColumn f⟩
  have code (f : Col j → Row j) :
      ∃ v : Fin a × Message (Cell j) d, D v.1 (liftMessage j v.2) = H f := by
    let S := support (H f)
    let m := 2^width j * width j - width j
    let e : Fin m ≃ S := (Fintype.equivFinOfCardEq (by simpa [S] using support_card (H f))).symm
    let xs : Fin m → Point := fun i => (e i).val
    obtain ⟨b, w, hw, cov⟩ := hD xs ⟨H f, fun i => (e i).property⟩
    have getCell (i) : ∃ c : Cell j, w.2 i = Sigma.mk j c := by
      obtain ⟨k, hk⟩ := hw i
      rw [hk]
      obtain ⟨c, _, h⟩ := Finset.mem_map.mp (e k).property
      exact ⟨c, h.symm⟩
    let v : Message (Cell j) d := ⟨w.1, fun i => (getCell i).choose⟩
    have wEq : liftMessage j v = w := by
      cases w with
      | mk l f =>
        apply congrArg (Sigma.mk l)
        funext i
        exact (getCell i).choose_spec.symm
    refine ⟨(b,v), ?_⟩
    rw [wEq]
    apply Eq.symm
    apply support_injective_subset
    intro y hy
    obtain ⟨i, hi⟩ := e.surjective (⟨y,hy⟩ : S)
    simpa [xs, hi] using cov i
  have inj : Function.Injective (fun f => (code f).choose) := by
    intro f g he
    have heq : H f = H g := (code f).choose_spec.symm.trans
      ((congrArg (fun v : Fin a × Message (Cell j) d => D v.1 (liftMessage j v.2)) he).trans
        (code g).choose_spec)
    exact onePerColumn_injective j (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
  calc
    _ = Fintype.card (Col j → Row j) := by simp [Col,Row,Nat.pow_mul]
    _ ≤ Fintype.card (Fin a × Message (Cell j) d) := Fintype.card_le_of_injective _ inj
    _ ≤ _ := by
      rw [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (message_bound j d)

theorem noBoundedCompression (d a : ℕ) :
    ∃ m : ℕ, ∀ D : Fin a → Message Point d → Hyp, ¬Reconstructs d a m D := by
  let j := 4*(d+a+1)
  let t := width j
  refine ⟨2^t*t-t, ?_⟩
  intro D h
  have low := counting_necessary j d a D h
  change 2^(t*t) ≤ a*(d+1)*(2^t*t)^d at low
  have upper : a*(d+1)*(2^t*t)^d ≤ 2^(a+(d+1)+(t+t)*d) := by
    rw [Nat.pow_add 2 (a+(d+1)) _, Nat.pow_add 2 a (d+1), Nat.pow_mul 2 (t+t) d, Nat.pow_add 2 t t]
    exact Nat.mul_le_mul (Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le)
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le) _)
  have expLe := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (low.trans upper)
  dsimp [t,width,j] at expLe
  nlinarith only [expLe, Nat.zero_le (d*d), Nat.zero_le (a*a), Nat.zero_le (d*a)]

end EMX
