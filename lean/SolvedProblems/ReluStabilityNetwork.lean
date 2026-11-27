module

public import SolvedProblems.ReluStabilitySweep
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Topology.InductiveDimension.Functions

@[expose] public section

open SignType Set

namespace ReluStability

noncomputable def Form.zero (p d : ℕ) : Form p d := ⟨0,fun _ => 0⟩

noncomputable def Form.add {p d : ℕ} (f g : Form p d) : Form p d :=
  ⟨f.bias+g.bias,fun i => f.weight i+g.weight i⟩

noncomputable def Form.sum {p d : ℕ} : {n : ℕ} → (Fin n → Form p d) → Form p d
  | 0, _ => .zero p d
  | _+1, f => (Form.sum (Fin.tail f)).add (f 0)

theorem Form.eval_sum {p d n : ℕ} (f : Fin n → Form p d) (θ : Params p) (x : Input d) :
    (Form.sum f).eval θ x = ∑ i, (f i).eval θ x := by
  induction n with
  | zero => simp [sum,zero,eval]
  | succ n ih =>
    rw [sum,Fin.sum_univ_succ]
    have add_eval (a b : Form p d) : (a.add b).eval θ x = a.eval θ x+b.eval θ x := by
      simp only [add,eval,map_add,add_mul,Finset.sum_add_distrib]; ring
    rw [add_eval,ih,add_comm]
    rfl

/-- A gate can depend affinely on the inputs and any previous gates, with
arbitrary polynomial functions of the parameters as all its coefficients.
Independent trainable weights, biases, fixed weights and shared weights are included. -/
structure Gate (p d n : ℕ) where
  direct : Form p d
  weight : Fin n → Coeff p

noncomputable def Gate.eval {p d n : ℕ} (a : Gate p d n) (θ : Params p) (x : Input d) (v : Fin n → ℝ) : ℝ :=
  a.direct.eval θ x + ∑ i, MvPolynomial.eval θ (a.weight i) * v i

noncomputable def Gate.form {p d n : ℕ} (a : Gate p d n) (v : Fin n → Form p d) : Form p d :=
  a.direct.add (Form.sum fun i => (v i).scale (a.weight i))

theorem Gate.eval_form {p d n : ℕ} (a : Gate p d n) (v : Fin n → Form p d) (θ : Params p) (x : Input d) :
    (a.form v).eval θ x = a.eval θ x (fun i => (v i).eval θ x) := by
  have ha (b c : Form p d) : (b.add c).eval θ x = b.eval θ x + c.eval θ x := by
    simp only [Form.add,Form.eval,map_add,add_mul,Finset.sum_add_distrib]; ring
  simp only [form,ha,Form.eval_sum,Form.eval_scale,eval]

inductive Model (p d : ℕ) : ℕ → Type where
  | empty : Model p d 0
  | append {n : ℕ} (b : Model p d n) (a : Gate p d n) : Model p d (n+1)

noncomputable def Model.pre {p d n : ℕ} (N : Model p d n) (θ : Params p) (x : Input d) : Fin n → ℝ :=
  match N with
  | .empty => Fin.elim0
  | .append b a => Fin.snoc (α:=fun _ => ℝ) (b.pre θ x) (a.eval θ x (fun i => max (b.pre θ x i) 0))

noncomputable def Model.masked {p d n : ℕ} (N : Model p d n) (σ : Fin n → Bool) : Fin n → Form p d :=
  match N with
  | .empty => Fin.elim0
  | @append _ _ k b a =>
    let v := b.masked (Fin.init σ)
    Fin.snoc (α:=fun _ => Form p d) v (if σ (Fin.last k) then a.form v else Form.zero p d)

noncomputable def Model.tests {p d n : ℕ} (N : Model p d n) : List (Form p d) :=
  match N with
  | .empty => []
  | @append _ _ k b a => b.tests ++ (Finset.univ : Finset (Fin k → Bool)).toList.map (fun σ => a.form (b.masked σ))

def Model.realizes {p d n : ℕ} (N : Model p d n) (σ : Fin n → Bool) (θ : Params p) (x : Input d) :=
  ∀ i, max (N.pre θ x i) 0 = (N.masked σ i).eval θ x

theorem Model.pre_last {p d n : ℕ} (b : Model p d n) (a : Gate p d n) (σ : Fin n → Bool)
    (θ : Params p) (x : Input d) (h : b.realizes σ θ x) :
    (b.append a).pre θ x (Fin.last n) = (a.form (b.masked σ)).eval θ x := by
  simp only [pre,Fin.snoc_last,Gate.eval_form]
  rw [show (fun i => max (b.pre θ x i) 0) = _ from funext h]

theorem Model.realizes_append {p d n : ℕ} (b : Model p d n) (a : Gate p d n) (σ : Fin n → Bool)
    (θ : Params p) (x : Input d) (h : b.realizes σ θ x) (active : Bool)
    (he : max ((a.form (b.masked σ)).eval θ x) 0 =
      (if active then a.form (b.masked σ) else Form.zero p d).eval θ x) :
    (b.append a).realizes (Fin.snoc (α:=fun _ => Bool) σ active) θ x := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [b.pre_last a σ θ x h,masked,Fin.snoc_last,Fin.init_snoc] using he
  | cast i => simpa only [pre,masked,Fin.snoc_castSucc,Fin.init_snoc] using h i

noncomputable def Model.word {p d n : ℕ} (N : Model p d n) (θ : Params p) (x : Input d) : Fin n → SignType :=
  fun i => sign (N.pre θ x i)

theorem Model.aligned_words {p d n : ℕ} (N : Model p d n) (θ η : Params p) (x y : Input d)
    (h : ∀ f ∈ N.tests, sign (f.eval θ x) = sign (f.eval η y)) :
    N.word θ x = N.word η y ∧ ∃ σ, N.realizes σ θ x ∧ N.realizes σ η y := by
  induction N with
  | empty => exact ⟨funext fun i => i.elim0,Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | @append n b a ih =>
    obtain ⟨hw,σ,hx,hy⟩ := ih (fun f hf => h f (List.mem_append_left _ hf))
    have hf := h (a.form (b.masked σ)) (List.mem_append_right _ (List.mem_map.mpr ⟨σ,by simp,rfl⟩))
    constructor
    · funext i
      induction i using Fin.lastCases with
      | last => simpa only [word,b.pre_last a σ θ x hx,b.pre_last a σ η y hy] using hf
      | cast i => simpa only [word,pre,Fin.snoc_castSucc] using congrFun hw i
    · by_cases hp : 0 < (a.form (b.masked σ)).eval θ x
      · have hy' := sign_eq_one_iff.mp (hf ▸ sign_pos hp)
        exact ⟨Fin.snoc σ true,b.realizes_append a σ θ x hx true (max_eq_left hp.le),
          b.realizes_append a σ η y hy true (max_eq_left hy'.le)⟩
      · have hy' : ¬0 < (a.form (b.masked σ)).eval η y := fun hy' =>
          hp (sign_eq_one_iff.mp (hf.trans (sign_pos hy')))
        refine ⟨Fin.snoc σ false,b.realizes_append a σ θ x hx false ?_,b.realizes_append a σ η y hy false ?_⟩
        · rw [max_eq_right (le_of_not_gt hp)]; simp [Form.zero,Form.eval]
        · rw [max_eq_right (le_of_not_gt hy')]; simp [Form.zero,Form.eval]

/-- The full ternary sign cell, including units exactly at zero. -/
def Model.cell {p d n : ℕ} (N : Model p d n) (θ : Params p) (s : Fin n → SignType) : Set (Input d) :=
  {x | N.word θ x = s}

end ReluStability
