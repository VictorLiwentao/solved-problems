module

public import SolvedProblems.ReluGateCircuit

@[expose] public section

namespace ReluMoments

/-- Optional weight indices allow arbitrary sparse or fully connected
architectures. Repeated indices denote shared parameters. -/
structure IndexedAffine (n p : ℕ) where
  input : Option (Fin p)
  bias : Option (Fin p)
  weight : Fin n → Option (Fin p)

def IndexedAffine.coeff {p : ℕ} (θ : Vector p) (i : Option (Fin p)) : ℝ :=
  i.elim 0 θ

noncomputable def IndexedAffine.instantiate {n p : ℕ} (a : IndexedAffine n p) (θ : Vector p) : GateAffine n :=
  ⟨(coeff θ a.input,coeff θ a.bias),fun i => coeff θ (a.weight i)⟩

def weightExpr {p : ℕ} (i : Option (Fin p)) (f : Network 1 p) : Network 1 p :=
  i.elim (.constant 0) (fun k => .scale k f)

theorem weightExpr_eval {p : ℕ} (i : Option (Fin p)) (f : Network 1 p) (θ : Vector p) (x : ℝ) :
    (weightExpr i f).eval θ (fun _ => x) = IndexedAffine.coeff θ i * f.eval θ (fun _ => x) := by
  cases i <;> simp [weightExpr,IndexedAffine.coeff,Network.eval]

def sumExpr {p : ℕ} : {n : ℕ} → (Fin n → Network 1 p) → Network 1 p
  | 0, _ => .constant 0
  | n+1, f => (sumExpr (Fin.init f)).add (f (Fin.last n))

theorem sumExpr_eval {p n : ℕ} (f : Fin n → Network 1 p) (θ : Vector p) (x : ℝ) :
    (sumExpr f).eval θ (fun _ => x) = ∑ i, (f i).eval θ (fun _ => x) := by
  induction n with
  | zero => simp [sumExpr,Network.eval]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,sumExpr,Network.eval,ih]
    rfl

def IndexedAffine.makeExpr {n p : ℕ} (a : IndexedAffine n p) (v : Fin n → Network 1 p) : Network 1 p :=
  ((weightExpr a.input (.input 0)).add (a.bias.elim (.constant 0) .parameter)).add
    (sumExpr (fun i => weightExpr (a.weight i) (v i)))

theorem IndexedAffine.makeExpr_eval {n p : ℕ} (a : IndexedAffine n p) (v : Fin n → Network 1 p) (θ : Vector p) (x : ℝ) :
    (a.makeExpr v).eval θ (fun _ => x) = (a.instantiate θ).eval x (fun i => (v i).eval θ (fun _ => x)) := by
  simp only [makeExpr,Network.eval,weightExpr_eval,sumExpr_eval,GateAffine.eval,instantiate,Line.value]
  cases a.bias <;> rfl

inductive IndexedCircuit (p : ℕ) : ℕ → Type where
  | empty : IndexedCircuit p 0
  | append {n : ℕ} (prev : IndexedCircuit p n) (a : IndexedAffine n p) : IndexedCircuit p (n+1)

noncomputable def IndexedCircuit.instantiate {n p : ℕ} (b : IndexedCircuit p n) (θ : Vector p) : Circuit n :=
  match b with
  | .empty => .empty
  | .append prev a => .append (prev.instantiate θ) (a.instantiate θ)

def IndexedCircuit.exprs {n p : ℕ} (b : IndexedCircuit p n) : Fin n → Network 1 p :=
  match b with
  | .empty => Fin.elim0
  | .append prev a => Fin.snoc (α:=fun _ => Network 1 p) prev.exprs (.relu (a.makeExpr prev.exprs))

theorem IndexedCircuit.eval_exprs {p n : ℕ} (b : IndexedCircuit p n) (θ : Vector p) (x : ℝ) :
    ∀ i, (b.exprs i).eval θ (fun _ => x) = (b.instantiate θ).values x i := by
  induction b with
  | empty => exact fun i => i.elim0
  | append prev a ih =>
    intro i
    induction i using Fin.lastCases with
    | cast i => simpa only [exprs,instantiate,Circuit.values,Fin.snoc_castSucc] using ih i
    | last =>
      simp only [exprs,instantiate,Circuit.values,Fin.snoc_last,Network.eval,a.makeExpr_eval]
      rw [show (fun i => (prev.exprs i).eval θ (fun _ => x)) = _ from funext ih]

theorem IndexedCircuit.eval_output {p n : ℕ} (b : IndexedCircuit p n) (a : IndexedAffine n p) (θ : Vector p) (x : ℝ) :
    (a.makeExpr b.exprs).eval θ (fun _ => x) = (b.instantiate θ).out (a.instantiate θ) x := by
  rw [a.makeExpr_eval,Circuit.out,show (fun i => (b.exprs i).eval θ (fun _ => x)) = _ from funext (b.eval_exprs θ x)]

end ReluMoments
