module

public import SolvedProblems.PromptBoundSelectWords
public import SolvedProblems.PromptBoundAlgorithms

public section
namespace PromptBound.Selector

/-- Test whether a word is unseen and extends the current prompt. -/
def matchesPrompt {q} (S : List (Word q)) (p y : Word q) : Bool :=
  !present S y && starts p y

theorem matchesPrompt_iff {q} (S : List (Word q)) (p y : Word q) :
    matchesPrompt S p y = true ↔ y ∉ S ∧ p.IsPrefix y := by
  simp [matchesPrompt, Bool.eq_false_iff]

def initialPool {q} (S : List (Word q)) (p : Word q) (b : ℕ) :=
  (words q b).filter (matchesPrompt S p)

theorem mem_pool {q} {S : List (Word q)} {p y : Word q} {b : ℕ} :
    y ∈ initialPool S p b ↔ y.length ≤ b ∧ y ∉ S ∧ p.IsPrefix y := by
  simp [initialPool, mem_words, matchesPrompt_iff]

/-- Apply the next consistent candidate only if it leaves a nonempty pool. -/
def narrow {q} (K : Word q → Bool) (S F : List (Word q)) :=
  if S.all K = true ∧ F.filter K ≠ [] then F.filter K else F

theorem narrow_sub {q} (K : Word q → Bool) (S F : List (Word q)) :
    narrow K S F ⊆ F := by unfold narrow; split <;> simp_all

theorem narrow_nonempty {q} (K : Word q → Bool) (S : List (Word q)) {F : List (Word q)}
    (hne : F ≠ []) : narrow K S F ≠ [] := by unfold narrow; split <;> simp_all

def pool {q} (C : Family q) (S F : List (Word q)) : ℕ → List (Word q)
  | 0 => F
  | j+1 => narrow (C j) S (pool C S F j)

theorem pool_sub {q} (C : Family q) (S F : List (Word q)) {i j : ℕ} (h : i≤j) :
    pool C S F j ⊆ pool C S F i := by
  induction j, h using Nat.le_induction with
  | base => rfl
  | succ j _ ih => exact fun _ hy ↦ ih (narrow_sub (C j) S (pool C S F j) hy)

theorem pool_nonempty {q} (C : Family q) (S : List (Word q)) {F : List (Word q)}
    (hne : F ≠ []) (t : ℕ) : pool C S F t ≠ [] := by
  induction t with
  | zero => exact hne
  | succ t ih => exact narrow_nonempty _ _ ih

/-- Once all earlier consistent hypotheses contain the target, its bounded fresh witness
survives until the true index is inspected. Thereafter every surviving output is in it. -/
theorem pool_correct {q} (C : Family q) (S F : List (Word q)) {z t : ℕ} (ht : z < t)
    (hS : ∀ w∈S, C z w = true) (earlier : ∀ j < z, (∀ w∈S, C j w = true) →
      ∀ w, C z w = true → C j w = true)
    (hit : ∃ y ∈ F, C z y = true) :
    pool C S F t ≠ [] ∧ ∀ y ∈ pool C S F t, y ∈ F ∧ C z y = true := by
  obtain ⟨w,hw,hk⟩ := hit
  have survive : ∀ j ≤ z, w ∈ pool C S F j := by
    intro j
    induction j with
    | zero => exact fun _ ↦ hw
    | succ j ih =>
      intro hj
      have old := ih (by omega)
      unfold pool narrow
      split
      next h => exact List.mem_filter.mpr ⟨old,earlier j (by omega) (List.all_eq_true.mp h.1) _ hk⟩
      next => exact old
  have hz := survive z le_rfl
  have keep : (pool C S F z).filter (C z) ≠ [] := by
    have m := List.mem_filter.mpr (show w∈pool C S F z ∧ C z w = true from ⟨hz,hk⟩)
    exact List.ne_nil_of_mem m
  have after : pool C S F (z+1) = (pool C S F z).filter (C z) := by
    simp [pool,narrow,List.all_eq_true.mpr hS,keep]
  refine ⟨pool_nonempty _ _ (List.ne_nil_of_mem hw) _,fun y hy ↦ ⟨?_,?_⟩⟩
  · exact pool_sub C S F (Nat.zero_le t) hy
  · have m := pool_sub C S F ht hy
    rw [after] at m
    exact (List.mem_filter.mp m).2

variable {X : Oracle}
@[fun_prop] theorem eff_matchesPrompt {q} :
    Effective X (fun v : (List (Word q) × Word q) × Word q ↦ matchesPrompt v.1.1 v.1.2 v.2) := by
  unfold matchesPrompt
  fun_prop

@[fun_prop] theorem eff_initialPool {q} :
    Effective X (fun v : (List (Word q) × Word q) × ℕ ↦ initialPool v.1.1 v.1.2 v.2) := by
  unfold initialPool
  exact eff_filter (X:=X) (α:=(List (Word q) × Word q) × ℕ) (f:=fun v ↦ words q v.2) (g:=fun u ↦ matchesPrompt u.1.1.1 u.1.1.2 u.2)
    (by fun_prop) (.comp (f:=fun u : ((List (Word q) × Word q) × ℕ) × Word q ↦ (u.1.1,u.2)) eff_matchesPrompt (by fun_prop))

theorem eff_narrow {q} (C : Family q) (mem : Computable (fun u : ℕ × Word q ↦ C u.1 u.2)) :
    Effective X (fun v : (ℕ × List (Word q)) × List (Word q) ↦ narrow (C v.1.1) v.1.2 v.2) := by
  have cm : Effective X (fun u : ℕ × Word q ↦ C u.1 u.2) := .basic mem
  have all : Effective X (fun v : (ℕ × List (Word q)) × List (Word q) ↦ v.1.2.all (C v.1.1)) :=
    eff_all (X:=X) (α:=(ℕ × List (Word q)) × List (Word q)) (f:=fun v ↦ v.1.2) (g:=fun u ↦ C u.1.1.1 u.2) (by fun_prop) (.comp (f:=fun u : ((ℕ × List (Word q)) × List (Word q)) × Word q ↦ (u.1.1.1,u.2)) cm (by fun_prop))
  have filt : Effective X (fun v : (ℕ × List (Word q)) × List (Word q) ↦ v.2.filter (C v.1.1)) :=
    eff_filter (X:=X) (α:=(ℕ × List (Word q)) × List (Word q)) (f:=Prod.snd) (g:=fun u ↦ C u.1.1.1 u.2) (by fun_prop) (.comp (f:=fun u : ((ℕ × List (Word q)) × List (Word q)) × Word q ↦ (u.1.1.1,u.2)) cm (by fun_prop))
  let pick (v : (ℕ × List (Word q)) × List (Word q)) :=
    bif v.1.2.all (C v.1.1) && !(decide (v.2.filter (C v.1.1) = []))
    then v.2.filter (C v.1.1) else v.2
  have hpick : Effective X pick := by unfold pick; fun_prop
  convert hpick using 1
  funext v
  simp [pick,narrow,Bool.cond_eq_ite]

theorem eff_pool {q} (C : Family q) (mem : Computable (fun u : ℕ × Word q ↦ C u.1 u.2)) :
    Effective X (fun v : (List (Word q) × List (Word q)) × ℕ ↦ pool C v.1.1 v.1.2 v.2) := by
  have step := eff_narrow (X:=X) C mem
  have hh : Effective X (fun v : (List (Word q) × List (Word q)) × ℕ ↦ Nat.rec (motive:=fun _ ↦ List (Word q)) v.1.2
      (fun j l ↦ narrow (C j) v.1.1 l) v.2) :=
    .recNat (α:=(List (Word q) × List (Word q)) × ℕ) (n:=Prod.snd) (z:=fun v ↦ v.1.2) (g:=fun i ↦ narrow (C i.1.2) i.1.1.1.1 i.2)
      (by fun_prop) (by fun_prop) (.comp (f:=fun v : (((List (Word q) × List (Word q)) × ℕ) × ℕ) × List (Word q) ↦ ((v.1.2,v.1.1.1.1),v.2)) step (by fun_prop))
  convert hh using 1
  funext v
  rcases v with ⟨⟨S,F⟩,n⟩
  induction n with
  | zero => rfl
  | succ n ih => simp [pool,ih]

end PromptBound.Selector
