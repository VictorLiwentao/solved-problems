module

public import SolvedProblems.EDMRows
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace EDMRows
variable {A : Type*}

/-- Swap every point of D with its distinct image outside D, fixing the rest. -/
noncomputable def exchangeFun (D : Set A) (e : D ↪ A) (x : A) : A := by
  classical
  exact if hx : x ∈ D then e ⟨x,hx⟩ else if hr : x ∈ Set.range e then hr.choose.val else x

theorem exchange_left {D : Set A} (e : D ↪ A) (a : D) : exchangeFun D e a.val = e a :=
  dite_eq_left a.property

theorem exchange_right {D : Set A} (e : D ↪ A) (fresh : ∀ a, e a ∉ D) (a : D) :
    exchangeFun D e (e a) = a.val := by
  classical
  have hr : e a ∈ Set.range e := ⟨a,rfl⟩
  unfold exchangeFun
  rw [dite_eq_right (fresh a),dite_eq_left hr]
  exact congrArg Subtype.val (e.injective hr.choose_spec)

theorem exchange_outside {D : Set A} (e : D ↪ A) {x : A} (hd : x ∉ D) (hr : x ∉ Set.range e) :
    exchangeFun D e x = x := by classical exact (dite_eq_right hd).trans (dite_eq_right hr)

theorem exchange_involutive {D : Set A} (e : D ↪ A) (fresh : ∀ a, e a ∉ D) :
    Function.Involutive (exchangeFun D e) := by
  classical
  intro x
  by_cases h : x ∈ D
  · exact (congrArg (exchangeFun D e) (exchange_left e ⟨x,h⟩)).trans (exchange_right e fresh _)
  by_cases hr : x ∈ Set.range e
  · obtain ⟨a,rfl⟩ := hr
    rw [exchange_right e fresh a,exchange_left]
  · rw [exchange_outside e h hr,exchange_outside e h hr]

noncomputable def exchange {D : Set A} (e : D ↪ A) (fresh : ∀ a, e a ∉ D) : Equiv.Perm A :=
  (exchange_involutive e fresh).toPerm _

variable {I : TallIdeal ℕ}

/-- For two small row supports, conjugation by a permutation fixing T moves
the entire part S∖T off the moved set of g. -/
private theorem clear_row {S T : Set ℕ} (hs : I.small S) (ht : I.small T) (g : rowGroup I)
    (overlap : ∀ a ∈ S ∩ T, g.val a = a) :
    ∃ τ : rowGroup I, (∀ a ∈ T, τ.val a = a) ∧ ∀ a ∈ S, g.val (τ.val a) = τ.val a := by
  classical
  let D := S \ T
  let avoid := (S ∪ T) ∪ moved g.val
  have small : I.small avoid := I.union (I.union hs ht) g.property
  obtain ⟨R,empty,inf,hr⟩ := I.fresh_reserve small
  let := inf.to_subtype
  let embed := Infinite.natEmbedding R
  let e : D ↪ ℕ := ⟨fun a => (embed a.val).val,fun a b h => Subtype.ext (embed.injective (Subtype.ext h))⟩
  have inside (a : D) : e a ∈ R := (embed a.val).property
  have fresh (a : D) : e a ∉ D := fun hd => empty (inside a) (Or.inl (Or.inl hd.1))
  let σ := exchange e fresh
  have permitted : σ ∈ rowGroup I := by
    apply I.down (T := S ∪ R) _ (I.union hs hr)
    intro x hx
    by_contra outside
    have hd : x ∉ D := fun hh => outside (Or.inl hh.1)
    have no : x ∉ Set.range e := fun ⟨a,ha⟩ => outside (Or.inr (ha ▸ inside a))
    exact hx (exchange_outside _ hd no)
  refine ⟨⟨σ,permitted⟩,?_,?_⟩
  · intro a ha
    exact exchange_outside e (fun h => h.2 ha)
      (fun ⟨b,eq⟩ => empty (inside b) (Or.inl (Or.inr (eq ▸ ha))))
  · intro a ha
    by_cases inT : a ∈ T
    · have eq : σ a = a := exchange_outside e (fun hd => hd.2 inT)
        (fun ⟨b,eq⟩ => empty (inside b) (Or.inl (Or.inr (eq ▸ inT))))
      rw [eq]
      exact overlap a ⟨ha,inT⟩
    · let b : D := ⟨a,ha,inT⟩
      have eq : σ a = e b := exchange_left e b
      rw [eq]
      exact Classical.byContradiction (fun moved' => empty (inside b) (Or.inr moved'))

/-- Intersect two supports when each pair of row sections is either small or
identical. This includes the paper's common full exceptional rows. The three
factors of a permutation are assembled simultaneously in the full product. -/
theorem supports_intersection {V : Type*} [MulAction (Group I) V] (x : V) (S T : Support)
    (sections : ∀ n, S n = T n ∨ I.small (S n) ∧ I.small (T n))
    (hs : Supports I S x) (ht : Supports I T x) : Supports I (fun n => S n ∩ T n) x := by
  classical
  intro g fix
  have section' (n : ℕ) : ∃ τ : rowGroup I, (∀ a ∈ T n, τ.val a = a) ∧
      ∀ a ∈ S n, (g n).val (τ.val a) = τ.val a := by
    rcases sections n with eq | ⟨s,t⟩
    · exact ⟨1,fun _ _ => rfl,fun a ha => fix n a ⟨ha,eq ▸ ha⟩⟩
    · exact clear_row s t _ (fix n)
  choose τ τT inner using section'
  have fixx := ht τ τT
  have fx : Fixes I (τ⁻¹ * g * τ) S := by
    intro n a ha
    change (τ n).val.symm ((g n).val ((τ n).val a)) = a
    rw [inner n a ha,(τ n).val.symm_apply_apply]
  have eq := congrArg (fun y => τ • y) (hs _ fx)
  simpa only [mul_smul,smul_inv_smul,fixx] using eq

end EDMRows
