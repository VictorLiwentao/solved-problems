module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Logic.Equiv.Set

public section
namespace WellOrderUnion

open Equiv Function Cardinal

/-- Encode a point by the lesser member of its orbit under an involution and a bit. -/
private def orbitCode {B} [LinearOrder B] (v : Perm B) (x : B) : B × Bool :=
  if x ≤ v x then (x, false) else (v x, true)

private theorem orbitCode_inj {B} [LinearOrder B] (v : Perm B) :
    Injective (orbitCode v) := by
  intro x y eq
  by_cases hx : x ≤ v x <;> by_cases hy : y ≤ v y <;>
    simp [orbitCode, hx, hy] at eq
  · exact eq
  · exact eq

private theorem orbitCode_flip {B} [LinearOrder B] (v : Perm B) (hv : Involutive v) (x : B) :
    (orbitCode v (v x)).1 = (orbitCode v x).1 := by
  by_cases h : x = v x
  · rw [← h]
  by_cases h' : x ≤ v x
  · have k := (lt_of_le_of_ne h' h).not_ge
    simp [orbitCode, hv x, h', k]
  · have k := le_of_not_ge h'
    simp [orbitCode, hv x, h', k]

/-- Two invariant parts of an infinite set, both large enough to contain a copy of the whole. -/
private theorem split_orbits {B : Type u} [Infinite B] [LinearOrder B]
    (v : Perm B) (hv : Involutive v) :
    ∃ D : B → Prop, (∀ x, D (v x) ↔ D x) ∧
      Nonempty (B ↪ {x // D x}) ∧ Nonempty (B ↪ {x // ¬D x}) := by
  classical
  let b := fun x : B => (orbitCode v x).1
  let R := Set.range b
  let enc : B ↪ R × Bool := ⟨fun x => (⟨b x,x,rfl⟩,(orbitCode v x).2),by
    intro x y h
    exact orbitCode_inj v (Prod.ext (congrArg (fun z : R × Bool => z.1.val) h)
      (congrArg (fun z : R × Bool => z.2) h))⟩
  have : Infinite R := by
    by_contra! h
    let : Finite R := h
    have : Finite B := Finite.of_injective enc enc.injective
    exact not_finite B
  obtain ⟨fold⟩ : Nonempty (R × Bool ↪ R) := by
    apply (Cardinal.le_def _ _).mp
    rw [Cardinal.mk_prod]
    simpa using (Cardinal.mul_eq_left (Cardinal.aleph0_le_mk R)
      ((Cardinal.natCast_le_aleph0 (n := 2)).trans (Cardinal.aleph0_le_mk R))
      (show (2 : Cardinal.{u}) ≠ 0 by simp)).le
  let key (x : B) : R := ⟨b x,x,rfl⟩
  have core (r : R) : b r.val = r.val := by
    obtain ⟨x,hx⟩ := r.prop
    change (orbitCode v r.val).1 = r.val
    rw [← hx]
    by_cases h : x ≤ v x
    · simp [b,orbitCode,h]
    · have h' := le_of_not_ge h
      simp [b,orbitCode,h,h',hv x]
  let D (x : B) := ∃ j : R, fold (j,true) = key x
  have tagged (x : B) (i : Bool) : key (fold (fold (enc x), i)).val = fold (fold (enc x), i) :=
    Subtype.ext (core _)
  have inj (i : Bool) : Injective (fun x : B => (fold (fold (enc x),i)).val) := by
    intro x y h
    exact enc.injective (fold.injective (Prod.mk.inj (fold.injective (Subtype.ext h))).1)
  refine ⟨D, fun x => ?_, ⟨⟨fun x => ⟨_, fold (enc x), (tagged x true).symm⟩,
    fun x y h => inj true (congrArg (fun z : {x // D x} => z.val) h)⟩⟩, ⟨⟨fun x => ⟨(fold (fold (enc x),false)).val,?_⟩,
    fun x y h => inj false (congrArg (fun z : {x // ¬D x} => z.val) h)⟩⟩⟩
  · have e : key (v x) = key x := Subtype.ext (orbitCode_flip v hv x)
    simp only [D,e]
  · rintro ⟨j,hj⟩
    rw [tagged x false] at hj
    exact Bool.noConfusion (Prod.mk.inj (fold.injective hj)).2

/-- Extend an embedding on one part to a permutation using large complements on both sides. -/
private theorem extend_embedding {B : Type u} {D : B → Prop}
    (f : {x // D x} ↪ B) (source : B ↪ {x // ¬D x})
    (target : B ↪ {x // x ∉ Set.range f}) :
    ∃ h : Perm B, ∀ x : {x // D x}, h x = f x := by
  classical
  let P := Set.range f
  obtain ⟨c⟩ := Embedding.antisymm ((Embedding.subtype _).trans target)
    ((Embedding.subtype _).trans source)
  let e := ((sumCompl D).symm.trans ((Equiv.ofInjective f f.injective).sumCongr c)).trans
    (sumCompl (· ∈ P))
  refine ⟨e, fun x => ?_⟩
  simp [e, Equiv.sumCompl_symm_apply_of_pos x.prop]

/-- A restriction of an involution is conjugate into a prescribed coloring stabilizer
when its complement contains a full-size reservoir of points. -/
private theorem hide {B : Type u} [LinearOrder B] (Q : B → ℕ) (e : B × Fin 3 ↪ B)
    (he : ∀ x, Q (e (x,0)) = Q (e (x,1)))
    (v : Perm B) (hv : Involutive v) (D : B → Prop) (hd : ∀ x, D (v x) ↔ D x)
    (reserve : B ↪ {x // ¬D x}) :
    ∃ h : Perm B, ∀ x, D x → Q (h (v x)) = Q (h x) := by
  classical
  let tag : Bool ↪ Fin 3 := ⟨fun b => if b then 1 else 0, by decide⟩
  let f : {x // D x} ↪ B := (Embedding.subtype _).trans
    ((⟨orbitCode v,orbitCode_inj v⟩ : B ↪ B × Bool).trans
      (((Embedding.refl B).prodMap tag).trans e))
  have val (x : {x // D x}) : f x = e ((orbitCode v x).1,tag (orbitCode v x).2) := rfl
  let spare : B ↪ {x // x ∉ Set.range f} :=
    ⟨fun x => ⟨e (x,2), by
      rintro ⟨y,hy⟩
      rw [val] at hy
      have hh := (Prod.mk.inj (e.injective hy)).2
      have impossible : ∀ b : Bool, tag b ≠ 2 := by decide
      exact impossible _ hh⟩, fun x y h =>
      (Prod.mk.inj (e.injective (congrArg Subtype.val h))).1⟩
  obtain ⟨h,hh⟩ := extend_embedding f reserve spare
  refine ⟨h, fun x hx => ?_⟩
  rw [hh ⟨v x,(hd x).mpr hx⟩,hh ⟨x,hx⟩,val,val,orbitCode_flip v hv x]
  cases (orbitCode v (v x)).2 <;> cases (orbitCode v x).2 <;>
    first | rfl | exact he _ | exact (he _).symm

private def clip {B} (v : Perm B) (hv : Involutive v) (D : B → Prop) [DecidablePred D]
    (hd : ∀ x, D (v x) ↔ D x) : Perm B :=
  let f x := if D x then v x else x
  let inv : ∀ x, f (f x) = x := fun x => by
    by_cases h : D x
    · simp [f,h,(hd x).mpr h,hv x]
    · simp [f,h]
  ⟨f,f,inv,inv⟩

@[expose] def Hides {B} (Q : B → ℕ) (v : Perm B) := ∃ h : Perm B, ∀ x, Q (h (v x)) = Q (h x)

private theorem split_hidden {B : Type u} [Infinite B] (Q : B → ℕ) (e : B × Fin 3 ↪ B)
    (he : ∀ x, Q (e (x,0)) = Q (e (x,1))) (v : Perm B) (hv : Involutive v) :
    ∃ a b : Perm B, Hides Q a ∧ Hides Q b ∧ v = a * b := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : B → B → Prop)
  obtain ⟨D,hd,⟨one⟩,⟨two⟩⟩ := split_orbits v hv
  let E x := ¬ D x
  have hE x : E (v x) ↔ E x := not_congr (hd x)
  let a := clip v hv D hd
  let b := clip v hv E hE
  obtain ⟨s,hs⟩ := hide Q e he v hv D hd two
  let reserveE : B ↪ {x // ¬E x} := one.trans
    ⟨fun x => ⟨x.val,fun h => h x.prop⟩,fun _ _ h => Subtype.ext (congrArg (fun z : {x // ¬E x} => z.val) h)⟩
  obtain ⟨t,ht⟩ := hide Q e he v hv E hE reserveE
  refine ⟨a,b,⟨s,fun x => ?_⟩,⟨t,fun x => ?_⟩,?_⟩
  · by_cases h : D x <;> simp [a,clip,h,hs x]
  · by_cases h : E x <;> simp [b,clip,h,ht x]
  · ext x
    by_cases hx : D x
    · simp [Perm.mul_apply,a,b,clip,E,hx]
    · simp [Perm.mul_apply,a,b,clip,E,hx,show ¬D (v x) from mt (hd x).mp hx]

/-- Pick an origin on each cycle and reflect the integer coordinate about it. The
reflection is independent of the coordinate even on a finite cycle. -/
private theorem cycle_reflection {B : Type u} (p : Perm B) :
    ∃ r : Perm B, (∀ x, r (r x) = x) ∧ (∀ x, r (p x) = p.symm (r x)) ∧
      ∀ x, p.SameCycle x (r x) := by
  classical
  let cls (x : B) := Quotient.mk (Perm.SameCycle.setoid p) x
  let base (x : B) := (cls x).out
  have repr (x : B) : p.SameCycle (base x) x := Quotient.exact (cls x).out_eq
  let idx (x : B) := (repr x).choose
  have atIdx (x : B) : (p ^ idx x) (base x) = x := (repr x).choose_spec
  have origin {x y : B} (h : p.SameCycle x y) : base x = base y :=
    congrArg Quotient.out (show cls x = cls y from Quotient.sound h)
  let rev (x : B) := (p ^ (-idx x)) (base x)
  have atNeg (x : B) (j : ℤ) : rev ((p^j) (base x)) = (p^(-j)) (base x) := by
    let y := (p^j) (base x)
    have common : base y = base x := (origin ((repr x).symm.trans ⟨j,rfl⟩)).symm
    have h := atIdx y
    rw [common] at h
    change (p ^ idx y) (base x) = (p ^ j) (base x) at h
    have eq := congrArg (fun t : B => (p ^ (-idx y-j)) t) h
    change (p ^ (-idx y)) (base y) = _
    rw [common]
    simpa only [← Perm.mul_apply, ← zpow_add, sub_add_cancel,
      show -idx y-j+idx y = -j by omega] using eq.symm
  have inv (x : B) : rev (rev x) = x := by
    calc
      rev (rev x) = (p ^ (-(-idx x))) (base x) := atNeg x (-idx x)
      _ = x := by simpa using atIdx x
  let r : Perm B := ⟨rev,rev,inv,inv⟩
  refine ⟨r, inv, fun x => ?_, fun x => (repr x).symm.trans ⟨-idx x,rfl⟩⟩
  change rev (p x) = p.symm ((p ^ (-idx x)) (base x))
  have step : p x = (p ^ (1 + idx x)) (base x) := by simp [zpow_add, atIdx]
  rw [step, atNeg]
  change (p ^ (-(1+idx x))) (base x) = (p⁻¹ * p ^ (-idx x)) (base x)
  rw [show -(1+idx x) = -1 + (-idx x) by omega, zpow_add, zpow_neg_one]

/-- A uniform bound of four conjugates works on every infinite block admitting the
same-color matching and hence on unrestricted products of such blocks. -/
theorem four_hidden {B : Type u} [Infinite B] (Q : B → ℕ) (e : B × Fin 3 ↪ B)
    (he : ∀ x, Q (e (x,0)) = Q (e (x,1))) (p : Perm B) :
    ∃ a b c d : Perm B, Hides Q a ∧ Hides Q b ∧ Hides Q c ∧ Hides Q d ∧
      p = (a*b)*(c*d) := by
  obtain ⟨r,hinv,hrev,_⟩ := cycle_reflection p
  have hi : Involutive (p*r) := fun x => by
    simp only [Perm.mul_apply,hrev,hinv,p.apply_symm_apply]
  obtain ⟨a,b,ha,hb,eq⟩ := split_hidden Q e he (p*r) hi
  obtain ⟨c,d,hc,hd,eq'⟩ := split_hidden Q e he r hinv
  refine ⟨a,b,c,d,ha,hb,hc,hd,?_⟩
  rw [← eq,← eq']
  ext x
  simp [hinv]

end WellOrderUnion
