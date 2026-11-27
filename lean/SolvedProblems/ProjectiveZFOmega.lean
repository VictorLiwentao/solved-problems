module

public import SolvedProblems.ProjectiveZFOrder

@[expose] public section

namespace ProjectiveZF

open Set Function

variable {V : Type*} [Membership V V]

/-- A designated internal omega consists exactly of the standard von Neumann
numerals, and each numeral contains the earlier ones. No global transitivity
or well-foundedness of the membership structure is required. -/
structure StandardOmega (ω : V) where
  numeral : ℕ ↪ V
  members : ∀ z, z ∈ ω ↔ ∃ n, numeral n = z
  earlier : ∀ (n : ℕ) (z : V), z ∈ numeral n ↔ ∃ j : Fin n, numeral j.val = z

/-- The membership-language definition of having finite cardinality. -/
def FiniteIn (ω X : V) : Prop := ∃ n, n ∈ ω ∧ Equinumerous n X

/-- The original internal definition of amorphousness: infinite, and every
internal subset is finite or has a finite relative complement. -/
def AmorphousIn (ω X : V) : Prop := ¬ FiniteIn ω X ∧
  ∀ T, (∀ a, a ∈ T → a ∈ X) → FiniteIn ω T ∨
    ∃ U, (∀ a, a ∈ U ↔ a ∈ X ∧ a ∉ T) ∧ FiniteIn ω U

theorem defFiniteIn {ι : Type*} {o s : (ι → V) → V} (ho : Term o) (hs : Term s) :
    Definable (fun v => FiniteIn (o v) (s v)) := by
  unfold FiniteIn
  repeat' first | apply defEquinumerous | apply defEx | apply defAnd | apply defMem | zf_terms

theorem defAmorphousIn {ι : Type*} {o s : (ι → V) → V} (ho : Term o) (hs : Term s) :
    Definable (fun v => AmorphousIn (o v) (s v)) := by
  unfold AmorphousIn
  repeat' first | apply defFiniteIn | apply defIff | apply defAnd | apply defOr | apply defNot | apply defAll
                | apply defEx | apply defImp | apply defMem | zf_terms

noncomputable def StandardOmega.enumerate {ω : V} (std : StandardOmega ω) (n : ℕ) : Fin n ≃ El (std.numeral n) := by
  let f (i : Fin n) : El (std.numeral n) := ⟨_,(std.earlier n _).mpr ⟨i,rfl⟩⟩
  apply Equiv.ofBijective f
  refine ⟨fun a b eq => Fin.ext (std.numeral.injective (congrArg Subtype.val eq)),?_⟩
  intro x
  obtain ⟨i,h⟩ := (std.earlier n x.val).mp x.property
  exact ⟨i,Subtype.ext h⟩

variable (M : Core V)
include M

/-- In an omega-standard membership model, internal finiteness is equivalent
to external finiteness of the set of members. -/
theorem finiteIn_iff {ω : V} (std : StandardOmega ω) (X : V) : FiniteIn ω X ↔ Finite (El X) := by
  classical
  constructor
  · rintro ⟨n,mem,eq⟩
    obtain ⟨k,rfl⟩ := (std.members n).mp mem
    obtain ⟨e⟩ := equiv_of_equinumerous M eq
    exact Finite.of_equiv (Fin k) ((std.enumerate k).trans e)
  · intro small
    let := small
    let := Fintype.ofFinite (El X)
    let n := Fintype.card (El X)
    let en := std.enumerate n
    let := Finite.of_equiv (Fin n) en
    exact ⟨std.numeral n,(std.members _).mpr ⟨n,rfl⟩,equinumerous_of_finite M (en.symm.trans (Fintype.equivFin (El X)).symm)⟩

private def restrictEquiv {X Y : V} {P : El X → Prop} (sub : ∀ a ∈ Y, a ∈ X)
    (rule : ∀ a : El X, a.val ∈ Y ↔ P a) : El Y ≃ {a : El X // P a} where
  toFun y := ⟨⟨y.val,sub y.val y.property⟩,(rule _).mp y.property⟩
  invFun a := ⟨a.val.val,(rule _).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite/cofinite condition used in the external order argument is an
exact interpretation of the original internal condition in omega-standard models. -/
theorem amorphousIn_iff {ω : V} (std : StandardOmega ω) (X : V) :
    AmorphousIn ω X ↔ Infinite (El X) ∧ SmallSubsets X := by
  classical
  constructor
  · rintro ⟨inf,h⟩
    refine ⟨(not_finite_iff_infinite).mp (fun f => inf ((finiteIn_iff M std X).mpr f)),?_⟩
    intro t
    obtain ⟨T,rep⟩ := M.separation X (fun a => a ∈ t) (defMem (termVar ()) (termParam _))
    have inc (a : V) (ha : a ∈ T) := ((rep a).mp ha).1
    have same (a : El X) : a.val ∈ T ↔ a.val ∈ t := (rep a.val).trans (and_iff_right a.property)
    rcases h T inc with finite | ⟨U,co,finite⟩
    · let := (finiteIn_iff M std _).mp finite
      exact Or.inl (show Finite _ from Finite.of_equiv (El T) (restrictEquiv inc same))
    · let := (finiteIn_iff M std _).mp finite
      let e := restrictEquiv (fun a ha => ((co a).mp ha).1) (fun a : El X => (co a.val).trans ((and_iff_right a.property).trans (not_congr (same a))))
      exact Or.inr (show Finite _ from Finite.of_equiv (El U) e)
  · rintro ⟨inf,small⟩
    refine ⟨fun f => (not_finite_iff_infinite.mpr inf) ((finiteIn_iff M std X).mp f),?_⟩
    intro T sub
    rcases small T with fin|fin
    · let : Finite {a : El X // a.val ∈ T} := fin.to_subtype
      let e := restrictEquiv sub (fun a : El X => Iff.rfl)
      exact Or.inl ((finiteIn_iff M std T).mpr (Finite.of_equiv _ e.symm))
    · obtain ⟨U,co⟩ := M.separation X (fun a => a ∉ T) (defNot (defMem (termVar ()) (termParam _)))
      let : Finite {a : El X // a.val ∉ T} := fin.to_subtype
      let e := restrictEquiv (fun a ha => ((co a).mp ha).1) (fun a : El X => (co a.val).trans (and_iff_right a.property))
      exact Or.inr ⟨U,co,(finiteIn_iff M std U).mpr (Finite.of_equiv _ e.symm)⟩

end ProjectiveZF
