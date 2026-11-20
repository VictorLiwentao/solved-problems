module

public import SolvedProblems.PromptBoundSimulation

public section
namespace PromptBound
variable {α β : Type} [Primcodable α] [Primcodable β] {X : Oracle} {q : ℕ}

@[fun_prop] theorem eff_present [DecidableEq β] (xs : α → List β) (y : α → β)
    (hl : Effective X xs) (hy : Effective X y) :
    Effective X (fun a => present (xs a) (y a)) := by
  exact eff_any (g := fun z : α × β => decide (y z.1 = z.2)) hl (by fun_prop)

@[fun_prop] theorem eff_starts [DecidableEq β] (p y : α → List β)
    (hp : Effective X p) (hy : Effective X y) :
    Effective X (fun a => starts (p a) (y a)) := by
  have ht : Effective X (fun a => (y a).take (p a).length) :=
    .comp (.basic Primrec.list_take.to_comp) (.pair (.comp eff_length hp) hy)
  exact eff_beq_comp _ _ hp ht

private abbrev ScanArgs (q : ℕ) := (List (Word q) × History q) × Round q
private abbrev ScanState (q : ℕ) := List (Word q) × Bool

/-- Finite history scan relative to the sample. -/
theorem eff_scan (X : Oracle) : Effective X
    (fun z : List (Word q) × History q => scan z.1 z.2) := by
  let seen := fun z : ScanArgs q × ScanState q => z.1.2.1 :: z.2.1
  have he : Effective X seen := by dsimp [seen]; fun_prop
  let possible := fun z : ScanArgs q × ScanState q =>
    z.1.1.1.any (fun y => !present (seen z) y && starts z.1.2.2 y)
  have hp : Effective X possible := by
    apply eff_any (g := fun a : (ScanArgs q × ScanState q) × Word q =>
      !present (seen a.1) a.2 && starts a.1.1.2.2 a.2)
    · fun_prop
    · fun_prop
  let f := fun z : ScanArgs q × ScanState q =>
    (seen z, z.2.2 && present z.1.1.1 z.1.2.1 && possible z)
  have hf : Effective X f := by dsimp [f]; fun_prop
  exact .foldList (f := Prod.snd) (z := fun _ => ([],true)) (g := f) (by fun_prop) (by fun_prop) hf

theorem eff_memories (X : Oracle) : Effective X (@memories q) := by
  let raw := fun S : List (Word q) =>
    (List.range (S.length+1)).map (fun i => (Encodable.decode₂ (History q) i).getD [])
  have hr : Effective X raw := by
    apply eff_map (g := fun z : List (Word q) × ℕ => (Encodable.decode₂ (History q) z.2).getD [])
    · change Effective X (fun S : List (Word q) => List.range (Nat.succ S.length))
      fun_prop
    · fun_prop
  exact eff_filter (g := fun z : List (Word q) × History q => (scan z.1 z.2).2)
    hr (eff_snd _ (eff_scan X))

theorem eff_replay (X : Oracle) : Effective X
    (fun z : (List (Word q) × Word q) × History q => replay z.1.1 z.1.2 z.2) := by
  let obs := fun z : (List (Word q) × Word q) × History q =>
    z.1.1.map (fun a => (a, ([] : Word q)))
  have ho : Effective X obs := by
    apply eff_map (g := fun a : ((List (Word q) × Word q) × History q) × Word q =>
      (a.2,([] : Word q))) <;> fun_prop
  change Effective X (fun z : (List (Word q) × Word q) × History q =>
    (((z.1.1.head?).getD [],z.1.2) :: obs z) ++ z.2)
  fun_prop

end PromptBound
