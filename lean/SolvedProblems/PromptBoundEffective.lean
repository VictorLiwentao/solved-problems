module

public import SolvedProblems.PromptBoundModel
public import Mathlib.Tactic.FunProp

public section
namespace PromptBound
attribute [fun_prop] Effective
variable {X : Oracle} {α β γ δ : Type} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]

@[fun_prop] theorem eff_id : Effective X (fun a : α => a) := .basic Primrec.id.to_comp
@[fun_prop] theorem eff_const (b : β) : Effective X (fun _ : α => b) := .basic (Primrec.const b).to_comp
@[fun_prop] theorem eff_comp (g : β → γ) (f : α → β) (hg : Effective X g) (hf : Effective X f) :
    Effective X (fun a => g (f a)) := .comp hg hf
@[fun_prop] theorem eff_pair (f : α → β) (g : α → γ) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => (f a,g a)) := .pair hf hg
@[fun_prop] theorem eff_fst (f : α → β × γ) (hf : Effective X f) :
    Effective X (fun a => (f a).1) := .comp (.basic Primrec.fst.to_comp) hf
@[fun_prop] theorem eff_snd (f : α → β × γ) (hf : Effective X f) :
    Effective X (fun a => (f a).2) := .comp (.basic Primrec.snd.to_comp) hf

@[fun_prop] theorem eff_encode : Effective X (@Encodable.encode α _) := .basic Primrec.encode.to_comp
@[fun_prop] theorem eff_decode : Effective X (@Encodable.decode₂ α _) := .basic Primrec.decode₂.to_comp
@[fun_prop] theorem eff_length : Effective X (@List.length α) := .basic Primrec.list_length.to_comp
@[fun_prop] theorem eff_rev : Effective X (@List.reverse α) := .basic Primrec.list_reverse.to_comp
@[fun_prop] theorem eff_range : Effective X List.range := .basic Primrec.list_range.to_comp
@[fun_prop] theorem eff_some : Effective X (@Option.some α) := .basic Primrec.option_some.to_comp
@[fun_prop] theorem eff_cons : Effective X (fun p : α × List α => p.1 :: p.2) :=
  .basic Primrec.list_cons.to_comp
@[fun_prop] theorem eff_append : Effective X (fun p : List α × List α => p.1 ++ p.2) :=
  .basic Primrec.list_append.to_comp
@[fun_prop] theorem eff_getD : Effective X (fun p : Option α × α => p.1.getD p.2) :=
  .basic (Primrec.option_getD.comp Primrec.fst Primrec.snd).to_comp
@[fun_prop] theorem eff_head : Effective X (@List.head? α) := .basic Primrec.list_head?.to_comp
@[fun_prop] theorem eff_isSome : Effective X (@Option.isSome α) := .basic Primrec.option_isSome.to_comp
@[fun_prop] theorem eff_flatten : Effective X (@List.flatten α) := .basic Primrec.list_flatten.to_comp
@[fun_prop] theorem eff_succ : Effective X Nat.succ := .basic Primrec.succ.to_comp
@[fun_prop] theorem eff_mul : Effective X (fun p : ℕ × ℕ => p.1 * p.2) := .basic Primrec.nat_mul.to_comp
@[fun_prop] theorem eff_blt : Effective X (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
  .basic (primrecPred_iff_primrec_decide.mp Primrec.nat_lt).to_comp
@[fun_prop] theorem eff_beq [DecidableEq α] : Effective X (fun p : α × α => decide (p.1 = p.2)) :=
  .basic (primrecPred_iff_primrec_decide.mp Primrec.eq).to_comp
@[fun_prop] theorem eff_max : Effective X (fun p : ℕ × ℕ => max p.1 p.2) :=
  .basic Primrec.nat_max.to_comp
@[fun_prop] theorem eff_cond : Effective X (fun p : Bool × (α × α) => bif p.1 then p.2.1 else p.2.2) :=
  .basic (Primrec.cond Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp
@[fun_prop] theorem eff_not : Effective X Bool.not := .basic Primrec.not.to_comp
@[fun_prop] theorem eff_and : Effective X (fun p : Bool × Bool => p.1 && p.2) := .basic Primrec.and.to_comp
@[fun_prop] theorem eff_or : Effective X (fun p : Bool × Bool => p.1 || p.2) := .basic Primrec.or.to_comp

@[fun_prop] theorem eff_and_comp (f g : α → Bool) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => f a && g a) := .comp eff_and (.pair hf hg)
@[fun_prop] theorem eff_or_comp (f g : α → Bool) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => f a || g a) := .comp eff_or (.pair hf hg)
@[fun_prop] theorem eff_cons_comp (f : α → β) (g : α → List β) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => f a :: g a) := .comp eff_cons (.pair hf hg)
@[fun_prop] theorem eff_append_comp (f g : α → List β) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => f a ++ g a) := .comp eff_append (.pair hf hg)
@[fun_prop] theorem eff_mul_comp (f g : α → ℕ) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => f a * g a) := .comp eff_mul (.pair hf hg)
@[fun_prop] theorem eff_blt_comp (f g : α → ℕ) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => decide (f a < g a)) := .comp eff_blt (.pair hf hg)
@[fun_prop] theorem eff_max_comp (f g : α → ℕ) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => max (f a) (g a)) := .comp eff_max (.pair hf hg)
@[fun_prop] theorem eff_beq_comp [DecidableEq β] (f g : α → β) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => decide (f a = g a)) := .comp eff_beq (.pair hf hg)
@[fun_prop] theorem eff_getD_comp (f : α → Option β) (g : α → β) (hf : Effective X f) (hg : Effective X g) :
    Effective X (fun a => (f a).getD (g a)) := .comp eff_getD (.pair hf hg)
@[fun_prop] theorem eff_cond_comp (f : α → Bool) (g h : α → β) (hf : Effective X f)
    (hg : Effective X g) (hh : Effective X h) :
    Effective X (fun a => bif f a then g a else h a) :=
  .comp eff_cond (.pair hf (.pair hg hh))

theorem eff_map {f : α → List β} {g : α × β → γ}
    (hf : Effective X f) (hg : Effective X g) : Effective X (fun a => (f a).map (fun b => g (a,b))) :=
  .mapList hf hg

theorem eff_filter {f : α → List β} {g : α × β → Bool}
    (hf : Effective X f) (hg : Effective X g) : Effective X (fun a => (f a).filter (fun b => g (a,b))) := by
  have ef : Effective X (fun a => (f a).foldr (fun b l => bif g (a,b) then b::l else l) []) :=
    .foldList (g := fun z : (α × β) × List β => bif g z.1 then z.1.2::z.2 else z.2) hf (eff_const []) (by fun_prop)
  convert ef using 1
  funext a
  induction f a with
  | nil => rfl
  | cons b l ih => simp only [List.filter_cons, List.foldr_cons]; cases g (a,b) <;> simp_all

theorem eff_all {f : α → List β} {g : α × β → Bool}
    (hf : Effective X f) (hg : Effective X g) : Effective X (fun a => (f a).all (fun b => g (a,b))) := by
  have ef : Effective X (fun a => (f a).foldr (fun b r => g (a,b) && r) true) :=
    .foldList (g := fun z : (α × β) × Bool => g z.1 && z.2) hf (eff_const true) (by fun_prop)
  convert ef using 1
  funext a
  induction f a <;> simp_all

theorem eff_any {f : α → List β} {g : α × β → Bool}
    (hf : Effective X f) (hg : Effective X g) : Effective X (fun a => (f a).any (fun b => g (a,b))) := by
  have ef : Effective X (fun a => (f a).foldr (fun b r => g (a,b) || r) false) :=
    .foldList (g := fun z : (α × β) × Bool => g z.1 || z.2) hf (eff_const false) (by fun_prop)
  convert ef using 1
  funext a
  induction f a <;> simp_all

end PromptBound
