module

public import SolvedProblems.SettlingSignals

@[expose] public section

open Nat.Partrec.Code
open Filter
namespace StrongSettling

/-- The input program must halt on every earlier input before this sum returns. -/
def prefixSum (c : Program) : ℕ →. ℕ
  | 0 => eval c 0
  | n+1 => (prefixSum c n).bind fun a => (eval c (n+1)).map fun b => a+b

def envelope (c : Program) (n : ℕ) : Part ℕ := (prefixSum c n).map fun s => n+1+s

private theorem sum_partrec : Partrec₂ prefixSum := by
  let U := (Program × ℕ) × (ℕ × ℕ)
  have step : Partrec fun q : U => (eval q.1.1 (q.2.1+1)).map (fun z => q.2.2+z) := by
    apply (eval_part.comp (Computable.fst.comp Computable.fst)
      (Computable.succ.comp (Computable.fst.comp Computable.snd))).map
    exact ((Primrec.to_comp Primrec.nat_add).to₂.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd).to₂
  have s := Partrec.nat_rec (α := Program × ℕ) Computable.snd
    (eval_part.comp Computable.fst (Computable.const 0)) step.to₂
  refine s.of_eq ?_
  rintro ⟨c,n⟩
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun v : Part ℕ => v.bind fun a => (eval c (n+1)).map fun b => a+b) ih

theorem envelope_partrec : Partrec₂ envelope := by
  apply sum_partrec.map
  exact ((Primrec.to_comp Primrec.nat_add).to₂.comp
    (Computable.succ.comp (Computable.snd.comp Computable.fst)) Computable.snd).to₂

/-- There is one computable list of programs for the envelopes. -/
theorem envelope_compiler : ∃ e : Program → Program, Computable e ∧
    ∀ c x, eval (e c) x = envelope c x := by
  let fn (i x : ℕ) := envelope (Denumerable.ofNat Program i) x
  have dec : Partrec₂ fn := (envelope_partrec.comp ((Computable.ofNat Program).comp Computable.fst) Computable.snd).to₂
  obtain ⟨m,hm⟩ := exists_code.mp (Partrec₂.unpaired'.mpr dec)
  refine ⟨fun c => curry m (Encodable.encode c),
    (primrec₂_curry.comp (Primrec.const m) Primrec.encode).to_comp,fun c x => ?_⟩
  rw [eval_curry,hm]
  simp [Nat.unpaired,fn]

private theorem larger_sum {c : Program} {n j v : ℕ} (h : v ∈ prefixSum c n) (below : j ≤ n) :
    ∃ u ∈ prefixSum c j, u ≤ v := by
  induction n generalizing v with
  | zero =>
    obtain rfl : j=0 := by omega
    exact ⟨_,h,le_rfl⟩
  | succ n ih =>
    by_cases eq : j=n+1
    · subst j; exact ⟨_,h,le_rfl⟩
    obtain ⟨a,ha,hv⟩ := Part.mem_bind_iff.mp h
    obtain ⟨b,_,rfl⟩ := (Part.mem_map_iff _).mp hv
    obtain ⟨u,hu,le⟩ := ih ha (by omega)
    exact ⟨u,hu,by omega⟩

/-- Every value at a larger input forces convergence at every smaller one,
and the output strictly increases between any two different inputs. -/
theorem envelope_initial {c : Program} {n m v : ℕ} (h : v ∈ envelope c n) (lt : m<n) :
    ∃ u ∈ envelope c m, u < v := by
  obtain ⟨a,ha,rfl⟩ := (Part.mem_map_iff _).mp h
  obtain ⟨b,hb,le⟩ := larger_sum ha lt.le
  exact ⟨_,(Part.mem_map_iff _).mpr ⟨b,hb,rfl⟩,by omega⟩

private theorem total_sum {c : Program} (h : ∀ x, (eval c x).Dom) (n : ℕ) :
    ∃ s ∈ prefixSum c n, ∃ v ∈ eval c n, v ≤ s := by
  induction n with
  | zero =>
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp (h 0)
    exact ⟨_,hv,_,hv,le_rfl⟩
  | succ n ih =>
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp (h (n+1))
    obtain ⟨a,ha,-⟩ := ih
    exact ⟨_,Part.mem_bind_iff.mpr ⟨a,ha,(Part.mem_map_iff _).mpr ⟨v,hv,rfl⟩⟩,v,hv,by omega⟩

/-- Total computable functions are pointwise majorized by total members of
the envelope list. Each such member is eventually eligible under a dominant modulus. -/
theorem effective_majorants (D : Enumeration)
    (dom : ∀ f : ℕ → ℕ, Computable f → ∀ᶠ x in atTop, f x ≤ D.modulus x) :
    ∃ e : Program → Program, Computable e ∧
      (∀ c n m v, v ∈ eval (e c) n → m<n → ∃ u ∈ eval (e c) m, u<v) ∧
      ∀ f : ℕ → ℕ, Computable f → ∃ c,
        (∀ x, ∃ v ∈ eval (e c) x, max x (f x)<v) ∧ ∀ᶠ x in atTop, Eligible D (e c) x := by
  obtain ⟨e,eff,ok⟩ := envelope_compiler
  refine ⟨e,eff,fun c n m v h lt => by simpa only [ok] using envelope_initial (ok c n ▸ h) lt,?_⟩
  intro f hf
  obtain ⟨c,hc⟩ := exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  have total (n : ℕ) : (eval c n).Dom := by rw [hc]; trivial
  have positive (n : ℕ) : ∃ v ∈ eval (e c) n, max n (f n)<v := by
    obtain ⟨s,hs,v,hv,le⟩ := total_sum total n
    have eq : v = f n := by rw [hc] at hv; exact Part.mem_some_iff.mp hv
    rw [ok]
    exact ⟨_,(Part.mem_map_iff _).mpr ⟨s,hs,rfl⟩,by omega⟩
  exact ⟨c,positive,eventually_eligible D dom _ (fun n => (positive n).choose_spec.1.1)⟩

end StrongSettling
