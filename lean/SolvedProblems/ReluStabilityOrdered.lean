module

public import SolvedProblems.ReluStabilityTransport
public import Mathlib.Topology.Order.MonotoneContinuity

@[expose] public section

open Set Filter
open scoped Topology

namespace ReluStability

noncomputable def move (t u : ℝ) : List ℝ → ℝ → ℝ
  | [], z => z + (u-t)
  | s :: ss, z => middle (move t u ss z) (oneMove t u s z) z

theorem move_abs (t u : ℝ) (ss : List ℝ) (z : ℝ) : |move t u ss z - z| ≤ |u-t| := by
  induction ss with
  | nil => simp [move]
  | cons s ss ih =>
    obtain ⟨hl,hr⟩ := middle_bounds (move t u ss z) (oneMove t u s z) z
    obtain ⟨ha,hb⟩ := abs_le.mp ih
    obtain ⟨hc,hd⟩ := abs_le.mp (oneMove_abs t u s z)
    apply abs_le.mpr
    change min _ _ ≤ move t u (s::ss) z at hl
    change move t u (s::ss) z ≤ max _ _ at hr
    constructor
    · have := (le_min (show z-|u-t| ≤ move t u ss z by linarith) (by linarith : z-|u-t| ≤ oneMove t u s z)).trans hl
      linarith
    · have := hr.trans (max_le (show move t u ss z ≤ z+|u-t| by linarith) (by linarith : oneMove t u s z ≤ z+|u-t|))
      linarith

theorem move_start (t u : ℝ) (ss : List ℝ) (h : ∀ s ∈ ss, SameSide t u s) : move t u ss t = u := by
  induction ss with
  | nil => simp [move]
  | cons s ss ih => rw [move,ih (fun l hl => h l (List.mem_cons_of_mem _ hl)),oneMove_start _ _ _ (h s (by simp)),middle_self]

theorem move_fixed (t u : ℝ) (ss : List ℝ) {s : ℝ} (hs : s ∈ ss) : move t u ss s = s := by
  induction ss with
  | nil => simp at hs
  | cons k ks ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · rw [move,oneMove_fixed,middle_right]
    · rw [move,ih hs,middle_left]

theorem move_mono {t u : ℝ} (ss : List ℝ) (h : ∀ s ∈ ss, SameSide t u s) : StrictMono (move t u ss) := by
  induction ss with
  | nil => intro x y hxy; change x+(u-t) < y+(u-t); linarith
  | cons s ss ih =>
    intro a b hxy
    exact middle_strict
      (ih (fun l hl => h l (List.mem_cons_of_mem _ hl)) hxy)
      (oneMove_mono (h s (by simp)) hxy) hxy

theorem move_same (t : ℝ) (ss : List ℝ) (z : ℝ) : move t t ss z = z := by
  have h := move_abs t t ss z
  simpa only [sub_self,abs_zero,abs_nonpos_iff,sub_eq_zero] using h

theorem move_continuous {B : Type*} [TopologicalSpace B] {t u z : B → ℝ} (ss : List (B → ℝ))
    (ht : Continuous t) (hu : Continuous u) (hz : Continuous z)
    (hs : ∀ s ∈ ss, Continuous s) (h : ∀ b s, s ∈ ss → SameSide (t b) (u b) (s b)) :
    Continuous fun b => move (t b) (u b) (ss.map (fun s => s b)) (z b) := by
  induction ss with
  | nil => exact hz.add (hu.sub ht)
  | cons s ss ih =>
    exact middle_continuous
      (ih (fun k hk => hs k (List.mem_cons_of_mem _ hk)) (fun b k hk => h b k (List.mem_cons_of_mem _ hk)))
      (oneMove_continuous ht hu (hs s (by simp)) hz (fun b => h b s (by simp))) hz

theorem move_surjective {t u : ℝ} (ss : List ℝ) (h : ∀ s ∈ ss, SameSide t u s) : Function.Surjective (move t u ss) := by
  have hc : Continuous (move t u ss) := by
    have hh := move_continuous (ss.map fun s => fun _ : ℝ => s) (t:=fun _ => t) (u:=fun _ => u) (z:=id)
      continuous_const continuous_const continuous_id (by simp only [List.mem_map,forall_exists_index,and_imp]; rintro _ s _ rfl; exact continuous_const) (by simpa using fun (_ : ℝ) => h)
    simpa [List.map_map,Function.comp_def] using hh
  intro y
  let low := y-|u-t|
  let high := y+|u-t|
  have h₁ := (abs_le.mp (move_abs t u ss low)).2
  have h₂ := (abs_le.mp (move_abs t u ss high)).1
  have hl : move t u ss low ≤ y := by dsimp [low] at *; linarith
  have hr : y ≤ move t u ss high := by dsimp [high] at *; linarith
  exact intermediate_value_univ low high hc ⟨hl,hr⟩

/-- Simultaneous transport of any finite set of real landmarks, allowing ties
that persist between the two configurations. The base space may itself contain
both parameters and lower-dimensional input coordinates. -/
theorem ordered_transport {B : Type*} [TopologicalSpace B] (xs : List ((B → ℝ) × (B → ℝ)))
    (hc : ∀ f ∈ xs, Continuous f.1 ∧ Continuous f.2)
    (ho : ∀ b, ∀ f ∈ xs, ∀ g ∈ xs, (f.1 b < g.1 b ↔ f.2 b < g.2 b) ∧ (f.1 b = g.1 b ↔ f.2 b = g.2 b)) :
    ∃ F : B → ℝ ≃o ℝ, Continuous (fun z : B×ℝ => F z.1 z.2) ∧
      (∀ b, ∀ f ∈ xs, F b (f.1 b) = f.2 b) ∧ (∀ b, (∀ f ∈ xs, f.1 b = f.2 b) → ∀ x, F b x = x) := by
  induction xs with
  | nil => exact ⟨fun _ => OrderIso.refl _,continuous_snd,by simp,by simp⟩
  | cons f xs ih =>
    have hin (g) (hg : g ∈ xs) := List.mem_cons_of_mem f hg
    obtain ⟨F,hF,hland,hid⟩ := ih (fun g hg => hc g (hin g hg)) (fun b g hg k hk => ho b g (hin _ hg) k (hin _ hk))
    let t := fun b => F b (f.1 b)
    let u := f.2
    let old := xs.map Prod.snd
    have same (b) (g) (hg : g ∈ xs) : SameSide (t b) (u b) (g.2 b) := by
      obtain ⟨hl,he⟩ := ho b f (by simp) g (hin _ hg)
      have hlt : t b < g.2 b ↔ f.1 b < g.1 b := by rw [←hland b g hg]; exact (F b).lt_iff_lt
      have heq : t b = g.2 b ↔ f.1 b = g.1 b := by rw [←hland b g hg]; exact (F b).injective.eq_iff
      exact ⟨hlt.trans hl,heq.trans he⟩
    have oldSide b : ∀ s ∈ old.map (fun s => s b), SameSide (t b) (u b) s := by
      simp only [old,List.map_map,List.mem_map,forall_exists_index,and_imp,Function.comp_apply]
      rintro _ g hg rfl
      exact same b g hg
    let G (b : B) : ℝ ≃o ℝ := (F b).trans
      ((move_mono _ (oldSide b)).orderIsoOfSurjective _ (move_surjective _ (oldSide b)))
    refine ⟨G,?_,?_,?_⟩
    · let Y := xs.map (fun g => fun z : B×ℝ => g.2 z.1)
      have ht : Continuous t := hF.comp (continuous_id.prodMk (hc f (by simp)).1)
      have hY : ∀ s ∈ Y, Continuous s := by
        simp only [Y,List.mem_map,forall_exists_index,and_imp]
        rintro _ g hg rfl
        exact (hc g (hin _ hg)).2.comp continuous_fst
      have hY' (z : B×ℝ) : ∀ s ∈ Y, SameSide (t z.1) (u z.1) (s z) := by
        simp only [Y,List.mem_map,forall_exists_index,and_imp]
        rintro _ g hg rfl
        exact same _ _ hg
      have HH := move_continuous Y (ht.comp continuous_fst) ((hc f (by simp)).2.comp continuous_fst) hF hY (fun z s hs => hY' z s hs)
      simpa only [G,OrderIso.trans_apply,StrictMono.coe_orderIsoOfSurjective,old,List.map_map,Y,Function.comp_def] using HH
    · intro b k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact move_start _ _ _ (oldSide b)
      · change move _ _ _ (F b (k.1 b)) = k.2 b
        rw [hland b k hk]
        exact move_fixed _ _ _ (List.mem_map.mpr ⟨k.2,List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩)
    · intro b h x
      have hh := hid b (fun g hg => h g (hin _ hg))
      change move (F b (f.1 b)) (f.2 b) _ (F b x) = x
      rw [hh,hh,h f (by simp),move_same]

end ReluStability
