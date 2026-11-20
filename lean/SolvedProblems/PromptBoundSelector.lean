module

public import SolvedProblems.PromptBoundSelectCandidates

public section
namespace PromptBound
namespace Selector

private def current {q} (h : History q) : Word q := (h.head?.getD ([],[])).2

private def seen {q} (h : History q) := canonical (sample h)

private def answer {q} (C : Family q) (h : History q) (b : ℕ) : Word q :=
  let S := seen h
  let p := current h
  (pool C S (initialPool S p b) h.length).head?.getD p

private def step {q} (C : Family q) (B : BoundStep q) : DetStep q := fun v ↦
  let h := v.1
  let res := B ((seen h,current h),v.2)
  res.map (answer C h)

private theorem effective_step {q} (C : Family q) (X : Oracle) (B : (List (Word q) × Word q) × ℕ → Option ℕ)
    (ef : Effective X B) (mem : Computable (fun u : ℕ × Word q ↦ C u.1 u.2)) :
    Effective X (step C B) := by
  have hsam : Effective X (@sample q) := eff_map (X:=X) (α:=History q) (f:=id) (g:=fun u ↦ u.2.1) eff_id (by fun_prop)
  have hs : Effective X (@seen q) := .comp (f:=sample) (g:=canonical) eff_canonical hsam
  have hc : Effective X (@current q) := by unfold current; fun_prop
  have make : Effective X (fun u : History q × ℕ ↦ initialPool (seen u.1) (current u.1) u.2) :=
    .comp (f:=fun u : History q × ℕ ↦ ((seen u.1,current u.1),u.2)) eff_initialPool (by fun_prop)
  have cut : Effective X (fun u : History q × ℕ ↦ pool C (seen u.1)
      (initialPool (seen u.1) (current u.1) u.2) u.1.length) :=
    .comp (f:=fun u : History q × ℕ ↦ ((seen u.1,initialPool (seen u.1) (current u.1) u.2),u.1.length)) (eff_pool C mem) (by fun_prop)
  have ha : Effective X (fun u : History q × ℕ ↦ answer C u.1 u.2) := by
    exact eff_getD_comp _ _ (.comp eff_head cut) (.comp hc (by fun_prop))
  let result (u : History q × ℕ) := B ((seen u.1,current u.1),u.2)
  have hr : Effective X result := .comp (f:=fun u : History q × ℕ ↦ ((seen u.1,current u.1),u.2)) ef (by fun_prop)
  let out (u : History q × ℕ) :=
    bif (result u).isSome then some (answer C u.1 ((result u).getD 0)) else none
  have outEf : Effective X out := by
    have prod : Effective X (fun u : History q × ℕ ↦ (u.1, (result u).getD 0)) := by fun_prop
    have hanswer := ha.comp prod
    unfold out
    fun_prop
  convert outEf using 1
  funext u
  change (result u).map _ = _
  cases h : result u <;> simp [out,h]

private theorem legal_sample {q} {K : Word q → Bool} {h : History q} (ok : Legal K h) :
    ∀ w ∈ sample h, K w = true := by
  induction h with
  | nil => simp [sample]
  | cons r l ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|tail
    · exact ok.1
    · exact ih ok.2.2 _ tail

private theorem legal_possible {q} {C : Family q} {z : ℕ} {h : History q}
    (hne : h ≠ []) (ok : Legal (C z) h) :
    Possible C (seen h) (current h) ∧ ∃ y, Fresh (C z) (seen h) (current h) y := by
  cases h with
  | nil => contradiction
  | cons r tail =>
    obtain ⟨y,ky,miss,pref⟩ := ok.2.1
    have hit : Fresh (C z) (seen (r::tail)) (current (r::tail)) y :=
      ⟨ky,fun h ↦ miss ((mem_canonical ..).mp h),pref⟩
    have m : r.1 ∈ seen (r::tail) := (mem_canonical ..).mpr (List.mem_cons_self)
    exact ⟨⟨List.ne_nil_of_mem m,z,fun w hw ↦ legal_sample ok w ((mem_canonical ..).mp hw),⟨y,hit⟩⟩,⟨y,hit⟩⟩

private theorem seen_rounds {q} (e : ℕ → Round q) (n : ℕ) (w : Word q) :
    w ∈ seen (rounds e n) ↔ ∃ i < n, (e i).1 = w := by
  rw [seen,mem_canonical]
  simp [sample,rounds,initial]

private theorem eventually_seen {q} {K : Word q → Bool} {e : ℕ → Round q}
    (full : Full K e) (T : List (Word q)) (ok : ∀ w ∈ T, K w = true) :
    ∃ N, ∀ n ≥ N, T ⊆ seen (rounds e (n+1)) := by
  induction T with
  | nil => exact ⟨0,by simp⟩
  | cons w l ih =>
    obtain ⟨N,all⟩ := ih (fun a ha ↦ ok a (List.mem_cons_of_mem _ ha))
    obtain ⟨i,atI⟩ := (full w).mp (ok w List.mem_cons_self)
    refine ⟨max i N,fun n hn x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl|hx
    · exact (seen_rounds ..).mpr ⟨i,by omega,atI⟩
    · exact all _ (by omega) hx

private theorem earlier_survivors {q} (C : Family q) (z : ℕ) {e : ℕ → Round q}
    (full : Full (C z) e) (J : ℕ) : ∃ N, ∀ n ≥ N, ∀ j < J,
      (∀ w ∈ seen (rounds e (n+1)), C j w = true) → ∀ w, C z w = true → C j w = true := by
  induction J with
  | zero => exact ⟨0,by simp⟩
  | succ J ih =>
    obtain ⟨N,early⟩ := ih
    by_cases good : ∀ w, C z w = true → C J w = true
    · refine ⟨N,fun n hn j hj h ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with old|rfl
      · exact early n hn j old h
      · exact good
    · push Not at good
      obtain ⟨x,hx,bad⟩ := good
      obtain ⟨i,atI⟩ := (full x).mp hx
      refine ⟨max i N,fun n hn j hj h ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with old|rfl
      · exact early n (by omega) j old h
      · have mem := (seen_rounds e (n+1) x).mpr ⟨i,by omega,atI⟩
        have := h x mem; simp_all

private theorem round_cons {q} (e : ℕ → Round q) (n) :
    rounds e (n+1) = e n :: rounds e n := by simp [rounds,initial,List.range_succ]

private theorem head_mem {α} {F : List α} (nonempty : F ≠ []) (x : α) :
    F.head?.getD x ∈ F := by cases F <;> simp_all

end Selector

open Selector in
/-- Select a bounded fresh completion from the pool left by all consistent earlier
candidates. After their finite counterexamples have appeared, that pool lies in the target. -/
theorem bound_to_det {q} (C : Family q) (X : Oracle)
    (mem : Computable (fun u : ℕ × Word q ↦ C u.1 u.2)) (h : LengthBound C X) :
    DetGenerates C X := by
  obtain ⟨B,he,stable,total,bounds⟩ := h
  refine ⟨step C B, effective_step C X B he mem, ?_, ?_, ?_⟩
  · intro h t m y htm atT
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp atT
    exact Option.map_eq_some_iff.mpr ⟨b,stable _ _ _ _ _ htm hb,rfl⟩
  · intro i h hne ok
    obtain ⟨t,b,hb⟩ := total _ _ (canon_canonical _) (legal_possible hne ok).1
    exact ⟨t,answer C h b,Option.map_eq_some_iff.mpr ⟨b,hb,rfl⟩⟩
  · intro i e full legal
    obtain ⟨T,Tgood,hT⟩ := bounds i
    obtain ⟨M,all⟩ := eventually_seen full T Tgood
    obtain ⟨N,early⟩ := earlier_survivors C i full i
    refine ⟨max i (max N M),fun n hn ↦ ?_⟩
    let h := rounds e (n+1)
    have ok := legal (n+1)
    have cons : h = e n :: rounds e n := round_cons e n
    have nonempty : h ≠ [] := by rw [cons]; simp
    obtain ⟨possible,witness⟩ := legal_possible nonempty ok
    obtain ⟨t,b,hb⟩ := total (seen h) (current h) (canon_canonical _) possible
    have data : ∀ w ∈ seen h, C i w = true := fun w hw ↦ legal_sample ok w ((mem_canonical ..).mp hw)
    obtain ⟨w,hw,short⟩ := hT _ _ (canon_canonical _) possible.1 (all _ (by omega)) data witness t b hb
    have hit : ∃ y ∈ initialPool (seen h) (current h) b, C i y = true :=
      ⟨w,mem_pool.mpr ⟨short,hw.2⟩,hw.1⟩
    have sz : h.length = n+1 := by simp [h,rounds,initial]
    obtain ⟨alive,correct⟩ := pool_correct C _ _ (z:=i) (t:=h.length) (by omega) data (early _ (by omega)) hit
    have output := correct _ (head_mem alive (current h))
    have matchY := mem_pool.mp output.1
    refine ⟨t,answer C h b,Option.map_eq_some_iff.mpr ⟨b,hb,rfl⟩,
      (e n).1,(e n).2,rounds e n,cons, output.2, ?_, ?_⟩
    · exact fun bad ↦ matchY.2.1 ((mem_canonical ..).mpr bad)
    · have hp : current h = (e n).2 := by rw [cons]; rfl
      rw [← hp]; exact matchY.2.2

end PromptBound
