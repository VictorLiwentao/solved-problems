module

public import SolvedProblems.OnlineCertificatesModel

public section

namespace OnlineCertificates

/-- A certificate search remembers each mistaken label, repeats stored labels, and stops
growing its memory once it reaches the top level on inconsistent data. -/
@[expose] def Rule (E : Nat → Hist) (d : Nat) (A : Machine) : Prop :=
  (∀ s x, Simple s → ∀ b, (x,b) ∈ s → Answers A s x (b,s,s)) ∧
  (∀ s x, Simple s → (∀ b, (x,b) ∉ s) → d < s.length → Answers A s x (false,s,s)) ∧
  ∀ s x, Simple s → (∀ b, (x,b) ∉ s) → s.length ≤ d →
    (∃ b, Listed E ((x,b)::s)) →
      ∃ b, Listed E ((x,b)::s) ∧
        Answers A s x (!b, if b = false then (x,false)::s else s,
                           if b = true then (x,true)::s else s)

private theorem answers_unique {A : Machine} (stable : Stable A) {s x r u}
    (a : Answers A s x r) (b : Answers A s x u) : r = u := by
  obtain ⟨t, ht⟩ := a
  obtain ⟨v, hv⟩ := b
  have ar := stable s x t (max t v) r (Nat.le_max_left ..) ht
  have au := stable s x v (max t v) u (Nat.le_max_right ..) hv
  exact Option.some.inj (ar.symm.trans au)

private theorem restrictRealizes {H h s} (sub : ∀ z ∈ s, z ∈ h)
    (real : Realizes H h) : Realizes H s := by
  obtain ⟨f, hf, ok⟩ := real
  exact ⟨f, hf, fun z hz => ok z (sub z hz)⟩

private theorem simple_cons {s : Hist} {x b} (hs : Simple s)
    (fresh : ∀ c, (x,c) ∉ s) : Simple ((x,b)::s) := by
  apply List.nodup_cons.mpr
  refine ⟨?_, hs⟩
  intro mem
  obtain ⟨⟨a,c⟩, ac, eq⟩ := List.mem_map.mp mem
  change a = x at eq
  subst a
  exact fresh c ac

/-- A stable effective implementation of the certificate search has the advertised mistake bound. -/
theorem fromRule {H : (Nat → Bool) → Prop} {d : Nat} {total : Bool} {E : Nat → Hist}
    {A : Machine} (_small : ∀ i, Simple (E i) ∧ (E i).length ≤ d+1)
    (empty : Listed E []) (stop : ∀ s, Simple s → Listed E s → Realizes H s → s.length ≤ d)
    (extend : ∀ s, Simple s → Listed E s → s.length ≤ d → (total = true ∨ Realizes H s) →
      ∀ x, (∀ b, (x,b) ∉ s) → ∃ b, Listed E ((x,b)::s))
    (prim : Primrec A) (stable : Stable A) (rule : Rule E d A) : Learnable H d total := by
  obtain ⟨repeatAnswer, top, search⟩ := rule
  -- On a legal run the memory stays in the hierarchy. On a realizable run each
  -- stored example accounts for exactly one mistake.
  have inv {h s m} (run : Run A h s m) (legal : total = true ∨ Realizes H h) :
      Simple s ∧ Listed E s ∧ (∀ z ∈ s, z ∈ h) ∧ (Realizes H h → m = s.length) := by
    induction run with
    | nil => exact ⟨by simp [Simple], empty, fun _ hz => hz, fun _ => rfl⟩
    | @step h s m x b r prev ans ih =>
      have tail : Realizes H ((x,b)::h) → Realizes H h :=
        restrictRealizes (fun z hz => List.mem_cons_of_mem _ hz)
      obtain ⟨simpS, listed, sub, count⟩ := ih (legal.imp_right tail)
      have grow (c : Bool) : ∀ z ∈ (x,c)::s, c = b → z ∈ (x,b)::h := by
        rintro z hz rfl
        rcases List.mem_cons.mp hz with rfl | hs
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (sub z hs)
      have old : ∀ z ∈ s, z ∈ (x,b)::h := fun z hz => List.mem_cons_of_mem _ (sub z hz)
      by_cases seen : ∃ c, (x,c) ∈ s
      · obtain ⟨c, hc⟩ := seen
        have eq := answers_unique stable ans (repeatAnswer s x simpS c hc)
        subst r
        simp only [ite_self]
        refine ⟨simpS, listed, old, ?_⟩
        intro real
        have saved := count (tail real)
        obtain ⟨f, _, ok⟩ := real
        have agrees : c = b := (ok (x,c) (old _ hc)).symm.trans (ok (x,b) List.mem_cons_self)
        simpa [agrees] using saved
      · have fresh : ∀ c, (x,c) ∉ s := fun c hc => seen ⟨c,hc⟩
        by_cases low : s.length ≤ d
        · have active := legal.imp_right (fun real => restrictRealizes old real)
          obtain ⟨c, next, predicted⟩ :=
            search s x simpS fresh low (extend s simpS listed low active x fresh)
          have eq := answers_unique stable ans predicted
          subst r
          cases c <;> cases b <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte,
            Nat.add_zero, List.length_cons, Bool.false_eq_true,
            Bool.true_eq_false]
          all_goals first
            | exact ⟨simpS, listed, old, fun real => count (tail real)⟩
            | exact ⟨simple_cons simpS fresh, next, fun z hz => grow _ z hz rfl,
                fun real => by rw [count (tail real)]⟩
        · have eq := answers_unique stable ans (top s x simpS fresh (Nat.lt_of_not_ge low))
          subst r
          simp only [ite_self]
          exact ⟨simpS, listed, old, fun real =>
            (low (stop s simpS listed (restrictRealizes old real))).elim⟩
  refine ⟨A, prim, stable, ?_, ?_⟩
  · intro h s m run legal x
    obtain ⟨hs, listed, sub, _⟩ := inv run legal
    by_cases seen : ∃ c, (x,c) ∈ s
    · obtain ⟨c, hc⟩ := seen
      exact ⟨_, repeatAnswer s x hs c hc⟩
    · have fresh : ∀ c, (x,c) ∉ s := fun c hc => seen ⟨c,hc⟩
      by_cases low : s.length ≤ d
      · obtain ⟨_, _, ans⟩ :=
          search s x hs fresh low (extend s hs listed low (legal.imp_right (restrictRealizes sub)) x fresh)
        exact ⟨_, ans⟩
      · exact ⟨_, top s x hs fresh (Nat.lt_of_not_ge low)⟩
  · intro h s m run real
    obtain ⟨hs, listed, sub, count⟩ := inv run (.inr real)
    rw [count real]
    exact stop s hs listed (restrictRealizes sub real)

end OnlineCertificates
