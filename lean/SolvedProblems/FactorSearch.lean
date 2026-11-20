module

public import SolvedProblems.FactorCuts

@[expose] public section

namespace PackingFactorization

/-- Lists of letters from the supplied alphabet of length at most n. -/
def boundedWords (A : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => [] :: A.flatMap (fun a => (boundedWords A n).map (a :: ·))

theorem boundedWords_spec (A : List α) (w : List α) (n : Nat) :
    w ∈ boundedWords A n ↔ w.length ≤ n ∧ ∀ a ∈ w, a ∈ A := by
  induction n generalizing w with
  | zero => cases w <;> simp [boundedWords]
  | succ n ih =>
    cases w with
    | nil => simp [boundedWords]
    | cons a w =>
      simp only [boundedWords,List.mem_cons,List.cons_ne_nil,false_or,List.mem_flatMap,
        List.mem_map,List.cons.injEq,List.length_cons,Nat.add_le_add_iff_right,
        forall_eq_or_imp]
      constructor
      · rintro ⟨b,hb,v,hv,rfl,rfl⟩
        exact ⟨((ih v).mp hv).1,hb,((ih v).mp hv).2⟩
      · rintro ⟨len,ha,hw⟩
        exact ⟨a,ha,w,(ih w).mpr ⟨len,hw⟩,rfl,rfl⟩

/-- Enumerate all possible continuations of a cut for the given overlap word. -/
def cutWalks {K} {p : Pattern K} (r : Bool) (c : Cut K) (w : List (Overlap p)) : List (List (Cut K)) :=
  w.foldr (fun a next x => (List.finRange (K+1)).flatMap (fun d =>
    if anchorCount a r x = anchorCount a (!r) d then (next d).map (d :: ·) else []))
    (fun _ => [[]]) c

private theorem cutWalks_nil {K} {p : Pattern K} (r : Bool) (c : Cut K) :
    cutWalks (p := p) r c [] = [[]] := rfl

private theorem cutWalks_cons {K} {p : Pattern K} (r : Bool) (c : Cut K) (a : Overlap p) (w : List (Overlap p)) :
    cutWalks r c (a::w) = (List.finRange (K+1)).flatMap (fun d =>
      if anchorCount a r c = anchorCount a (!r) d then (cutWalks r d w).map (d :: ·) else []) := rfl

theorem cutWalks_spec {K} {p : Pattern K} (r : Bool) (c : Cut K) (w : List (Overlap p)) (ds) :
    ds ∈ cutWalks r c w ↔ Walk r c w ds := by
  induction w generalizing c ds with
  | nil =>
    constructor
    · simpa [cutWalks_nil] using (show ds=[] → Walk r c [] ds by rintro rfl; exact .nil _)
    · intro h; cases h; simp [cutWalks_nil]
  | cons a w ih =>
    simp only [cutWalks_cons,List.mem_flatMap,List.mem_finRange,true_and]
    constructor
    · rintro ⟨d,hd⟩
      split at hd
      next h =>
        obtain ⟨vs,hv,rfl⟩ := List.mem_map.mp hd
        exact .step h ((ih _ _).mp hv)
      next => simp at hd
    · intro h
      cases h with
      | step next rest =>
        rename_i d vs
        unfold Cross at next
        refine ⟨d,?_⟩
        rw [ite_eq_left next]
        exact List.mem_map.mpr ⟨_,(ih _ _).mpr rest,rfl⟩

/-- A profile records the initial cut as well as its continuation. -/
def cutProfiles {K} {p : Pattern K} (r : Bool) (m : Overlap p) (h : Nat) (w : List (Overlap p)) :=
  (List.finRange (K+1)).flatMap (fun c =>
    if anchorCount m (!r) c = h then (cutWalks r c w).map (c :: ·) else [])

theorem cutProfiles_spec {K} {p : Pattern K} (r : Bool) (m : Overlap p) (h w cs) :
    cs ∈ cutProfiles r m h w ↔ Profile r m h w cs := by
  simp only [cutProfiles,List.mem_flatMap,List.mem_finRange,true_and]
  constructor
  · rintro ⟨c,hc⟩
    split at hc
    next e =>
      obtain ⟨ds,mem,rfl⟩ := List.mem_map.mp hc
      exact ⟨c,ds,rfl,e,(cutWalks_spec ..).mp mem⟩
    next => simp at hc
  · rintro ⟨c,ds,rfl,e,path⟩
    exact ⟨c,by rw [ite_eq_left e]; exact List.mem_map.mpr ⟨ds,(cutWalks_spec ..).mpr path,rfl⟩⟩

def forks {K} {p : Pattern K} (r : Bool) (m : Overlap p) (h : Nat) (w : List (Overlap p)) : Bool :=
  let profiles := cutProfiles r m h w
  profiles.any (fun cs => profiles.any (fun ds => cs != ds))

theorem forks_spec {K} {p : Pattern K} (r : Bool) (m : Overlap p) (h w) :
    forks r m h w = true ↔ TwoProfiles r m h w := by
  simp only [forks,List.any_eq_true,cutProfiles_spec,bne_iff_ne,TwoProfiles]
  constructor
  · rintro ⟨cs,hc,ds,hd,ne⟩
    exact ⟨cs,ds,hc,hd,ne⟩
  · rintro ⟨cs,ds,hc,hd,ne⟩
    exact ⟨cs,hc,ds,hd,ne⟩

/-- Return a concrete short witness when the side can occupy gap h. -/
def markedWord? {K} {p : Pattern K} (A : List (Overlap p)) (r : Bool) (m : Overlap p) (h : Nat) :=
  (boundedWords A (K+1)).find? (forks r m h)

def marked? {K} {p : Pattern K} (A : List (Overlap p)) (r : Bool) (m : Overlap p) (h : Nat) :=
  (markedWord? A r m h).isSome

theorem marked?_spec {K} {p : Pattern K} (A : List (Overlap p)) (r : Bool) (m : Overlap p) (h : Nat) :
    marked? A r m h = true ↔ Marked {a | a ∈ A} r m h := by
  simp only [marked?, markedWord?, List.isSome_find?, List.any_eq_true, boundedWords_spec, forks_spec,
    Marked, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w,⟨len,allowed⟩,fork⟩; exact ⟨w,allowed,len,fork⟩
  · rintro ⟨w,allowed,len,fork⟩; exact ⟨w,⟨len,allowed⟩,fork⟩

theorem markedWord?_sound {K} {p : Pattern K} {A : List (Overlap p)} {r} {m : Overlap p} {h w}
    (returned : markedWord? A r m h = some w) :
    (∀ a ∈ w, a ∈ A) ∧ w.length ≤ K+1 ∧ TwoProfiles r m h w := by
  have hw := (boundedWords_spec A w (K+1)).mp (List.mem_of_find?_eq_some returned)
  exact ⟨hw.2,hw.1,(forks_spec ..).mp (List.find?_some returned)⟩

end PackingFactorization
