module

public import SolvedProblems.FactorWindows

@[expose] public section

namespace PackingFactorization

def limit (K n : Nat) := 3*((n+1)*K)

theorem limit_mono (K n) : limit K n ≤ limit K (n+1) := by
  unfold limit; rw [Nat.succ_mul (n+1)]; omega

theorem fresh_ge (K r n i) : limit K n ≤ fresh K r n i := by
  unfold fresh limit; split <;> omega

theorem fresh_lt (K r n) (i : Fin K) : fresh K r n i.val < limit K (n+1) := by
  unfold fresh limit; rw [Nat.succ_mul (n+1)]; split <;> omega

theorem fresh_inj (K r n) {i j : Nat} : fresh K r n i = fresh K r n j → i=j := by
  unfold fresh; split <;> omega

theorem initial_shared {K} {p : Pattern K} (r) (m : Overlap p) (i : Fin m.size) :
    initial r m (slot m (!r) i) = 3*i.val+1 := by
  simp [initial,slot_shared,local_slot]

theorem initial_lt {K} {p : Pattern K} (r) (m : Overlap p) (i) : initial r m i < limit K 1 := by
  unfold initial
  split
  next h =>
    have := (seamIndex m (!r) i h).isLt
    have := m.proper
    simp only [limit,Nat.reduceAdd,Nat.two_mul]
    omega
  next => exact fresh_lt K r 0 i

theorem initial_inj {K} {p : Pattern K} (r) (m : Overlap p) : Function.Injective (initial r m) := by
  intro i j eq
  unfold initial at eq
  split at eq <;> rename_i ei
  · split at eq <;> rename_i ej
    · have e : seamIndex m (!r) i ei = seamIndex m (!r) j ej := Fin.ext (by omega)
      exact (slot_local m _ i ei).symm.trans ((congrArg (slot m (!r)) e).trans (slot_local m _ j ej))
    · have lt := (seamIndex m (!r) i ei).isLt
      have ge := fresh_ge K r 0 j.val
      simp [limit] at ge
      have := m.proper
      omega
  · split at eq <;> rename_i ej
    · have lt := (seamIndex m (!r) j ej).isLt
      have ge := fresh_ge K r 0 i.val
      simp [limit] at ge
      have := m.proper
      omega
    · exact Fin.ext (fresh_inj _ _ _ eq)

theorem attach_shared {K} {p : Pattern K} (r) (m : Overlap p) (v n) (i : Fin m.size) :
    attach r m v n (slot m (!r) i) = v (slot m r i) := by
  simp [attach,slot_shared,local_slot]

theorem attach_lt {K} {p : Pattern K} (r) (m : Overlap p) (v n) (low : ∀ i, v i < limit K n) (i) :
    attach r m v n i < limit K (n+1) := by
  unfold attach
  split
  · exact lt_of_lt_of_le (low _) (limit_mono _ _)
  · exact fresh_lt K r n i

theorem attach_inj {K} {p : Pattern K} (r) (m : Overlap p) (v n)
    (low : ∀ i, v i < limit K n) (inj : Function.Injective v) :
    Function.Injective (attach r m v n) := by
  intro i j eq
  unfold attach at eq
  split at eq <;> rename_i ei
  · split at eq <;> rename_i ej
    · have e := inj eq
      have f := congrArg (fun x => seamIndex m r x.val x.property)
        (show (⟨_,slot_shared m r (seamIndex m (!r) i ei)⟩ : {t // shared m r t}) =
          ⟨_,slot_shared m r (seamIndex m (!r) j ej)⟩ from Subtype.ext e)
      simp only [local_slot] at f
      exact (slot_local m _ i ei).symm.trans ((congrArg (slot m (!r)) f).trans (slot_local m _ j ej))
    · have := low (slot m r (seamIndex m (!r) i ei))
      have := fresh_ge K r n j.val
      omega
  · split at eq <;> rename_i ej
    · have := low (slot m r (seamIndex m (!r) j ej))
      have := fresh_ge K r n i.val
      omega
    · exact Fin.ext (fresh_inj _ _ _ eq)

/-- A set of physical positions cuts a given window after exactly its first c ranks. -/
def Aligned {K} (p : Pattern K) (keep : Nat → Prop) (v : Fin K → Nat) (c : Cut K) :=
  ∀ i, keep (v i) ↔ (p i).val < c.val

def AlignedAll {K} (p : Pattern K) (keep : Nat → Prop) :=
  List.Forall₂ (Aligned p keep)

theorem sameAnchor {K} {p : Pattern K} {a : Overlap p} {r c d} (eq : Cross r a c d)
    (i : Fin a.size) : (p (slot a r i)).val < c.val ↔ (p (slot a (!r) i)).val < d.val := by
  have e := members_eq a r eq
  exact (show i ∈ anchors a r c ↔ i ∈ anchors a (!r) d from e ▸ Iff.rfl) |>
    (fun h => by simpa [anchors] using h)

private theorem realizeAux {K} {p : Pattern K} {r c w ds} (walk : @Walk K p r c w ds)
    (v : Fin K → Nat) (n) (low : ∀ i, v i < limit K n) (keep : Nat → Prop)
    (init : Aligned p keep v c) :
    ∃ pred : Nat → Prop, (∀ x < limit K n, pred x ↔ keep x) ∧
      AlignedAll p pred (framesAux r v n w) (c::ds) := by
  induction walk generalizing v n keep with
  | nil => exact ⟨keep,fun _ _ => Iff.rfl,.cons init .nil⟩
  | @step a c d w ds cross walk ih =>
    let next (x : Nat) := if x < limit K n then keep x else
      ∃ i : Fin K, x=fresh K r n i.val ∧ (p i).val < d.val
    have agree (x) (h : x < limit K n) : next x ↔ keep x := by simp [next,h]
    have aligned : Aligned p next (attach r a v n) d := by
      intro i
      unfold attach
      split
      next h =>
        let t := seamIndex a (!r) i h
        calc
          next (v (slot a r t)) ↔ keep (v (slot a r t)) := agree _ (low _)
          _ ↔ (p (slot a r t)).val < c.val := init _
          _ ↔ (p i).val < d.val := by simpa only [t,slot_local] using sameAnchor cross t
      next h =>
        simp only [next, ite_eq_right (Nat.not_lt_of_ge (fresh_ge K r n i.val))]
        constructor
        · rintro ⟨j,eq,hj⟩
          have : i=j := Fin.ext (fresh_inj _ _ _ eq)
          simpa [this] using hj
        · exact fun hi => ⟨i,rfl,hi⟩
    obtain ⟨pred,old,all⟩ := ih _ (n+1) (attach_lt r a v n low) next aligned
    have persist (x) (h : x < limit K n) : pred x ↔ keep x :=
      (old x (lt_of_lt_of_le h (limit_mono _ _))).trans (agree x h)
    exact ⟨pred,persist,.cons (fun i => (persist _ (low i)).trans (init i)) all⟩

theorem realize {K} {p : Pattern K} {r m h w cs} (profile : @Profile K p r m h w cs) :
    ∃ pred : Nat → Prop, AlignedAll p pred (frames r m w) cs := by
  obtain ⟨c,ds,rfl,_,walk⟩ := profile
  let keep (x : Nat) := ∃ i, initial r m i=x ∧ (p i).val<c.val
  have hi : Aligned p keep (initial r m) c := by
    intro i
    exact ⟨fun ⟨j,eq,hj⟩ => initial_inj r m eq ▸ hj, fun h => ⟨i,rfl,h⟩⟩
  obtain ⟨pred,_,align⟩ := realizeAux walk _ 1 (initial_lt r m) keep hi
  exact ⟨pred,align⟩

end PackingFactorization
