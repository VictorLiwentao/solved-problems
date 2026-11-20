module

public import SolvedProblems.PackingPowersModel

public section

namespace PackingPowers

private def block {n b c} : Site n b c → Fin (n+2)
  | .l i | .r i => i
  | .a i | .mid i _ => i.castSucc
  | .tail i _ => i.succ

private def phase {n b c} : Site n b c → Nat
  | .l _ => 0
  | .a _ | .tail _ _ => 1
  | .r _ => 2
  | .mid _ _ => 3

private def region {n b c} (x : Site n b c) := 4*(block x).val + phase x

private def cut {n b} (s : Fin n → Fin (b+1)) (i : Fin (n+1)) : Nat :=
  if h : 0 < i.val then (s ⟨i.val-1, by have := i.isLt; omega⟩).val else 0

private def tie {n b c} (s : Fin n → Fin (b+1)) : Site n b c → Nat
  | .l _ | .r _ => 0
  | .a i => 2*cut s i
  | .mid _ t => t.val
  | .tail _ t => 2*t.val+1

private def before {n b c} (s : Fin n → Fin (b+1)) (x y : Site n b c) : Prop :=
  region x < region y ∨ region x = region y ∧ tie s x < tie s y

private theorem key_inj {n b c} (s : Fin n → Fin (b+1)) (x y : Site n b c)
    (hr : region x = region y) (ht : tie s x = tie s y) : x = y := by
  cases x <;> cases y <;> simp [region,phase,block,tie, Fin.ext_iff] at * <;> omega

private def standard {n b c} (s : Fin n → Fin (b+1)) : Packing n b c := by
  refine ⟨before s,?_,?_,?_,?_⟩
  · intro x; simp [before]
  · intro x y z; unfold before; omega
  · intro x y ne
    apply Classical.byContradiction
    intro neither
    apply ne
    apply key_inj s x y <;> unfold before at neither <;> omega
  · intro i
    simp [Window, before, region,block,phase,tie]
    exact ⟨by omega,fun _ => by omega, fun _ _ h => h, fun _ _ h => h⟩

private theorem trans {n b c} (p : Packing n b c) {x y z} : p.val x y → p.val y z → p.val x z :=
  p.property.2.1 x y z

private theorem window {n b c} (p : Packing n b c) (i) : Window p.val i := p.property.2.2.2 i

private theorem leftRight {n b c} (p : Packing n b c) (i : Fin (n+2)) :
    p.val (.l i) (.r i) := by
  by_cases h : i.val < n+1
  · let a : Fin (n+1) := ⟨i,h⟩
    exact trans p (window p a).1 (window p a).2.1
  · let a : Fin (n+1) := ⟨i-1,by have := i.isLt; omega⟩
    have e : a.succ = i := Fin.ext (by dsimp [a]; omega)
    exact e ▸ (window p a).2.2.2.1

private theorem leftChain {n b c} (p : Packing n b c) (i j : Fin (n+2)) (h : i < j) :
    p.val (.l i) (.l j) := by
  suffices aux : ∀ z, ∀ hz : z < n+2, i.val < z → p.val (.l i) (.l ⟨z,hz⟩) by
    exact aux j j.isLt h
  intro z
  induction z with
  | zero => intro hz h; omega
  | succ z ih =>
    intro hz hz'
    let a : Fin (n+1) := ⟨z,by omega⟩
    have edge := trans p (leftRight p a.castSucc) (window p a).2.2.1
    by_cases he : i.val = z
    · have hi : i = a.castSucc := Fin.ext he
      exact hi ▸ edge
    · exact trans p (ih (by omega) (by omega)) edge

private theorem leftStep {n b c} (p : Packing n b c) (x : Site n b c) :
    x = .l (block x) ∨ p.val (.l (block x)) x := by
  cases x with
  | l i => exact Or.inl rfl
  | r i => exact Or.inr (leftRight p i)
  | a i => exact Or.inr (window p i).1
  | mid i t => exact Or.inr (trans p (leftRight p i.castSucc) ((window p i).2.2.2.2.1 t).1)
  | tail i t => exact Or.inr (((window p i).2.2.2.2.2.2.1 t).1)

private theorem stepNext {n b c} (p : Packing n b c) (x : Site n b c) (j : Fin (n+2))
    (h : block x < j) : p.val x (.l j) := by
  let i : Fin (n+1) := ⟨(block x).val,by have := j.isLt; change (block x).val < j.val at h; omega⟩
  have hb : block x = i.castSucc := rfl
  have next := (window p i).2.2.1
  have hx : p.val x (.l i.succ) := by
    cases x with
    | l a => exact trans p (leftRight p i.castSucc) next
    | r a => exact next
    | a a => exact trans p (window p a).2.1 next
    | mid a t => exact ((window p a).2.2.2.2.1 t).2
    | tail a t => exact trans p ((window p a).2.2.2.2.2.2.1 t).2 next
  by_cases e : i.succ.val = j.val
  · exact Fin.ext e ▸ hx
  · exact trans p hx (leftChain p i.succ j (by change (block x).val+1 < j.val; change (block x).val < j.val at h; change ¬(block x).val+1 = j.val at e; omega))

private theorem regionOrdered {n b c} (p : Packing n b c) (x y : Site n b c)
    (h : region x < region y) : p.val x y := by
  by_cases bl : block x < block y
  · have a := stepNext p x (block y) bl
    rcases leftStep p y with e|e
    · rw [e] at * <;> assumption
    · exact trans p a e
  have small (v : Site n b c) : phase v < 4 := by cases v <;> simp [phase]
  have be : block x = block y := Fin.ext (by
    have := small x; have := small y; unfold region at h; change ¬(block x).val < (block y).val at bl; omega)
  have ph : phase x < phase y := by unfold region at h; rw [be] at h; omega
  have belowR (v : Site n b c) (hp : phase v < 2) : p.val v (.r (block v)) := by
    cases v with
    | l i => exact leftRight p i
    | a i => exact (window p i).2.1
    | tail i t => exact ((window p i).2.2.2.2.2.2.1 t).2
    | r i | mid i _ => simp [phase] at hp
  cases y with
  | l i => simp [phase] at ph
  | a i =>
    have e : x = .l (block x) := by cases x <;> simp_all [phase,block]
    exact e ▸ be ▸ (window p i).1
  | tail i t =>
    have e : x = .l (block x) := by cases x <;> simp_all [phase,block]
    exact e ▸ be ▸ ((window p i).2.2.2.2.2.2.1 t).1
  | r i => have v := belowR x ph; rw [be] at v; exact v
  | mid i t =>
    have end' := ((window p i).2.2.2.2.1 t).1
    by_cases hr : phase x < 2
    · have v := belowR x hr; rw [be] at v; exact trans p v end'
    · have e : x = .r (block x) := by cases x <;> simp_all [phase,block]
      exact e ▸ be ▸ end'

private theorem least {P : Nat → Prop} (h : ∃ i, P i) :
    ∃ i, P i ∧ ∀ k, P k → i ≤ k := by
  classical
  obtain ⟨i, hi⟩ := h
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases lower : ∃ k < i, P k
    · obtain ⟨k, hk, hpk⟩ := lower
      exact ih k hk hpk
    · exact ⟨i, hi, fun k hk => Nat.le_of_not_gt fun hki => lower ⟨k,hki,hk⟩⟩

private theorem threshold {b} (q : Fin b → Prop)
    (down : ∀ a z, a < z → q z → q a) :
    ∃ k : Fin (b+1), ∀ t, q t ↔ t.val < k.val := by
  classical
  let missing (i : Nat) := ∀ t : Fin b, t.val = i → ¬ q t
  have hb : missing b := fun t eq => by have := t.isLt; omega
  obtain ⟨v,hv,minimal⟩ := least (P := missing) ⟨b,hb⟩
  have lim := minimal b hb
  refine ⟨⟨v,by omega⟩,fun t => ⟨?_,?_⟩⟩
  · intro hit
    change t.val < v
    apply Classical.byContradiction
    intro ge
    have ht := t.isLt
    let lo : Fin b := ⟨v,by omega⟩
    have hl := hv lo rfl
    by_cases eq : v = t.val
    · exact hl ((show lo = t from Fin.ext eq).symm ▸ hit)
    · exact hl (down lo t (show v < t.val by omega) hit)
  · intro h
    apply Classical.byContradiction
    intro no
    have lower := minimal t.val (fun z hz => by simpa [show z=t from Fin.ext hz] using no)
    change t.val < v at h
    omega

private theorem cut_succ {n b} (s : Fin n → Fin (b+1)) (i : Fin n) :
    cut s i.succ = (s i).val := by simp [cut]

private theorem cutSpec {n b c} (p : Packing n b c) (i : Fin n) :
    ∃ k : Fin (b+1), ∀ t, p.val (.tail i.castSucc t) (.a i.succ) ↔ t.val < k.val := by
  apply threshold
  intro a z h hz
  exact trans p ((window p i.castSucc).2.2.2.2.2.2.2 a z h) hz

private theorem gap {n b c} (s : Fin n → Fin (b+1)) (i : Fin n) (t : Fin b) :
    (standard (c:=c) s).val (.tail i.castSucc t) (.a i.succ) ↔ t.val < (s i).val := by
  change before s _ _ ↔ _
  simp [before,region,block,phase,tie,cut_succ]
  omega

private theorem tieOrdered {n b c} (p : Packing n b c) (s : Fin n → Fin (b+1))
    (spec : ∀ i t, p.val (.tail i.castSucc t) (.a i.succ) ↔ t.val < (s i).val)
    (x y : Site n b c) (hr : region x = region y) (ht : tie s x < tie s y) :
    p.val x y := by
  cases x <;> cases y <;> simp [region,block,phase,tie] at hr ht <;> try omega
  case a.a i j =>
    have e : i = j := Fin.ext (by omega)
    subst j
    omega
  case a.tail i j t =>
    have e : i.val = j.val+1 := by omega
    let k : Fin n := ⟨j.val, by have := i.isLt; omega⟩
    have ej : j = k.castSucc := rfl
    have ei : i = k.succ := Fin.ext e
    rw [ei,cut_succ] at ht
    rw [ej, ei]
    rcases p.property.2.2.1 (.a k.succ) (.tail k.castSucc t) (by simp) with a|a
    · exact a
    · have := (spec k t).mp a; omega
  case mid.mid i a j z =>
    have e : i = j := Fin.ext (by omega)
    subst j
    exact (window p i).2.2.2.2.2.1 a z ht
  case tail.a i t j =>
    have e : j.val = i.val+1 := by omega
    let k : Fin n := ⟨i.val,by have := j.isLt; omega⟩
    have ei : i = k.castSucc := rfl
    have ej : j = k.succ := Fin.ext e
    rw [ej,cut_succ] at ht
    rw [ei,ej]
    exact (spec k t).mpr (by omega)
  case tail.tail i a j z =>
    have e : i = j := Fin.ext (by omega)
    subst j
    exact (window p i).2.2.2.2.2.2.2 a z (by change a.val < z.val; omega)

private theorem surj {n b c} (p : Packing n b c) :
    ∃ s : Fin n → Fin (b+1), standard s = p := by
  classical
  let s i := (cutSpec p i).choose
  have spec i := (cutSpec p i).choose_spec
  have forward : ∀ x y, before s x y → p.val x y := by
    intro x y h
    rcases h with r|⟨r,t⟩
    · exact regionOrdered p x y r
    · exact tieOrdered p s spec x y r t
  refine ⟨s,Subtype.ext (funext fun x => funext fun y => propext ⟨forward x y,?_⟩)⟩
  intro h
  have ne : x ≠ y := fun eq => p.property.1 _ (eq ▸ h)
  rcases (standard (c:=c) s).property.2.2.1 x y ne with v|v
  · exact v
  · exact False.elim (p.property.1 _ (trans p h (forward y x v)))

private theorem inj {n b c} (s t : Fin n → Fin (b+1)) (h : standard (c:=c) s = standard t) :
    s = t := by
  funext i
  have read (m : Fin b) : m.val < (s i).val ↔ m.val < (t i).val := by
    rw [←gap (c:=c) s i m, ←gap (c:=c) t i m, h]
  apply Fin.ext
  by_cases a : (s i).val < (t i).val
  · have eq := read ⟨(s i).val, by have := (t i).isLt; omega⟩
    simp at eq
    omega
  · by_cases b' : (t i).val < (s i).val
    · have eq := read ⟨(t i).val, by have := (s i).isLt; omega⟩
      simp at eq
      omega
    · omega

private def row {n b c} : Site n b c → Nat
  | .l i | .r i | .a i | .mid i _ | .tail i _ => i.val

private def offset {n b c} : Site n b c → Nat
  | .l _ => 0
  | .r _ => 1
  | .a _ => 2
  | .mid _ t => 3+t.val
  | .tail _ t => 3+c+t.val

private theorem layout {n b c} (x : Site n b c) :
    position x = row x * (b+c+3) + offset x ∧ offset x < b+c+3 := by
  cases x <;> simp [position,row,offset,Nat.add_assoc] <;> omega

private theorem rowOffset {n b c} (x y : Site n b c) (h : position x = position y) :
    x = y := by
  let d := b+c+3
  have hd : d > 0 := by dsimp [d]; omega
  have quot (z : Site n b c) : position z / d = row z := by
    have e := (layout z).1
    change position z = row z*d+offset z at e
    rw [e,Nat.mul_comm (row z) d,Nat.mul_add_div hd,Nat.div_eq_of_lt (layout z).2,Nat.add_zero]
  have rem (z : Site n b c) : position z % d = offset z := by
    rw [(layout z).1,Nat.mul_add_mod_of_lt (layout z).2]
  have a := (quot x).symm.trans ((congrArg (fun z => z / d) h).trans (quot y))
  have b' := (rem x).symm.trans ((congrArg (fun z => z % d) h).trans (rem y))
  cases x <;> cases y <;> simp [row,offset,Fin.ext_iff] at * <;> omega

private theorem physical (n b c : Nat) : Physical n b c := by
  let d := b+c+3
  have hd : d > 0 := by dsimp [d]; omega
  refine ⟨rowOffset,?_,?_⟩
  · intro x
    by_cases hi : row x < n+1
    · have lim := Nat.mul_le_mul_right d (show row x + 1 ≤ n+1 by omega)
      rw [Nat.succ_mul] at lim
      have e := (layout x).1
      have lo := (layout x).2
      change position x = row x*d+offset x at e
      change offset x < d at lo
      change position x < (n+1)*d+2
      omega
    · cases x with
      | l i | r i =>
        simp only [row] at hi
        have h : i.val=n+1 := by have := i.isLt; omega
        simp [position,h]
      | a i | mid i _ | tail i _ => simp only [row] at hi; exact False.elim (hi i.isLt)
  · intro z hz
    change z < (n+1)*d+2 at hz
    by_cases e : z < (n+1)*d
    · let i : Fin (n+1) := ⟨z/d,(Nat.div_lt_iff_lt_mul hd).mpr e⟩
      let t := z%d
      have ht : t < d := Nat.mod_lt _ hd
      have eq : i.val*d + t = z := Nat.div_add_mod' _ _
      by_cases t0 : t=0
      · exact ⟨.l i.castSucc,by change i.val*d=z; omega⟩
      by_cases t1 : t=1
      · exact ⟨.r i.castSucc,by change i.val*d+1=z; omega⟩
      by_cases t2 : t=2
      · exact ⟨.a i,by change i.val*d+2=z; omega⟩
      by_cases mid : t < 3+c
      · exact ⟨.mid i ⟨t-3,by omega⟩,by change i.val*d+3+(t-3)=z; omega⟩
      · change t < b+c+3 at ht
        exact ⟨.tail i ⟨t-(3+c),by omega⟩,by change i.val*d+3+c+(t-(3+c))=z; omega⟩
    · let j : Fin (n+2) := ⟨n+1,by omega⟩
      by_cases eq : z = (n+1)*d
      · exact ⟨.l j,eq.symm⟩
      · exact ⟨.r j,by change (n+1)*d+1=z; omega⟩

/-- Enumerate the length-n choice strings by their base-k numeral, with the
least significant digit at the first boundary. -/
private theorem digits {k : Nat} (hk : 0 < k) (n : Nat) :
    ∃ e : Fin (k^n) → (Fin n → Fin k),
      (∀ x y, e x = e y → x = y) ∧ ∀ f, ∃ x, e x = f := by
  induction n with
  | zero =>
    refine ⟨fun _ => Fin.elim0,fun x y _ => Fin.ext (by have := x.isLt; have := y.isLt; simp at *; omega),?_⟩
    exact fun f => ⟨⟨0,by simp⟩,funext (fun i => Fin.elim0 i)⟩
  | succ n ih =>
    obtain ⟨d,di,ds⟩ := ih
    let hi (x : Fin (k^(n+1))) : Fin (k^n) :=
      ⟨x.val/k, (Nat.div_lt_iff_lt_mul hk).mpr (by simpa [Nat.pow_succ] using x.isLt)⟩
    let lo (x : Fin (k^(n+1))) : Fin k := ⟨x.val%k,Nat.mod_lt _ hk⟩
    refine ⟨fun x => Fin.cases (lo x) (d (hi x)),?_,?_⟩
    · intro x y h
      have low : lo x = lo y := congrFun h 0
      have high := di _ _ (funext (fun i => show d (hi x) i = d (hi y) i from congrFun h i.succ))
      have l : x.val%k = y.val%k := congrArg Fin.val low
      have q : x.val/k = y.val/k := congrArg Fin.val high
      exact Fin.ext (by rw [←Nat.div_add_mod' x.val k, ←Nat.div_add_mod' y.val k, q, l])
    · intro f
      obtain ⟨z,hz⟩ := ds (fun i => f i.succ)
      let x : Fin (k^(n+1)) := ⟨z.val*k+(f 0).val,by
        rw [Nat.pow_succ]
        have m := Nat.mul_le_mul_right k (show z.val+1 ≤ k^n from z.isLt)
        rw [Nat.succ_mul] at m
        have := (f 0).isLt
        omega⟩
      have l : lo x = f 0 := Fin.ext (Nat.mul_add_mod_of_lt (f 0).isLt)
      have q : hi x = z := Fin.ext (by
        change (z.val*k+(f 0).val)/k = z.val
        rw [Nat.mul_comm z.val k,Nat.mul_add_div hk,Nat.div_eq_of_lt (f 0).isLt,Nat.add_zero])
      exact ⟨x,funext (Fin.cases l (fun i => show d (hi x) i = f i.succ by rw [q,hz]))⟩

/-- The overlap-two pattern gives k choices independently at each interior boundary. -/
theorem everyPower {k K : Nat} (positive : 1 ≤ k) (length : k+4 ≤ K) :
    ∃ b c : Nat, b+c+5 = K ∧ ∀ n,
      Physical n b c ∧ ∃ f : Fin (k^n) → Packing n b c,
        (∀ s t, f s = f t → s = t) ∧ ∀ p, ∃ s, f s = p := by
  cases k with
  | zero => omega
  | succ b =>
    let c := K-(b+5)
    refine ⟨b,c,by dsimp [c]; omega,?_⟩
    intro n
    obtain ⟨e,ei,es⟩ := digits positive n
    refine ⟨physical n b c,fun v => standard (e v),fun x y h => ei _ _ (inj _ _ h),?_⟩
    intro p
    obtain ⟨s,hs⟩ := surj p
    obtain ⟨v,hv⟩ := es s
    exact ⟨v,(congrArg standard hv).trans hs⟩

end PackingPowers
