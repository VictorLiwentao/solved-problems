module

public import SolvedProblems.SelectedLaw

public section

namespace SelectedDisagreement

private theorem weight_zero (p : Point → ℝ) (f) : weight p 0 f = 0 := rfl
private theorem weight_step (p : Point → ℝ) (k : Nat) (f) : weight p (k+1) f =
    weight p k f + p (.ordinary k) * f (.ordinary k) + p (.marker k) * f (.marker k) := rfl

theorem wmono {p : Point → ℝ} (hp : ∀ x, 0 ≤ p x) (k : Nat) {f g : Point → ℝ}
    (h : ∀ x, f x ≤ g x) : weight p k f ≤ weight p k g := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [weight_step, weight_step]
    exact add_le_add (add_le_add ih (mul_le_mul_of_nonneg_left (h _) (hp _)))
      (mul_le_mul_of_nonneg_left (h _) (hp _))

theorem wadd (p : Point → ℝ) (k) (f g : Point → ℝ) :
    weight p k (fun x => f x + g x) = weight p k f + weight p k g := by
  induction k with
  | zero => simp [weight_zero]
  | succ k ih => simp only [weight_step, ih, mul_add]; ac_rfl

theorem wscale (p : Point → ℝ) (k) (c : ℝ) (f : Point → ℝ) :
    weight p k (fun x => c * f x) = c * weight p k f := by
  induction k with
  | zero => simp [weight_zero]
  | succ k ih => simp only [weight_step, ih, mul_add]; ac_rfl

theorem wconst (p : Point → ℝ) (k) (c : ℝ) :
    weight p k (fun _ => c) = c * weight p k (fun _ => 1) := by
  simpa using wscale p k c (fun _ => 1)

theorem wpos {p : Point → ℝ} (hp : ∀ x, 0 ≤ p x) (k) {f : Point → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ weight p k f := by
  have le := wmono hp k h
  rwa [wconst, zero_mul] at le

theorem wlength {p : Point → ℝ} (hp : ∀ x, 0 ≤ p x) {f : Point → ℝ} (h : ∀ x, 0 ≤ f x)
    {j k : Nat} (hle : j ≤ k) : weight p j f ≤ weight p k f := by
  induction hle with
  | refl => exact le_rfl
  | step _ ih =>
    rw [weight_step]
    exact le_trans (le_trans ih (le_add_of_nonneg_right (mul_nonneg (hp _) (h _))))
      (le_add_of_nonneg_right (mul_nonneg (hp _) (h _)))

private theorem wexchange (p : Point → ℝ) (j k) (f : Point → Point → ℝ) :
    weight p j (fun x => weight p k (f x)) = weight p k (fun y => weight p j (fun x => f x y)) := by
  induction k with
  | zero => simp only [weight_zero]; rw [wconst, zero_mul]
  | succ k ih =>
    simp only [weight_step, wadd, wscale, ih]

private theorem izero (p : Point → ℝ) (k) (f) : iid p k 0 f = f [] := rfl
private theorem istep (p : Point → ℝ) (k m) (f) :
    iid p k (m+1) f = weight p k (fun x => iid p k m (fun s => f (x::s))) := rfl

theorem imono {p : Point → ℝ} (hp : ∀ x, 0 ≤ p x) (k m) {f g : List Point → ℝ}
    (h : ∀ s, f s ≤ g s) : iid p k m f ≤ iid p k m g := by
  induction m generalizing f g with
  | zero => exact h []
  | succ m ih => rw [istep,istep]; exact wmono hp k (fun x => ih (fun s => h (x::s)))

theorem iadd (p : Point → ℝ) (k m) (f g : List Point → ℝ) :
    iid p k m (fun s => f s + g s) = iid p k m f + iid p k m g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih => simp only [istep, ih, wadd]

theorem iscale (p : Point → ℝ) (k m) (c : ℝ) (f : List Point → ℝ) :
    iid p k m (fun s => c * f s) = c * iid p k m f := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => simp only [istep, ih, wscale]

/-- Sum a test over all distinguished sample positions, giving it the point there and the
remaining sample in its original order. -/
noncomputable def nominations (f : Point → List Point → ℝ) : List Point → ℝ
  | [] => 0
  | x::s => f x s + nominations (fun y t => f y (x::t)) s

theorem nominations_nonneg {f : Point → List Point → ℝ} (h : ∀ x s, 0 ≤ f x s) (s) :
    0 ≤ nominations f s := by
  induction s generalizing f with
  | nil => exact le_rfl
  | cons x s ih => exact add_nonneg (h x s) (ih (fun y t => h y (x::t)))

theorem nomination_mem {f : Point → List Point → ℝ} (h : ∀ x s, 0 ≤ f x s)
    {x : Point} {s : List Point} (hx : x ∈ s) (w : ∀ u, (∀ y ∈ u, y ∈ s) → 1 ≤ f x u) :
    1 ≤ nominations f s := by
  induction s generalizing f with
  | nil => simp at hx
  | cons y s ih =>
    rw [nominations]
    rcases List.mem_cons.mp hx with rfl | hm
    · exact le_add_of_le_of_nonneg (w _ (by simp_all)) (nominations_nonneg (fun z t => h z (x::t)) _)
    · apply le_add_of_nonneg_of_le (h _ _)
      apply ih (fun z t => h z (y::t)) hm
      intro u hu
      apply w
      simp only [List.mem_cons]
      exact fun z hz => hz.imp id (hu z)

theorem iid_nominations (p : Point → ℝ) (k m) (f : Point → List Point → ℝ) :
    iid p k (m+1) (nominations f) =
      (m+1 : Nat) * weight p k (fun x => iid p k m (f x)) := by
  induction m generalizing f with
  | zero => simp only [istep, izero, nominations, add_zero, Nat.zero_add, Nat.cast_one, one_mul]
  | succ m ih =>
    have term (x : Point) : iid p k (m+1) (fun s => nominations f (x::s)) =
        iid p k (m+1) (f x) + (m+1 : Nat) *
          weight p k (fun y => iid p k m (fun s => f y (x::s))) := by
      change iid p k (m+1) (fun s => f x s + nominations (fun y u => f y (x::u)) s) = _
      rw [iadd, ih]
    change weight p k (fun x => iid p k (m+1) (fun s => nominations f (x::s))) = _
    simp only [term, wadd, wscale]
    rw [wexchange p k k (fun x y => iid p k m (fun t => f y (x::t)))]
    change _ + _ * weight p k (fun x => iid p k (m+1) (f x)) = _
    simp only [Nat.cast_succ, add_mul, one_mul]
    ac_rfl

end SelectedDisagreement
