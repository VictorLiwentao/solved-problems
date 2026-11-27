module

public import SolvedProblems.ReluStabilityForms

@[expose] public section

open SignType Set Filter
open scoped Topology

namespace ReluStability

def Aligns {B : Type*} [TopologicalSpace B] {p d : ℕ} (fs : List (Form p d))
    (θ : Params p) (w : B → Params p) (H : Family B (Input d)) : Prop :=
  ∀ b f, f ∈ fs → ∀ x, sign (f.eval θ x) = sign (f.eval (w b) (H.map b x))

theorem lift_arrangement {B : Type*} [TopologicalSpace B] {p d : ℕ} (fs : List (Form p (d+1)))
    (θ : Params p) (w : B → Params p) (hw : Continuous w)
    (hl : ∀ b f, f ∈ fs → sign (MvPolynomial.eval θ f.lead) = sign (MvPolynomial.eval (w b) f.lead))
    (H : Family B (Input d)) (hh : Aligns (projected fs) θ w H)
    (hid : ∀ b, w b = θ → ∀ x, H.map b x = x) :
    ∃ G : Family B (Input (d+1)), Aligns fs θ w G ∧ ∀ b, w b = θ → ∀ x, G.map b x = x := by
  classical
  let active := fs.filter fun f => MvPolynomial.eval θ f.lead ≠ 0
  let left (f : Form p (d+1)) (z : B×Input d) := f.root θ z.2
  let right (f : Form p (d+1)) (z : B×Input d) := f.root (w z.1) (H.map z.1 z.2)
  let knots := active.map fun f => (left f,right f)
  have nh (b) (f) (hf : f ∈ fs) : MvPolynomial.eval θ f.lead = 0 ↔ MvPolynomial.eval (w b) f.lead = 0 := by
    rw [←sign_eq_zero_iff,←sign_eq_zero_iff (a:=MvPolynomial.eval (w b) f.lead),hl b f hf]
  have hc (k) (hk : k ∈ knots) : Continuous k.1 ∧ Continuous k.2 := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hk
    obtain ⟨hfs,hlead⟩ := List.mem_filter.mp hf
    have hne : MvPolynomial.eval θ f.lead ≠ 0 := by simpa using hlead
    refine ⟨(f.tail.continuous_eval.comp (continuous_const.prodMk continuous_snd)).neg.div_const _,?_⟩
    exact ((f.tail.continuous_eval.comp ((hw.comp continuous_fst).prodMk H.forward)).neg).div
      (f.lead.continuous_eval.comp (hw.comp continuous_fst)) (fun z => mt (nh z.1 f hfs).mpr hne)
  have ho (z : B×Input d) (i) (hi : i ∈ knots) (j) (hj : j ∈ knots) :
      (i.1 z < j.1 z ↔ i.2 z < j.2 z) ∧ (i.1 z = j.1 z ↔ i.2 z = j.2 z) := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hi
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hj
    obtain ⟨hfs,hnf'⟩ := List.mem_filter.mp hf
    obtain ⟨hgs,hng'⟩ := List.mem_filter.mp hg
    have hnf : MvPolynomial.eval θ f.lead ≠ 0 := by simpa using hnf'
    have hng : MvPolynomial.eval θ g.lead ≠ 0 := by simpa using hng'
    apply (sign_sub_iff ..).mp
    change sign (f.root θ z.2-g.root θ z.2) = sign (f.root _ _ - g.root _ _)
    have hd := hh z.1 (f.resultant g) (by
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨f,hfs,List.mem_map.mpr ⟨g,hgs,rfl⟩⟩) z.2
    rw [f.root_sub g _ _ hnf hng,f.root_sub g _ _ (mt (nh _ f hfs).mpr hnf) (mt (nh _ g hgs).mpr hng),
      sign_quotient,sign_quotient,sign_mul,sign_mul,hd,hl _ f hfs,hl _ g hgs]
  obtain ⟨T,hT,hland,htid⟩ := ordered_transport knots hc ho
  refine ⟨H.lift T hT,?_,?_⟩
  · intro b f hf x
    have ht : f.tail ∈ projected fs := List.mem_append_left _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
    change sign (f.eval θ x) = sign (f.eval (w b) (liftForward H T b x))
    by_cases hz : MvPolynomial.eval θ f.lead = 0
    · simpa only [f.eval_split,hz,(nh b f hf).mp hz,zero_mul,zero_add,liftForward,Fin.tail_cons] using
        hh b f.tail ht (Fin.tail x)
    · have hk : (left f,right f) ∈ knots := List.mem_map.mpr ⟨f,List.mem_filter.mpr ⟨hf,by simpa using hz⟩,rfl⟩
      have hm : T (b,Fin.tail x) (left f (b,Fin.tail x)) = right f (b,Fin.tail x) := hland (b,Fin.tail x) (left f,right f) hk
      rw [f.eval_from_root _ _ hz,f.eval_from_root _ _ (mt (nh _ f hf).mpr hz),sign_mul,sign_mul,hl _ f hf]
      congr 1
      simp only [liftForward,Fin.cons_zero,Fin.tail_cons]
      change sign (x 0 - left f (b,Fin.tail x)) = sign (T _ (x 0) - right f (b,Fin.tail x))
      rw [←hm]
      exact (sign_sub_iff ..).mpr ⟨(T _).lt_iff_lt.symm,(T _).injective.eq_iff.symm⟩
  · intro b hb x
    have hkn : ∀ k ∈ knots, k.1 (b,Fin.tail x) = k.2 (b,Fin.tail x) := by
      intro k hk
      obtain ⟨f,_,rfl⟩ := List.mem_map.mp hk
      simp [left,right,hb,hid b hb]
    change Fin.cons (T (b,Fin.tail x) (x 0)) (H.map b (Fin.tail x)) = x
    rw [htid _ hkn,hid _ hb,Fin.cons_self_tail]

/-- A finite parameter-polynomial discriminant list suffices to keep every
ternary sign throughout the whole input space under ambient homeomorphisms. -/
theorem sweep {B : Type*} [TopologicalSpace B] {p : ℕ} (d : ℕ) (fs : List (Form p d))
    (θ : Params p) (w : B → Params p) (hw : Continuous w)
    (hs : ∀ b q, q ∈ discriminants d fs → sign (MvPolynomial.eval θ q) = sign (MvPolynomial.eval (w b) q)) :
    ∃ H : Family B (Input d), Aligns fs θ w H ∧ ∀ b, w b = θ → ∀ x, H.map b x = x := by
  induction d with
  | zero =>
    refine ⟨Family.identity _ _,?_,fun _ _ _ => rfl⟩
    intro b f hf x
    simpa [Form.eval] using hs b f.bias (List.mem_map.mpr ⟨f,hf,rfl⟩)
  | succ d ih =>
    obtain ⟨H,hh,hid⟩ := ih (projected fs) (fun b q hq => hs b q (List.mem_append_right _ hq))
    exact lift_arrangement fs θ w hw (fun b f hf => hs b f.lead (List.mem_append_left _ (List.mem_map.mpr ⟨f,hf,rfl⟩))) H hh hid

/-- The parameter region is the complement of explicit polynomial zero loci.
Every base parameter in it has a neighborhood of simultaneous triviality. -/
theorem arrangement_stable {p d : ℕ} (fs : List (Form p d)) :
    let U := Good (discriminants d fs)
    IsOpen U ∧ Dense U ∧ (∀ᵐ θ ∂MeasureTheory.volume, θ ∈ U) ∧
      ∀ θ ∈ U, ∃ V : Set (Params p), IsOpen V ∧ θ ∈ V ∧
        ∃ H : Family V (Input d), Aligns fs θ Subtype.val H ∧ ∀ b : V, b.val = θ → ∀ x, H.map b x = x := by
  refine ⟨(good_locus _).1,(good_locus _).2.1,(good_locus _).2.2,?_⟩
  intro θ hθ
  obtain ⟨V,hsub,hopen,hmem⟩ := mem_nhds_iff.mp (signs_near _ hθ)
  refine ⟨V,hopen,hmem,?_⟩
  exact sweep d fs θ Subtype.val continuous_subtype_val (fun b => hsub b.property)

end ReluStability
