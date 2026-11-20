module

public import SolvedProblems.AtomSplitFinite

@[expose] public section

namespace AtomSplit
open Set Equiv

variable {k : ℕ} {block : ℕ → Fin k} {X : Type u} (act : stabilizer block →* Perm X)

def orbit (U : Set ℕ) (x : X) : Set X := {y | ∃ q : stabilizer block, q.val ∈ Inside U ∧ act q x = y}

theorem mem_orbit_self (U : Set ℕ) (x : X) : x ∈ orbit act U x := ⟨1,(Inside U).one_mem,by simp⟩

theorem orbit_stable {U : Set ℕ} (x : X) (hU : Inside U ≤ stabilizer block) (g : Inside U) (y : X) :
    localAction act hU g y ∈ orbit act U x ↔ y ∈ orbit act U x := by
  let k := Subgroup.inclusion hU g
  have hk : k.val ∈ Inside U := g.property
  constructor
  · rintro ⟨q,hq,eq⟩
    refine ⟨k⁻¹*q,(Inside U).mul_mem ((Inside U).inv_mem hk) hq,?_⟩
    change act q x = act k y at eq
    rw [map_mul,map_inv,Perm.mul_apply,eq]
    exact (act k).symm_apply_apply y
  · rintro ⟨q,hq,rfl⟩
    exact ⟨k*q,(Inside U).mul_mem hk hq,by rw [map_mul]; rfl⟩

private theorem orbit_conj {U : Set ℕ} {x : X} {g : stabilizer block}
    (keep : ∀ a, g.val a ∈ U ↔ a ∈ U) (fix : act g x = x) :
    ∀ y ∈ orbit act U x, act g y ∈ orbit act U x := by
  rintro _ ⟨q,hq,rfl⟩
  have conf : (g*q*g⁻¹).val ∈ Inside U := by
    intro a ha
    have hn : g.val.symm a ∉ U := fun e => ha (by simpa using (keep (g.val.symm a)).mpr e)
    change g.val (q.val (g.val.symm a)) = a
    rw [hq _ hn,Equiv.apply_symm_apply]
  refine ⟨g*q*g⁻¹,conf,?_⟩
  have back : (act g).symm x = x := (Equiv.symm_apply_eq _).mpr fix.symm
  simp only [map_mul, map_inv,Perm.mul_apply]
  change act g (act q ((act g).symm x)) = _
  rw [back]

theorem orbit_supported (hs : LocallySupported act) (U : Set ℕ) (x : X) : Supported act (orbit act U x) := by
  obtain ⟨Q,hQ⟩ := hs x
  refine ⟨U::Q,fun g hp y => ?_⟩
  have fix : act g x = x := hQ g (fun D h => hp D (List.mem_cons_of_mem _ h))
  have keep : ∀ a, g.val a ∈ U ↔ a ∈ U := hp U (by simp)
  constructor
  · intro e
    have inv : act g⁻¹ x = x := by
      rw [map_inv]; exact (Equiv.symm_apply_eq _).mpr fix.symm
    have back : ∀ a, g⁻¹.val a ∈ U ↔ a ∈ U := fun a => by
      change g.val.symm a ∈ U ↔ _; simpa using (keep (g.val.symm a)).symm
    simpa using orbit_conj act back inv _ e
  · exact orbit_conj act keep fix _

theorem inside_commute {U D : Set ℕ} (dis : Disjoint U D) {g p : Perm ℕ}
    (hg : g ∈ Inside D) (hp : p ∈ Inside U) : g*p=p*g := by
  apply Equiv.ext; intro a; simp only [Perm.mul_apply]
  by_cases hu : a ∈ U
  · have ha := (inside_preserves hp a).mpr hu
    rw [hg _ (Set.disjoint_left.mp dis ha),hg _ (Set.disjoint_left.mp dis hu)]
  · rw [hp _ hu]
    by_cases hd : a ∈ D
    · rw [hp _ (Set.disjoint_right.mp dis ((inside_preserves hg a).mpr hd))]
    · rw [hg _ hd,hp _ hu]

theorem orbit_fixed_disjoint {U D : Set ℕ} (dis : Disjoint U D) {g : stabilizer block}
    (hg : g.val ∈ Inside D) {x : X} (fix : act g x = x) :
    ∀ y ∈ orbit act U x, act g y = y := by
  rintro _ ⟨q,hq,rfl⟩
  have eq : g*q=q*g := Subtype.ext (inside_commute dis hg hq)
  calc act g (act q x) = act (g*q) x := by rw [map_mul]; rfl
       _ = act q x := by rw [eq,map_mul,Perm.mul_apply,fix]

end AtomSplit
