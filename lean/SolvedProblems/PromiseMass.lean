module

public import SolvedProblems.MassModel

public section

namespace PromiseMass

private theorem addUnit (n d : Nat) :
    Adds (List.replicate n true ++ false :: List.replicate d false)
         (List.replicate n false ++ true :: List.replicate d false)
         (List.replicate n true ++ true :: List.replicate d false) := by
  have zeros (r) : Adds (List.replicate r false) (List.replicate r false)
      (List.replicate r false) := by
    induction r with
    | zero => exact .nil
    | succ _ ih => exact .cons rfl ih
  induction n with
  | zero => exact .cons rfl (zeros d)
  | succ _ ih => exact .cons rfl ih

private theorem cyclic_divides {f k m} (hp : poly k m f) (hc : cyclic k f) : k ∣ m := by
  let a := f (true :: List.replicate (k-1) false)
  have mass (n d : Nat) (size : n+d=k) :
      f (List.replicate n true ++ List.replicate d false) = n*a := by
    induction n generalizing d with
    | zero => simpa [← size] using hp.1
    | succ n ih =>
      have unit := hc (List.replicate n false) (true :: List.replicate d false) (by simp; omega)
      have count : d+n=k-1 := by omega
      simp [count] at unit
      have h := hp.2.2.2 _ _ _ (by simp; omega) (addUnit n d)
      rw [unit] at h
      have prev := ih (d+1) (by omega)
      rw [List.replicate_succ] at prev
      rw [prev] at h
      rw [List.replicate_succ']
      simpa [List.append_assoc, Nat.succ_mul,a] using h.symm
  exact ⟨a,by simpa [hp.2.1] using mass k 0 (by omega)⟩

private theorem countAdds {xs ys zs} (h : Adds xs ys zs) :
    xs.count true + ys.count true = zs.count true := by
  induction h with
  | nil => rfl
  | @cons a b c xs ys zs h _ ih =>
    cases a <;> cases b <;> cases c <;> simp_all <;> omega

/-- The full cyclic spectrum of the endpoint-preserving addition template.
At each permitted arity, a fully symmetric operation realizes it. -/
theorem cyclicSpectrum (k m : Nat) :
    ((∃ f, poly k m f ∧ cyclic k f) ↔ k ∣ m) ∧
    ((∃ f, poly k m f ∧ symmetric k f) ↔ k ∣ m) := by
  have realize (dvd : k ∣ m) : ∃ f, poly k m f ∧ symmetric k f := by
    obtain ⟨a,rfl⟩ := dvd
    let f (xs : List Bool) := xs.count true * a
    refine ⟨f,⟨by simp [f,List.count_eq_zero_of_not_mem],by simp [f],?_,?_⟩,?_⟩
    · intro xs len
      exact Nat.mul_le_mul_right a (len ▸ List.count_le_length (a := true) (l := xs))
    · intro xs ys zs _ h
      simp only [f, ← Nat.add_mul, countAdds h]
    · intro xs ys _ perm
      exact congrArg (· * a) (perm.count_eq true)
  have toCyc {f} (sym : symmetric k f) : cyclic k f :=
    fun u v len => sym _ _ (by simpa using len) List.perm_append_comm
  exact ⟨⟨fun ⟨_,hp,hc⟩ => cyclic_divides hp hc,fun h =>
    let ⟨f,hp,hs⟩ := realize h; ⟨f,hp,toCyc hs⟩⟩,
    ⟨fun ⟨_,hp,hs⟩ => cyclic_divides hp (toCyc hs),realize⟩⟩

end PromiseMass
