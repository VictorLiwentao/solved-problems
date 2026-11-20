module

public import SolvedProblems.RuntimeTable

public section

namespace BusyBeaver

/-- At a fixed state bound, splitting a finite table by colour preserves its record. -/
theorem record_split (table : List α) (runtime : α → Nat) (red : α → Bool) :
    max (record runtime (table.filter red))
        (record runtime (table.filter (fun m => !(red m)))) = record runtime table := by
  induction table with
  | nil => rfl
  | cons m ms ih =>
    cases h : red m <;>
      simp [h, record, List.foldr_cons] at * <;> omega

end BusyBeaver
