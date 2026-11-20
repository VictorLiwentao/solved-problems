module

@[expose] public section

namespace BusyBeaver

/-- The largest recorded runtime, with zero for an empty table. -/
def record (runtime : α → Nat) (table : List α) : Nat :=
  table.foldr (fun machine best => max (runtime machine) best) 0

end BusyBeaver
