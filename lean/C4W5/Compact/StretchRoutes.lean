import C4W5.Compact.Contracts

namespace C4W5.Compact
open Connect4.NarrowBoards

/-- Adapt the four exact generated unbounded endpoints to the independent contracts layer.
    In particular the Top proof is stronger than the threshold needed here. -/
theorem stretch_families_of
    (stop : ∀ m : Nat, 5 ≤ m → Safe (2*m) (Top m))
    (g3 : ∀ m : Nat, 7 ≤ m → Safe (2*m) (G 3))
    (tight : ∀ b : Nat, 5 ≤ b → Safe (2*b+2) (G b))
    (mid : ∀ b : Nat, 5 ≤ b → Safe (2*b+4) (G b))
    (wide : ∀ m b : Nat, 5 ≤ b → b+3 ≤ m → Safe (2*m) (G b)) :
    StretchFamilies where
  top := fun m hm => stop m (by omega)
  g3 := g3
  g5_tight := fun b hb => by
    rw [show 2 * (b + 1) = 2*b+2 by omega]
    exact tight b hb
  g5_mid := fun b hb => by
    rw [show 2 * (b + 2) = 2*b+4 by omega]
    exact mid b hb
  g5_wide := wide

#print axioms stretch_families_of
end C4W5.Compact
