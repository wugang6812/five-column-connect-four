import C4W5.Even
import C4W5.Odd.Main

/-!
# Complete Finite-Height Five-Column Connect Four Theorem (`FiveColumnsUnified`)

Instantiates `C4W5Gen.five_columns_draw_of_even` with `C4W5.five_columns_even_draw`
to establish `five_columns_draw : ∀ h : Nat, IsDraw h (emptyBoard 5)` for ALL natural heights `h ≥ 0`.
-/

namespace C4W5
open Connect4.NarrowBoards

/-- **Unified Finite-Height Theorem**:
    On five columns and EVERY height `h : Nat` (`h = 0, 1, 2, 3, ...`),
    Gravity Connect Four `5 × h` is a game-theoretic draw from the empty board. -/
theorem five_columns_draw (h : Nat) : IsDraw h (emptyBoard 5) :=
  C4W5Gen.five_columns_draw_of_even five_columns_even_draw h

/-- Neither player can force a win at any finite horizon on `5 × h` for any `h : Nat`. -/
theorem five_columns_neither_player_wins (h : Nat) :
    (¬ ∃ k, WinFor h Connect4.Player.black k (emptyBoard 5)) ∧
    (¬ ∃ k, WinFor h Connect4.Player.white k (emptyBoard 5)) :=
  draw_excludes_forced_wins (five_columns_draw h)

#print axioms five_columns_draw
#print axioms five_columns_neither_player_wins

end C4W5
