import C4W5.Compact.Contracts
import C4W5.Cert.Gen.Z8_33311.Main

namespace C4W5.Compact
open Connect4 (Player opponent)
open Connect4.NarrowBoards

theorem z33311_at (H : Nat) (he : H % 2 = 0) (h10 : 10 ≤ H) :
    Safe H (play (play (T 0) 0 .white) 0 .black) := by
  have e : playList (emptyBoard 5) .black [2, 2, 2, 0, 0] =
      play (play (T 0) 0 .white) 0 .black := by
    simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_2, T, centre, wb, opponent]
  exact e ▸ Z8_33311.safe H he (by omega)

#print axioms z33311_at
end C4W5.Compact
