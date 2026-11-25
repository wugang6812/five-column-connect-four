import C4W5.Compact.Contracts
import C4W5.Cert.Gen.Z8_322.Main
import C4W5.Cert.Gen.Z8_s113.Main
import C4W5.Cert.Gen.Z8_s123.Main
import C4W5.Cert.Gen.Z8_side11.Main
import C4W5.Cert.Gen.Z8_side15.Main
import C4W5.Cert.Gen.Z8_side21.Main
import C4W5.Cert.Gen.Z8_side25.Main
import C4W5.Cert.Gen.Z8_G1.Main

namespace C4W5.Compact
open Connect4 (Player opponent)
open Connect4.NarrowBoards

structure SmallZonesAt (H : Nat) : Prop where
  c322 : Safe H P322
  s113 : Safe H (play (play (T 1) 2 .white) 1 .black)
  s123 : Safe H (play (play (T 2) 2 .white) 4 .black)
  side12 : ∀ (b : Nat) (q : Fin 5), (b = 1 ∨ b = 2) → (q = 0 ∨ q = 4) → Safe H (Side b q)
  g1 : Safe H (G 1)

theorem small_zones_at (H : Nat) (he : H % 2 = 0) (h10 : 10 ≤ H) : SmallZonesAt H where
  c322 := by
    have e : playList (emptyBoard 5) .black [2, 1, 1] = P322 := by
      simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, P322, opponent]
    exact e ▸ Z8_322.safe H he (by omega)
  s113 := by
    have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 2, 1] =
        play (play (T 1) 2 .white) 1 .black := by
      simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, T, centre, wb, opponent]
    exact e ▸ Z8_s113.safe H he (by omega)
  s123 := by
    have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 2, 4] =
        play (play (T 2) 2 .white) 4 .black := by
      simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_4, T, centre, wb, opponent]
    exact e ▸ Z8_s123.safe H he (by omega)
  side12 := by
    intro b q hb hq
    rcases hb with rfl | rfl <;> rcases hq with rfl | rfl
    · have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 0, 3] = Side 1 0 := by
        simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2,
          play_ofCols_3, Side, T, centre, wb, opponent]
      exact e ▸ Z8_side11.safe H he (by omega)
    · have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 4, 3] = Side 1 4 := by
        simp [playList, emptyBoard_eq, play_ofCols_4, play_ofCols_1, play_ofCols_2,
          play_ofCols_3, Side, T, centre, wb, opponent]
      exact e ▸ Z8_side15.safe H he (by omega)
    · have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 0, 3] = Side 2 0 := by
        simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2,
          play_ofCols_3, Side, T, centre, wb, opponent]
      exact e ▸ Z8_side21.safe H he (by omega)
    · have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 4, 3] = Side 2 4 := by
        simp [playList, emptyBoard_eq, play_ofCols_4, play_ofCols_1, play_ofCols_2,
          play_ofCols_3, Side, T, centre, wb, opponent]
      exact e ▸ Z8_side25.safe H he (by omega)
  g1 := by
    have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 3, 1] = G 1 := by
      simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
    exact e ▸ Z8_G1.safe H he (by omega)

#print axioms small_zones_at
end C4W5.Compact
