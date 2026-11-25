import C4W5.Compact.ZoneSmall
import C4W5.Compact.Zone33311
import C4W5.Cert.Gen.Z10_311.Main
import C4W5.Cert.Gen.Z10_G2.Main
import C4W5.Cert.Gen.Z10_U.Main
import C4W5.Cert.Gen.Z12_G4.Main

/-! Full parametric fixed-Zone supplier. Source draft until each imported
    compact table and the coherent integrated build have actually passed. -/
namespace C4W5.Compact
open Connect4 (Player opponent)
open Connect4.NarrowBoards

theorem zones : Zones where
  c311 := fun m hm => by
    have e : playList (emptyBoard 5) .black [2, 0, 0] = P311 := by
      simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_2, P311, opponent]
    exact e ▸ Z10_311.safe (2*m) (by omega) (by omega)
  c322 := fun m hm => (small_zones_at (2*m) (by omega) (by omega)).c322
  c33311 := fun m hm => z33311_at (2*m) (by omega) (by omega)
  s113 := fun m hm => (small_zones_at (2*m) (by omega) (by omega)).s113
  s123 := fun m hm => (small_zones_at (2*m) (by omega) (by omega)).s123
  side12 := fun m b q hm hb hq => (small_zones_at (2*m) (by omega) (by omega)).side12 b q hb hq
  g1 := fun m hm => (small_zones_at (2*m) (by omega) (by omega)).g1
  g2 := fun m hm => by
    have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 3, 1] = G 2 := by
      simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
    exact e ▸ Z10_G2.safe (2*m) (by omega) (by omega)
  g4 := fun m hm => by
    have e : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] = G 4 := by
      simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
    exact e ▸ Z12_G4.safe (2*m) (by omega) (by omega)
  u := fun m hm => by
    have e : playList (emptyBoard 5) .black [2, 2, 2, 2, 1] =
        play (play (T 0) 2 .white) 1 .black := by
      simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, T, centre, wb, opponent]
    exact e ▸ Z10_U.safe (2*m) (by omega) (by omega)

#print axioms zones
end C4W5.Compact
