import C4W5.Compact.Contracts

/-! Turn generated exact-playlist theorems into normalized board obligations. -/
namespace C4W5.Compact
open Connect4 (Player opponent)
open Connect4.NarrowBoards

structure FinitePlays : Prop where
  c311_10 : Safe 10 (playList (emptyBoard 5) .black [2, 0, 0])
  g2_10 : Safe 10 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 3, 1])
  g3_10 : Safe 10 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1])
  g4_10 : Safe 10 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1])
  top_10 : Safe 10 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3])
  u_10 : Safe 10 (playList (emptyBoard 5) .black [2, 2, 2, 2, 1])
  g3_12 : Safe 12 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1])
  g4_12 : Safe 12 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1])
  g5_12 : Safe 12 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1])
  top_12 : Safe 12 (playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3])

private theorem play311_eq : playList (emptyBoard 5) .black [2, 0, 0] = P311 := by
  simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_2, P311, opponent]
private theorem g2_eq : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 3, 1] = G 2 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
private theorem g3_eq : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1] = G 3 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
private theorem g4_eq : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] = G 4 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
private theorem g5_eq : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] = G 5 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
private theorem top5_eq : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3] = Top 5 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, Top, centre, wb, opponent]
private theorem top6_eq : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3] = Top 6 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, Top, centre, wb, opponent]
private theorem u_eq : playList (emptyBoard 5) .black [2, 2, 2, 2, 1] =
    play (play (T 0) 2 .white) 1 .black := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, T, centre, wb, opponent]

theorem finite_gaps_of_plays (P : FinitePlays) : FiniteGaps where
  c311_10 := play311_eq ▸ P.c311_10
  g2_10 := g2_eq ▸ P.g2_10
  g3_10 := g3_eq ▸ P.g3_10
  g4_10 := g4_eq ▸ P.g4_10
  top_10 := top5_eq ▸ P.top_10
  u_10 := u_eq ▸ P.u_10
  g3_12 := g3_eq ▸ P.g3_12
  g4_12 := g4_eq ▸ P.g4_12
  g5_12 := g5_eq ▸ P.g5_12
  top_12 := top6_eq ▸ P.top_12

#print axioms finite_gaps_of_plays
end C4W5.Compact
