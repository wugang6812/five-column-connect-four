import C4W5.FiveColumnsUnified

open Connect4.NarrowBoards

example : ∀ {h : Nat}, 2 ≤ h → h % 2 = 0 → IsDraw h (emptyBoard 5) :=
  @C4W5.five_columns_even_draw

example : ∀ h : Nat, IsDraw h (emptyBoard 5) :=
  C4W5.five_columns_draw

example : ∀ h : Nat,
    (¬ ∃ k, WinFor h Connect4.Player.black k (emptyBoard 5)) ∧
    (¬ ∃ k, WinFor h Connect4.Player.white k (emptyBoard 5)) :=
  C4W5.five_columns_neither_player_wins

#print axioms C4W5.five_columns_even_draw
#print axioms C4W5.five_columns_draw
#print axioms C4W5.five_columns_neither_player_wins
