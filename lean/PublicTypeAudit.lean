import FiveColumns.ClosedByStretch
import FiveColumns.OptimalOpening

open Connect4.NarrowBoards

example : ∀ {h : Nat}, 2 ≤ h → h % 2 = 0 → IsDraw h (emptyBoard 5) :=
  @C4W5.five_columns_even_draw

example : FiveColumns.FiveEvenDrawGoal := FiveColumns.five_even_draw_by_stretch

example : ∀ {m : Nat}, 1 ≤ m → IsDraw (2*m) (play (emptyBoard 5) 2 .black) :=
  @FiveColumns.draw_after_center

example : ∀ {m : Nat}, 2 ≤ m → ∀ c : Fin 5,
    Legal (2*m) (play (play (emptyBoard 5) 2 .black) c .white) c ∧
    C4W5.Safe (2*m) (play (play (play (emptyBoard 5) 2 .black) c .white) c .black) :=
  @FiveColumns.nonloss_same_column_reply

#print axioms C4W5.five_columns_even_draw
#print axioms FiveColumns.five_even_draw_by_stretch
#print axioms FiveColumns.draw_after_center
#print axioms FiveColumns.nonloss_same_column_reply
