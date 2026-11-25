import FiveColumns.Specification
import experiments.NarrowBoards

namespace FiveColumns
open Connect4

private theorem stones_agree (pieces : List Player) (n : Nat) :
    FourColumns.stone pieces n = NarrowBoards.stone pieces n := by
  induction pieces generalizing n with
  | nil => cases n <;> rfl
  | cons a rest ih => cases n with
    | zero => rfl
    | succ n => exact ih n

private theorem cells_agree {w : Nat} (h : Nat) (P : NarrowBoards.Board w) (x y : Int) :
    FourColumns.cellAtInt h P x y = NarrowBoards.cellAtInt h P x y := by
  simp only [FourColumns.cellAtInt, NarrowBoards.cellAtInt, stones_agree]

private theorem four_iff {w : Nat} (h : Nat) (P : NarrowBoards.Board w) (p : Player) :
    FourColumns.HasFour h P p ↔ NarrowBoards.HasFour h P p := by
  simp only [FourColumns.HasFour, NarrowBoards.HasFour,
    FourColumns.HasFourDir, NarrowBoards.HasFourDir, cells_agree]

private theorem safe_iff {w : Nat} (h : Nat) (p : Player) (k : Nat) (P : NarrowBoards.Board w) :
    FourColumns.SafeFor h p k P ↔ NarrowBoards.SafeFor h p k P := by
  induction k generalizing P with
  | zero => simp only [FourColumns.SafeFor, NarrowBoards.SafeFor, four_iff]
  | succ k ih =>
    rw [FourColumns.SafeFor, NarrowBoards.SafeFor]
    have moveEq : FourColumns.toMove P = NarrowBoards.toMove P := rfl
    by_cases turn : NarrowBoards.toMove P = p <;>
      simp [four_iff, FourColumns.BoardFull, NarrowBoards.BoardFull, moveEq, turn,
        FourColumns.Legal, NarrowBoards.Legal, FourColumns.play, NarrowBoards.play, ih]

/-- Both libraries use the same rules for every width, height, and position. -/
theorem draw_iff_narrowBoards {w h : Nat} (P : Connect4.NarrowBoards.Board w) :
    Connect4.FourColumns.IsDraw h P ↔ Connect4.NarrowBoards.IsDraw h P := by
  simp only [FourColumns.IsDraw, NarrowBoards.IsDraw,
    FourColumns.CanAvoidLoss, NarrowBoards.CanAvoidLoss, safe_iff]

/-- Export the stretching theorem at the type used by the original five-column project. -/
theorem frozen_goal_of_even_draw
    (draw : ∀ {h : Nat}, 2 ≤ h → h % 2 = 0 →
      Connect4.NarrowBoards.IsDraw h (Connect4.NarrowBoards.emptyBoard 5)) :
    FiveEvenDrawGoal := by
  intro m hm
  apply (draw_iff_narrowBoards _).mpr
  exact draw (by omega) (by omega)

#print axioms frozen_goal_of_even_draw
end FiveColumns
