import FiveColumns.CentralOpening
import C4W5.Even

namespace FiveColumns
open Connect4.NarrowBoards

/-- Opening in column three preserves the game-theoretic draw at every positive even height. -/
theorem draw_after_center {m : Nat} (hm : 1 ≤ m) :
    IsDraw (2*m) CentralOpening.center :=
  C4W5.Compact.draw_after_center_of C4W5.compact_certificates C4W5.compact_center_two hm

/-- From height four on, Black may answer White's first move in exactly that column. -/
theorem nonloss_same_column_reply {m : Nat} (hm : 2 ≤ m) (c : Fin 5) :
    Legal (2*m) (play CentralOpening.center c .white) c ∧
    C4W5.Safe (2*m) (play (play CentralOpening.center c .white) c .black) :=
  C4W5.Compact.same_column_reply_of C4W5.compact_certificates hm c

#print axioms draw_after_center
#print axioms nonloss_same_column_reply
end FiveColumns
