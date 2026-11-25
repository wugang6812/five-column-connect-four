import experiments.NarrowBoards
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Five columns: positions of the proof tree

Board model, `HasFour`, `SafeFor`, `CanAvoidLoss` are REUSED from `Connect4.NarrowBoards`
(the same definitions as the published width 1–4 results).  Rows are 0-based here; the notes
(00_STATUS/*.md) use 1-based rows.  Columns are `Fin 5`; column 3 of the notes is index 2.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

abbrev B5 := Board 5

/-- A board from its five column words (bottom first). -/
def ofCols (c1 c2 c3 c4 c5 : List Player) : B5 := ![c1, c2, c3, c4, c5]

@[simp] theorem ofCols_0 (a b c d e : List Player) : ofCols a b c d e 0 = a := rfl
@[simp] theorem ofCols_1 (a b c d e : List Player) : ofCols a b c d e 1 = b := rfl
@[simp] theorem ofCols_2 (a b c d e : List Player) : ofCols a b c d e 2 = c := rfl
@[simp] theorem ofCols_3 (a b c d e : List Player) : ofCols a b c d e 3 = d := rfl
@[simp] theorem ofCols_4 (a b c d e : List Player) : ofCols a b c d e 4 = e := rfl

theorem play_ofCols_0 (a b c d e : List Player) (p : Player) :
    play (ofCols a b c d e) 0 p = ofCols (a ++ [p]) b c d e := by
  funext i; fin_cases i <;> simp [play, ofCols]
theorem play_ofCols_1 (a b c d e : List Player) (p : Player) :
    play (ofCols a b c d e) 1 p = ofCols a (b ++ [p]) c d e := by
  funext i; fin_cases i <;> simp [play, ofCols]
theorem play_ofCols_2 (a b c d e : List Player) (p : Player) :
    play (ofCols a b c d e) 2 p = ofCols a b (c ++ [p]) d e := by
  funext i; fin_cases i <;> simp [play, ofCols]
theorem play_ofCols_3 (a b c d e : List Player) (p : Player) :
    play (ofCols a b c d e) 3 p = ofCols a b c (d ++ [p]) e := by
  funext i; fin_cases i <;> simp [play, ofCols]
theorem play_ofCols_4 (a b c d e : List Player) (p : Player) :
    play (ofCols a b c d e) 4 p = ofCols a b c d (e ++ [p]) := by
  funext i; fin_cases i <;> simp [play, ofCols]

theorem totalStones_ofCols (a b c d e : List Player) :
    totalStones (ofCols a b c d e) = a.length + b.length + c.length + d.length + e.length := by
  simp [totalStones, Fin.sum_univ_five, ofCols]

theorem emptyBoard_eq : emptyBoard 5 = ofCols [] [] [] [] [] := by
  funext i; fin_cases i <;> rfl

/-- `(WB)^n`, bottom first. -/
def wb : Nat → List Player
  | 0 => []
  | n + 1 => .white :: .black :: wb n

@[simp] theorem wb_length (n : Nat) : (wb n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wb, ih]; omega

theorem wb_succ (n : Nat) : wb (n + 1) = wb n ++ [.white, .black] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv_lhs => rw [wb, ih]
    rfl

/-- The centre column after 3,3,3. -/
def centre : List Player := [.black, .white, .black]

/-- T(1,b) = 333(22)^b, White to move. -/
def T (b : Nat) : B5 := ofCols [] (wb b) centre [] []

/-- G(b,H) = T(1,b)·W4·B2, White to move (independent of H as a board). -/
def G (b : Nat) : B5 := ofCols [] (wb b ++ [.black]) centre [.white] []

/-- Top(H), H = 2m: T(1,m-1)·W2·B4, White to move. -/
def Top (m : Nat) : B5 := ofCols [] (wb (m - 1) ++ [.white]) centre [.black] []

/-- Side branch T(1,b)·Wq·B4 (0-based column `q`). -/
def Side (b : Nat) (q : Fin 5) : B5 := play (play (T b) q .white) 3 .black

end C4W5
