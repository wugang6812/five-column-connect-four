import experiments.FourColumns

/-! Frozen interfaces. Coordinates are zero based; column lists run bottom to top.
No strategy assumption is hidden in the definitions below. -/
namespace FiveColumns
open Connect4 Connect4.FourColumns

abbrev Position := Board 5
abbrev Col := Fin 5
def FiveEvenDrawGoal : Prop :=
  ∀ m : Nat, 1 ≤ m → IsDraw (2 * m) (emptyBoard 5)
def WhiteGoal : Prop :=
  ∀ m : Nat, 1 ≤ m → CanAvoidLoss (2 * m) .white (emptyBoard 5)
def BlackGoal : Prop :=
  ∀ m : Nat, 1 ≤ m → CanAvoidLoss (2 * m) .black (emptyBoard 5)

def wb (b : Nat) : List Player := (List.replicate b [.white, .black]).flatten
def GBoard (b : Nat) : Position := fun c =>
  if c = 1 then wb b ++ [.black] else
  if c = 2 then [.black, .white, .black] else
  if c = 3 then [.white] else []
def TBoard (b : Nat) : Position := fun c =>
  if c = 1 then wb b else
  if c = 2 then [.black, .white, .black] else []

def GStarGoal : Prop := ∀ m b : Nat, 4 ≤ m → 3 ≤ b → b ≤ m - 1 →
  CanAvoidLoss (2 * m) .black (GBoard b)
def GInteriorGoal : Prop := ∀ m b : Nat, 4 ≤ m → 3 ≤ b → b ≤ m - 2 →
  CanAvoidLoss (2 * m) .black (GBoard b)
def GTopGoal : Prop := ∀ m : Nat, 4 ≤ m →
  CanAvoidLoss (2 * m) .black (GBoard (m - 1))

def firstBlack : Position := play (emptyBoard 5) 2 .black
def centralThree : Position := play (play firstBlack 2 .white) 2 .black
def SmallGoal : Prop := CanAvoidLoss 2 .black (emptyBoard 5)
def OpeningSideGoal : Prop := ∀ m : Nat, 2 ≤ m → ∀ c : Col, c ≠ 2 →
  CanAvoidLoss (2 * m) .black (play firstBlack c .white)
def CentralSideGoal : Prop := ∀ m : Nat, 2 ≤ m → ∀ c : Col, c ≠ 1 → c ≠ 3 →
  CanAvoidLoss (2 * m) .black (play centralThree c .white)
def TPeripheralGoal : Prop := ∀ m b : Nat, 2 ≤ m → 1 ≤ b → b ≤ m - 1 →
  ∀ c : Col,
    (c = 0 ∨ c = 2 ∨ c = 4 ∨ (c = 3 ∧ b < 3) ∨ (c = 1 ∧ b = m - 1)) →
    CanAvoidLoss (2 * m) .black (play (TBoard b) c .white)
def PeripheralGoals : Prop := SmallGoal ∧ OpeningSideGoal ∧ CentralSideGoal ∧ TPeripheralGoal
def ReductionGoal : Prop := PeripheralGoals → GStarGoal → BlackGoal

def LiveBlack (h : Nat) (P : Position) : Prop :=
  Valid h P ∧ toMove P = .black ∧ ¬ HasFour h P .black ∧
    ¬ HasFour h P .white ∧ ¬ BoardFull h P

/-- A fixed first move, followed by at most d White moves; d=0 is unused. -/
def HorizonMove (h : Nat) (P : Position) (d : Nat) (c : Col) : Prop :=
  Legal h P c ∧ SafeFor h .black (2 * d - 1) (play P c .black)
def J (h : Nat) (P : Position) (c : Col) : Prop := Legal h P c
def I (h : Nat) (P : Position) (c : Col) : Prop := Legal h P c ∧ HasFour h (play P c .black) .black
def T (h : Nat) (P : Position) (c : Col) : Prop := Legal h P c ∧ HasFour h (play P c .white) .white

def HasFourCells (f : Int → Int → Option Player) (p : Player) : Prop :=
  ∃ x y dx dy : Int,
    ((dx = 0 ∧ dy = 1) ∨ (dx = 1 ∧ dy = 0) ∨
     (dx = 1 ∧ dy = 1) ∨ (dx = 1 ∧ dy = -1)) ∧
    ∀ i : Fin 4, f (x + (i : Int) * dx) (y + (i : Int) * dy) = some p

/-- Hypothetical White stone one cell ABOVE the current landing point.
The intervening empty cell remains empty; this is geometry, not a legal move. -/
def upperWhiteCells (h : Nat) (P : Position) (c : Col) : Int → Int → Option Player :=
  fun x y => if x = (c.val : Int) ∧ y = ((P c).length + 1 : Nat) then some .white
    else cellAtInt h P x y
def L (h : Nat) (P : Position) (c : Col) : Prop :=
  (P c).length + 1 < h ∧ HasFourCells (upperWhiteCells h P c) .white

def A1FormulaGoal : Prop := ∀ h P, LiveBlack h P → ∀ c : Col,
  HorizonMove h P 1 c ↔ I h P c ∨
    (J h P c ∧ (∀ d : Col, T h P d → d = c) ∧ ¬ L h P c)
def HorizonMonotoneGoal : Prop := ∀ h P, LiveBlack h P → ∀ d : Nat, 1 ≤ d →
  ∀ c : Col, HorizonMove h P (d + 1) c → HorizonMove h P d c

/-- From a valid Black-to-move position, White can force a win using at most
n additional White moves. Not an evaluator for arbitrary White-to-move boards.
Entry Black win is rejected before considering White win; draws never win. -/
def WhiteWinsIn (h : Nat) : Nat → Position → Prop
  | 0, P => ¬ HasFour h P .black ∧ HasFour h P .white
  | n + 1, P =>
    ¬ HasFour h P .black ∧
    (HasFour h P .white ∨
      (¬ BoardFull h P ∧
       ∀ c : Col, Legal h P c →
         let Q := play P c .black
         ¬ HasFour h Q .black ∧ ¬ BoardFull h Q ∧
           ∃ w : Col, Legal h Q w ∧ WhiteWinsIn h n (play Q w .white)))
def EmptyHorizonLosesGoal : Prop := ∀ h P, LiveBlack h P → ∀ d : Nat, 1 ≤ d →
  (∀ c : Col, ¬ HorizonMove h P d c) → WhiteWinsIn h d P

end FiveColumns
