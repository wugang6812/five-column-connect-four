import C4W5.Theory.ClaimStretch

namespace C4W5.LongThreat
open Connect4 (Player opponent)
open Connect4.NarrowBoards

def Threat (H : Nat) (R : Board 5) (t : Fin 5) (rho : Nat) : Prop :=
  ∃ (x y dy : Int) (i : Fin 4), dy ∈ ([0, 1, -1] : List Int) ∧
    x + (i : Int) * 1 = (t.val : Int) ∧ y + (i : Int) * dy = (rho : Int) ∧
    ∀ j : Fin 4, j ≠ i → cellAtInt H R (x + (j : Int) * 1) (y + (j : Int) * dy) = some .black

def Guard (t : Fin 5) (rho : Nat) (Q : Fin 5 → Prop) (h0 : Fin 5 → Nat) (x y : Int) : Prop :=
  (∃ q, (q = t ∨ Q q) ∧ Claimed q (h0 q) x y) ∨ (x = (t.val : Int) ∧ (rho : Int) ≤ y)

def Dead (H : Nat) (R : Board 5) (t : Fin 5) (rho : Nat)
    (Q : Fin 5 → Prop) (h0 : Fin 5 → Nat) (c : Fin 5) (r : Nat) : Prop :=
  ∀ dy ∈ ([0, 1, -1] : List Int), ∀ i : Fin 4,
    ∃ j : Fin 4,
    let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
    let y := (r : Int) - (i : Int) * dy + (j : Int) * dy
    cellAtInt H R x y = some .black ∨ Guard t rho Q h0 x y ∨
      ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int))

structure Hyp (H : Nat) (R : Board 5) (t : Fin 5) (rho : Nat) (Q : Fin 5 → Prop) : Prop where
  even : H % 2 = 0
  valid : Valid H R
  not_mem : ¬ Q t
  odd : (H - (R t).length) % 2 = 1
  qpar : ∀ q, Q q → (H - (R q).length) % 2 = 0
  target_gt : (R t).length < rho
  target_lt : rho < H
  target_odd : (rho - (R t).length) % 2 = 1
  ntr : ∀ c, Legal H R c → ¬ TopThree R c
  threat : Threat H R t rho
  dead : ∀ c r, Exceptional R c r ∨ PotExc H R c r → Dead H R t rho Q (fun q => (R q).length) c r

end C4W5.LongThreat
