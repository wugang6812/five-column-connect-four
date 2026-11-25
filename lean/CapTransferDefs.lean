import LongThreat
import LongThreatStretch
import C4W5.Theory.ZoneL

/-!
Source-only formalization draft. No proof kernel run has been made on this module.
The board-level model is SG5 proper (no hidden Zone top or truncation).
-/
namespace C4W5.CapTransfer
open Connect4 (Player opponent)
open Connect4.NarrowBoards

def protect (t : Fin 5) (Q : Fin 5 → Prop) (q : Fin 5) : Prop := q = t ∨ Q q

/-- The phase-II guard uses its original coordinate system until the cap. -/
def PostGuard (t s : Fin 5) (a b : Nat) (Q : Fin 5 → Prop)
    (h0 : Fin 5 → Nat) (x y : Int) : Prop :=
  (∃ q, protect t Q q ∧ Claimed q (h0 q) x y) ∨
    (x = (s.val : Int) ∧ ((b : Int) ≤ y ∨
      ((a : Int) ≤ y ∧ y % 2 = (h0 s : Int) % 2)))

def PostDead (H : Nat) (R : Board 5) (t s : Fin 5) (a b : Nat)
    (Q : Fin 5 → Prop) (h0 : Fin 5 → Nat) (c : Fin 5) (r : Nat) : Prop :=
  ∀ dy ∈ ([0, 1, -1] : List Int), ∀ i : Fin 4,
    ∃ j : Fin 4,
    let x := (c.val : Int) - (i : Int) * 1 + (j : Int) * 1
    let y := (r : Int) - (i : Int) * dy + (j : Int) * dy
    cellAtInt H R x y = some .black ∨ PostGuard t s a b Q h0 x y ∨
      ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int))

structure Hyp (H : Nat) (R : Board 5) (t s : Fin 5) (a b : Nat) (Q : Fin 5 → Prop) : Prop where
  even : H % 2 = 0
  valid : Valid H R
  distinct : s ≠ t
  noT : ¬ Q t
  noS : ¬ Q s
  oddT : (R t).length % 2 = 1
  evenS : (R s).length % 2 = 0
  evenQ : ∀ q, Q q → (R q).length % 2 = 0
  above : (R s).length < a
  order : a < b
  below : b < H
  oddA : (a - (R s).length) % 2 = 1
  evenB : b % 2 = (R s).length % 2
  noTriple : ∀ c, Legal H R c → ¬ TopThree R c
  threatA : LongThreat.Threat H R s a
  threatB : LongThreat.Threat H R s b
  deadA : ∀ c r, Exceptional R c r ∨ PotExc H R c r →
    LongThreat.Dead H R s a (protect t Q) (fun q => (R q).length) c r
  deadB : ∀ c r, Exceptional R c r ∨ PotExc H R c r →
    PostDead H R t s a b Q (fun q => (R q).length) c r

/-- There is no second phase controller. The invariant retains the exact first
    phase from LongThreat, waiting for a cap in the extra protected odd column. -/
structure BeforeCap (H : Nat) (R : Board 5) (t s : Fin 5) (a b : Nat)
    (Q : Fin 5 → Prop) (h0 : Fin 5 → Nat) : Prop where
  inv : LongThreat.Inv H s a (protect t Q) h0 R
  threatB : LongThreat.Threat H R s b
  deadB : ∀ c r, Exceptional R c r ∨ PotExc H R c r →
    PostDead H R t s a b Q h0 c r

def L (H : Nat) (R : Board 5) : Prop := ∃ t s a b Q, Hyp H R t s a b Q

end C4W5.CapTransfer
