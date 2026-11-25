import WindowStretchExtra
import LongThreatLeaf

/-! Witness index is merely a hint. The returned witness is checked on the
requested H/Pos, never on the board represented by the hint's lookup key. -/
namespace C4W5.WindowBank
open Connect4.NarrowBoards

abbrev WitnessCheck := Nat → Pos → Fin 5 → Nat → Nat → Fin 3 → Fin 4 → Bool

def applyWitness (test : WitnessCheck) (H : Nat) (p : Pos) (word : Nat) : Bool :=
  force word fun w =>
  force (w / 5) fun w1 =>
  force (w1 / 61) fun w2 =>
  force (w2 / 32) fun w3 =>
  test H p ⟨w % 5, Nat.mod_lt _ (by decide)⟩ (w1 % 61) (w2 % 32)
    ⟨w3 % 3, Nat.mod_lt _ (by decide)⟩ ⟨(w3 / 3) % 4, Nat.mod_lt _ (by decide)⟩

def witnessGate (test : WitnessCheck) (F : SFormat) (hints : Bank) (H : Nat) (p : Pos) : Bool :=
  force (F.key H p) fun key =>
  match find F.radix F.repBase key hints with
  | none => false
  | some w => applyWitness test H p (w % F.repBase)

theorem witnessGate_sound (test : WitnessCheck)
    (sound : ∀ H p t rho mask d i, test H p t rho mask d i = true → LongThreat.L H p.toBoard)
    (F : SFormat) (hints : Bank) (H : Nat) (p : Pos)
    (ok : witnessGate test F hints H p = true) : LongThreat.L H p.toBoard := by
  simp only [witnessGate, force_eq] at ok
  split at ok
  · cases ok
  · simp only [applyWitness, force_eq] at ok
    exact sound _ _ _ _ _ _ _ ok

def referenceGate : SFormat → Bank → Nat → Pos → Bool := witnessGate LongThreat.check

theorem referenceGate_sound (F : SFormat) (hints : Bank) (H : Nat) (p : Pos)
    (h : referenceGate F hints H p = true) : LongThreat.L H p.toBoard :=
  witnessGate_sound LongThreat.check (fun _ _ _ _ _ _ _ h => LongThreat.check_leaf h) F hints H p h

#print axioms witnessGate_sound
#print axioms referenceGate_sound
end C4W5.WindowBank
