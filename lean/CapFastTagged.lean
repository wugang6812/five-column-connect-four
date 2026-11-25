import CapDoubleMasks
import CapTaggedGate

namespace C4W5.CapFastTagged
open Connect4.NarrowBoards C4W5.WindowBank
open C4W5.CapTagged (L base maxCode capMask)

def applyCapRaw (H : Nat) (p : Pos) (code : Nat) : Bool :=
  force (code / 5) fun w1 =>
  force (w1 / 5) fun w2 =>
  force (w2 / 32) fun w3 =>
  force (w3 / 32) fun w4 =>
  force (w4 / 3) fun w5 =>
  force (w5 / 3) fun w6 =>
  let t : Fin 5 := ⟨code%5,Nat.mod_lt _ (by decide)⟩
  let s : Fin 5 := ⟨w1%5,Nat.mod_lt _ (by decide)⟩
  CapFast.checkPost H p t s (2*(w2%32)+1) (2*(w3%32)) (capMask H p t s)
    ⟨w4%3,Nat.mod_lt _ (by decide)⟩ ⟨w5%3,Nat.mod_lt _ (by decide)⟩
    ⟨w6%4,Nat.mod_lt _ (by decide)⟩ ⟨(w6/4)%4,Nat.mod_lt _ (by decide)⟩

theorem applyCapRaw_sound {H : Nat} {p : Pos} {code : Nat}
    (h : applyCapRaw H p code = true) : CapTransfer.L H p.toBoard := by
  simp only [applyCapRaw,force_eq] at h
  exact CapFast.checkPost_leaf h

def applyTagged (H : Nat) (p : Pos) (code : Nat) : Bool :=
  if code < base then applyWitness LongThreat.checkBits H p code
  else if code < maxCode then applyCapRaw H p (code - base)
  else false

theorem applyTagged_sound {H : Nat} {p : Pos} {code : Nat}
    (h : applyTagged H p code = true) : L H p.toBoard := by
  unfold applyTagged at h
  split at h
  · left
    simp only [applyWitness,force_eq] at h
    exact LongThreat.check_leaf (LongThreat.checkBits_reference h)
  · split at h
    · exact Or.inr (applyCapRaw_sound h)
    · cases h

def gate (F : SFormat) (hints : Bank) (H : Nat) (p : Pos) : Bool :=
  force (F.key H p) fun key =>
  match find F.radix F.repBase key hints with
  | none => false
  | some w => applyTagged H p (w % F.repBase)

theorem gate_sound (F : SFormat) (hints : Bank) (H : Nat) (p : Pos)
    (ok : gate F hints H p = true) : L H p.toBoard := by
  simp only [gate, force_eq] at ok
  split at ok
  · cases ok
  · exact applyTagged_sound ok

#print axioms gate_sound
end C4W5.CapFastTagged
