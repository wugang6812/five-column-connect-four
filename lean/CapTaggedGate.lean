import CapTransferCheck
import WindowLongGateFast

/-! Isolated optional leaf gateway, same 5^10 payload width. -/
namespace C4W5.CapTagged
open Connect4.NarrowBoards C4W5.WindowBank

def L (h : Nat) (A : Board 5) : Prop := LongThreat.L h A ∨ CapTransfer.L h A

theorem leafSound {D : Nat} (hD : 2 ≤ D) : LeafSound D L := by
  intro h A H R hi hs ht hw hb
  rcases hi with ho | hc
  · exact LongThreat.leafSound hD h A H R ho hs ht hw hb
  · exact CapTransfer.leafSound hD h A H R hc hs ht hw hb

def base : Nat := 117120
def maxCode : Nat := 3803520

/-- All other positive even vacancy columns add guards, without changing
    the parity component of the CapTransfer witness. -/
def capMask (H : Nat) (p : Pos) (t s : Fin 5) : Nat :=
  let col (c : Nat) := if c = t.val ∨ c = s.val ∨ H ≤ p.ht c ∨ (p.ht c) % 2 ≠ 0
    then 0 else 2^c
  col 0 + col 1 + col 2 + col 3 + col 4

def encode (t s : Fin 5) (a0 b0 : Fin 32) (da db : Fin 3) (ia ib : Fin 4) : Nat :=
  base + t.val + 5 * (s.val + 5 * (a0.val + 32 * (b0.val + 32 *
    (da.val + 3 * (db.val + 3 * (ia.val + 4 * ib.val))))))

theorem encode_range (t s : Fin 5) (a0 b0 : Fin 32) (da db : Fin 3) (ia ib : Fin 4) :
    base ≤ encode t s a0 b0 da db ia ib ∧ encode t s a0 b0 da db ia ib < maxCode := by
  have ht := t.isLt; have hs := s.isLt
  have ha := a0.isLt; have hb := b0.isLt
  have hda := da.isLt; have hdb := db.isLt
  have hia := ia.isLt; have hib := ib.isLt
  unfold encode base maxCode
  omega

theorem maxCode_fits : maxCode ≤ 5^10 := by decide

def applyCapRaw (H : Nat) (p : Pos) (code : Nat) : Bool :=
  force (code / 5) fun w1 =>
  force (w1 / 5) fun w2 =>
  force (w2 / 32) fun w3 =>
  force (w3 / 32) fun w4 =>
  force (w4 / 3) fun w5 =>
  force (w5 / 3) fun w6 =>
  let t : Fin 5 := ⟨code%5,Nat.mod_lt _ (by decide)⟩
  let s : Fin 5 := ⟨w1%5,Nat.mod_lt _ (by decide)⟩
  CapTransfer.check H p t s (2*(w2%32)+1) (2*(w3%32)) (capMask H p t s)
    ⟨w4%3,Nat.mod_lt _ (by decide)⟩ ⟨w5%3,Nat.mod_lt _ (by decide)⟩
    ⟨w6%4,Nat.mod_lt _ (by decide)⟩ ⟨(w6/4)%4,Nat.mod_lt _ (by decide)⟩

theorem applyCapRaw_sound {H : Nat} {p : Pos} {code : Nat}
    (h : applyCapRaw H p code = true) : CapTransfer.L H p.toBoard := by
  simp only [applyCapRaw,force_eq] at h
  exact CapTransfer.check_leaf h

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

#print axioms leafSound
#print axioms gate_sound
end C4W5.CapTagged
