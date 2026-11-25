import WindowZoneEnds
import CapDoubleMasks
import CapTaggedGate

/-! Source-stage SGZ-only tagged witness lookup. No controller or game changes. -/
namespace C4W5.WindowBank.ZoneTagged
open Connect4.NarrowBoards C4W5.WindowBank
open C4W5.CapTagged (base maxCode capMask)

abbrev CapTest := Nat → Pos → Fin 5 → Fin 5 → Nat → Nat → Nat →
    Fin 3 → Fin 3 → Fin 4 → Fin 4 → Bool

def longCode (t : Fin 5) (rho : Fin 61) (mask : Fin 32) (d : Fin 3) (i : Fin 4) : Nat :=
  t.val + 5 * (rho.val + 61 * (mask.val + 32 * (d.val + 3 * i.val)))

/-- Existing Long codes are strictly below the Cap tag range. -/
theorem longCode_lt_base (t : Fin 5) (rho : Fin 61) (mask : Fin 32) (d : Fin 3) (i : Fin 4) :
    longCode t rho mask d i < base := by
  have ht := t.isLt
  have hr := rho.isLt
  have hm := mask.isLt
  have hd := d.isLt
  have hi := i.isLt
  unfold longCode base
  omega

/-- Policy reply payload base is unchanged. This is a width bound, not a
    certificate correctness or exact-decoding assumption. -/
theorem tag_fits (t s : Fin 5) (a0 b0 : Fin 32) (da db : Fin 3) (ia ib : Fin 4) :
    base ≤ CapTagged.encode t s a0 b0 da db ia ib ∧
      CapTagged.encode t s a0 b0 da db ia ib < 5^10 := by
  have h := CapTagged.encode_range t s a0 b0 da db ia ib
  exact ⟨h.1, lt_of_lt_of_le h.2 CapTagged.maxCode_fits⟩

/-- Exactly the existing parity-compressed Cap fields, with strict-low maximal Q.
    The reference and post-only evaluators differ only in the mask scan. -/
def applyCap (test : CapTest) (k : Nat) (p : Pos) (raw : Nat) : Bool :=
  force (raw / 5) fun w1 =>
  force (w1 / 5) fun w2 =>
  force (w2 / 32) fun w3 =>
  force (w3 / 32) fun w4 =>
  force (w4 / 3) fun w5 =>
  force (w5 / 3) fun w6 =>
  let t : Fin 5 := ⟨raw % 5, Nat.mod_lt _ (by decide)⟩
  let s : Fin 5 := ⟨w1 % 5, Nat.mod_lt _ (by decide)⟩
  test k p t s (2 * (w2 % 32) + 1) (2 * (w3 % 32)) (capMask k p t s)
    ⟨w4 % 3, Nat.mod_lt _ (by decide)⟩ ⟨w5 % 3, Nat.mod_lt _ (by decide)⟩
    ⟨w6 % 4, Nat.mod_lt _ (by decide)⟩ ⟨(w6 / 4) % 4, Nat.mod_lt _ (by decide)⟩

def capTest (postOnly : Bool) : CapTest :=
  if postOnly then CapFast.checkPost else CapFast.check

theorem applyCap_sound (postOnly : Bool) {k : Nat} {p : Pos} {raw : Nat}
    (h : applyCap (capTest postOnly) k p raw = true) : CapTransfer.L k p.toBoard := by
  simp only [applyCap, force_eq] at h
  cases postOnly
  · exact CapFast.check_leaf h
  · exact CapFast.checkPost_leaf h

def applyTagged (postOnly : Bool) (k : Nat) (p : Pos) (code : Nat) : Bool :=
  if code < base then applyWitness LongThreat.SZ.checkZone k p code
  else if code < maxCode then applyCap (capTest postOnly) k p (code - base)
  else false

theorem applyTagged_sound (postOnly : Bool) {k : Nat} {p : Pos} {code : Nat}
    (h : applyTagged postOnly k p code = true) : ZoneEnds.SZ.Extra k p.toBoard := by
  unfold applyTagged at h
  split at h
  · simp only [applyWitness, force_eq] at h
    exact ZoneEnds.SZ.checkLongExtra h
  · split at h
    · exact Or.inr (applyCap_sound postOnly h)
    · cases h

/-- One hint lookup for both terminal types, on the complete Zone key. A hit
    must decode to the exact queried height, masks/heights, and all five labels;
    and its witness is independently checked on the queried board itself. -/
def gate (postOnly : Bool) (F : SZFormat) (hints : Bank) : ZEndGate :=
  fun k p l => force (F.key k p l) fun key =>
    match find F.radix F.repBase key hints with
    | none => false
    | some w => (F.height w == k) && (F.pos w).beq p && (F.labels w).beq l &&
      applyTagged postOnly k p (w % F.repBase)

theorem gate_sound (postOnly : Bool) (F : SZFormat) (hints : Bank) (k : Nat) (p : Pos)
    (l : Lab5) (h : gate postOnly F hints k p l = true) : ZoneEnds.SZ.Extra k p.toBoard := by
  simp only [gate, force_eq] at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h
    exact applyTagged_sound postOnly h.2

/-- The two actual public arithmetic assumptions and exact existing G b goal
    are retained. This theorem is conditional on checked concrete policy data. -/
theorem g5_wide_of_tagged (F : SZFormat) (policy hints : Bank)
    (ok : all F.radix (zoneEndsRow 2 F policy (gate true F hints)) policy = true)
    (root : szmem F policy 14 g5p ⟨0, 0, 0, 0, 0⟩ = true)
    (m b : Nat) (hb : 5 ≤ b) (hbm : b + 3 ≤ m) :
    Safe (2 * m) (G b) :=
  g5_zone_ends F policy (gate true F hints) (gate_sound true F hints) ok root m b hb hbm

#print axioms longCode_lt_base
#print axioms tag_fits
#print axioms applyTagged_sound
#print axioms gate_sound
#print axioms g5_wide_of_tagged
end C4W5.WindowBank.ZoneTagged
