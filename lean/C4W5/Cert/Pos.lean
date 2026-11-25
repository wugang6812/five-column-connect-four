import C4W5.Base.Steps
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compact positions for kernel-checked certificates

A column is a pair (height, black mask): bit `r` of the mask is set iff the stone in row `r` is Black.
The representation is row-aligned, so fours can be found with a few bitwise operations, all of which
are GMP-accelerated in the kernel (`Nat.log2` is not, which is why heights are stored).
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

def bitP (b : Bool) : Player := if b then .black else .white

/-- Decode a column of height `h` with black mask `b`. -/
def decC : Nat → Nat → List Player
  | 0, _ => []
  | h + 1, b => decC h b ++ [bitP (b.testBit h)]

@[simp] theorem decC_length (h b : Nat) : (decC h b).length = h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [decC, ih]

theorem stone_decC (h b r : Nat) :
    stone (decC h b) r = if r < h then some (bitP (b.testBit r)) else none := by
  induction h with
  | zero => simp [decC, stone]
  | succ h ih =>
    rw [decC, stone_append, decC_length, ih]
    by_cases h1 : r < h
    · rw [if_pos h1, if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : r = h
      · subst h2; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem decC_congr (h b b' : Nat) (hb : ∀ r, r < h → b.testBit r = b'.testBit r) :
    decC h b = decC h b' := by
  induction h with
  | zero => rfl
  | succ h ih => rw [decC, decC, ih (fun r hr => hb r (by omega)), hb h (by omega)]

theorem testBit_false_of_lt {b h r : Nat} (hb : b < 2 ^ h) (hr : h ≤ r) : b.testBit r = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hr))

/-- A position: five columns as (black mask, height). -/
structure Pos where
  b0 : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  h0 : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat
  h4 : Nat
  deriving DecidableEq

def Pos.bm (p : Pos) : Nat → Nat
  | 0 => p.b0
  | 1 => p.b1
  | 2 => p.b2
  | 3 => p.b3
  | _ => p.b4

def Pos.ht (p : Pos) : Nat → Nat
  | 0 => p.h0
  | 1 => p.h1
  | 2 => p.h2
  | 3 => p.h3
  | _ => p.h4

/-- New black mask after a stone of colour `pl` lands at row `h`. -/
def pushM (b h : Nat) : Player → Nat
  | .black => b ||| 2 ^ h
  | .white => b

def Pos.push (p : Pos) (c : Nat) (pl : Player) : Pos :=
  match c with
  | 0 => { p with b0 := pushM p.b0 p.h0 pl, h0 := p.h0 + 1 }
  | 1 => { p with b1 := pushM p.b1 p.h1 pl, h1 := p.h1 + 1 }
  | 2 => { p with b2 := pushM p.b2 p.h2 pl, h2 := p.h2 + 1 }
  | 3 => { p with b3 := pushM p.b3 p.h3 pl, h3 := p.h3 + 1 }
  | _ => { p with b4 := pushM p.b4 p.h4 pl, h4 := p.h4 + 1 }

def Pos.empty : Pos := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Well-formed for board height `H`: masks fit below the heights, heights fit on the board. -/
def Pos.WF (H : Nat) (p : Pos) : Prop := ∀ c : Nat, p.bm c < 2 ^ p.ht c ∧ p.ht c ≤ H

def wf1 (H b h : Nat) : Bool := Nat.blt b (2 ^ h) && Nat.ble h H

def Pos.wfB (H : Nat) (p : Pos) : Bool :=
  wf1 H p.b0 p.h0 && wf1 H p.b1 p.h1 && wf1 H p.b2 p.h2 && wf1 H p.b3 p.h3 && wf1 H p.b4 p.h4

theorem wf1_sound {H b h : Nat} (hh : wf1 H b h = true) : b < 2 ^ h ∧ h ≤ H := by
  unfold wf1 at hh
  simpa only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] using hh

theorem Pos.wfB_sound {H : Nat} {p : Pos} (hh : p.wfB H = true) : p.WF H := by
  unfold Pos.wfB at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩ := hh
  intro c
  unfold Pos.bm Pos.ht
  split
  · exact wf1_sound a0
  · exact wf1_sound a1
  · exact wf1_sound a2
  · exact wf1_sound a3
  · exact wf1_sound a4

theorem Pos.WF_empty (H : Nat) : Pos.empty.WF H := by
  intro c; unfold Pos.bm Pos.ht; split <;> simp [Pos.empty]

theorem pushM_lt {b h : Nat} (hb : b < 2 ^ h) (pl : Player) : pushM b h pl < 2 ^ (h + 1) := by
  have h2 : 2 ^ (h + 1) = 2 ^ h + 2 ^ h := by rw [Nat.pow_succ]; omega
  cases pl
  · show b ||| 2 ^ h < 2 ^ (h + 1)
    exact Nat.or_lt_two_pow (by omega) (by omega)
  · show b < 2 ^ (h + 1)
    omega

theorem Pos.WF_push {H : Nat} {p : Pos} (hw : p.WF H) (c : Fin 5) (pl : Player)
    (hl : p.ht c.val < H) : (p.push c.val pl).WF H := by
  have a0 := hw 0
  have a1 := hw 1
  have a2 := hw 2
  have a3 := hw 3
  have a4 := hw 4
  simp only [Pos.bm, Pos.ht] at a0 a1 a2 a3 a4
  intro d
  fin_cases c <;> simp only [Pos.ht] at hl <;> rcases d with _ | _ | _ | _ | d <;>
    simp only [Pos.push, Pos.bm, Pos.ht] <;>
    first
      | assumption
      | exact ⟨pushM_lt a0.1 pl, hl⟩
      | exact ⟨pushM_lt a1.1 pl, hl⟩
      | exact ⟨pushM_lt a2.1 pl, hl⟩
      | exact ⟨pushM_lt a3.1 pl, hl⟩
      | exact ⟨pushM_lt a4.1 pl, hl⟩

def Pos.toBoard (p : Pos) : Board 5 := fun c => decC (p.ht c.val) (p.bm c.val)

theorem Pos.toBoard_empty : Pos.empty.toBoard = emptyBoard 5 := by
  funext c; fin_cases c <;> simp [Pos.toBoard, Pos.bm, Pos.ht, Pos.empty, decC, emptyBoard]

theorem decC_push {b h : Nat} (hb : b < 2 ^ h) (pl : Player) :
    decC (h + 1) (pushM b h pl) = decC h b ++ [pl] := by
  rw [decC]
  cases pl
  · show decC h (b ||| 2 ^ h) ++ [bitP ((b ||| 2 ^ h).testBit h)] = _
    rw [decC_congr h (b ||| 2 ^ h) b (fun r hr => by
      rw [Nat.testBit_or, Nat.testBit_two_pow]; simp; omega)]
    rw [Nat.testBit_or, Nat.testBit_two_pow_self]; simp [bitP]
  · show decC h b ++ [bitP (b.testBit h)] = _
    rw [testBit_false_of_lt hb (le_refl h)]; rfl

theorem Pos.toBoard_push {H : Nat} {p : Pos} (hw : p.WF H) (c : Fin 5) (pl : Player) :
    (p.push c.val pl).toBoard = play p.toBoard c pl := by
  funext d
  have hc := (hw c.val).1
  fin_cases c <;> fin_cases d <;>
    simp [Pos.toBoard, Pos.push, Pos.bm, Pos.ht, play] <;>
    (unfold Pos.bm Pos.ht at hc; exact decC_push hc pl)

theorem Pos.height (p : Pos) (c : Fin 5) : (p.toBoard c).length = p.ht c.val := decC_length _ _

theorem Pos.ht_push_self (p : Pos) (c : Fin 5) (pl : Player) : (p.push c.val pl).ht c.val = p.ht c.val + 1 := by
  fin_cases c <;> rfl

/-- Mask of the stones of colour `pl` in a column. -/
def maskOf (pl : Player) (b h : Nat) : Nat :=
  match pl with
  | .black => b
  | .white => (2 ^ h - 1) ^^^ b

theorem testBit_maskOf {b h : Nat} (hb : b < 2 ^ h) (pl : Player) (r : Nat) :
    (maskOf pl b h).testBit r = true ↔ stone (decC h b) r = some pl := by
  rw [stone_decC]
  by_cases hr : r < h
  · rw [if_pos hr]
    cases pl
    · show b.testBit r = true ↔ _
      cases hbit : b.testBit r <;> simp [bitP]
    · show ((2 ^ h - 1) ^^^ b).testBit r = true ↔ _
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
      cases hbit : b.testBit r <;> simp [bitP, hr]
  · rw [if_neg hr]
    have hf := testBit_false_of_lt hb (not_lt.mp hr)
    cases pl
    · show b.testBit r = true ↔ _
      simp [hf]
    · show ((2 ^ h - 1) ^^^ b).testBit r = true ↔ _
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]; simp [hf, hr]

def Pos.mask (p : Pos) (pl : Player) (c : Nat) : Nat := maskOf pl (p.bm c) (p.ht c)

/-- Cells of the decoded board, in terms of mask bits. -/
theorem cell_iff {H : Nat} {p : Pos} (hw : p.WF H) (pl : Player) (c : Fin 5) (y : Int) :
    cellAtInt H p.toBoard (c.val : Int) y = some pl ↔ 0 ≤ y ∧ (p.mask pl c.val).testBit y.toNat = true := by
  have hwc := hw c.val
  unfold Pos.mask
  rw [testBit_maskOf hwc.1]
  constructor
  · intro hs
    obtain ⟨d, hx, hy0, hyh, hst⟩ := cellAtInt_some hs
    have : d = c := by apply Fin.ext; omega
    subst this
    exact ⟨hy0, hst⟩
  · rintro ⟨hy0, hst⟩
    have hlt := stone_bound _ _ _ hst
    rw [decC_length] at hlt
    rw [cellAtInt_fin _ c y hy0 (by omega)]
    exact hst

end C4W5
