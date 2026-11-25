import C4W5.Theory.ClaimStretch
import C4W5.Cert.Tree

/-!
# A kernel-friendly check of the claim criterion on compact positions

`claimB h p = true → ∃ q, ClaimHyp h p.toBoard q`.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

def cellBlack (h : Nat) (p : Pos) (x y : Int) : Bool :=
  decide (0 ≤ x) && decide (x < 5) && decide (0 ≤ y) && decide (y < (h : Int)) &&
    (p.bm x.toNat).testBit y.toNat

theorem cellBlack_sound {h : Nat} {p : Pos} (hw : p.WF h) {x y : Int}
    (hc : cellBlack h p x y = true) : cellAtInt h p.toBoard x y = some .black := by
  unfold cellBlack at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have hx : x = ((⟨x.toNat, by omega⟩ : Fin 5).val : Int) := by simp; omega
  rw [hx, cellAtInt_fin _ _ _ h3 h4]
  show stone (decC (p.ht x.toNat) (p.bm x.toNat)) y.toNat = some .black
  rw [stone_decC]
  have hlt : y.toNat < p.ht x.toNat := by
    by_contra hcon
    rw [testBit_false_of_lt (hw x.toNat).1 (by omega)] at h5
    cases h5
  rw [if_pos hlt, h5]; rfl

def lineJ (h : Nat) (p : Pos) (q : Fin 5) (h0 : Nat) (x y dy : Int) (j : Nat) : Bool :=
  cellBlack h p (x + (j : Int) * 1) (y + (j : Int) * dy) ||
  decide (Claimed q h0 (x + (j : Int) * 1) (y + (j : Int) * dy)) ||
  decide (¬ (0 ≤ x + (j : Int) * 1 ∧ x + (j : Int) * 1 < 5 ∧ 0 ≤ y + (j : Int) * dy ∧
      y + (j : Int) * dy < (h : Int)))

def lineOKB (h : Nat) (p : Pos) (q : Fin 5) (h0 : Nat) (x y dy : Int) : Bool :=
  lineJ h p q h0 x y dy 0 || lineJ h p q h0 x y dy 1 || lineJ h p q h0 x y dy 2 ||
    lineJ h p q h0 x y dy 3

theorem lineJ_sound {h : Nat} {p : Pos} (hw : p.WF h) {q : Fin 5} {h0 : Nat} {x y dy : Int}
    (j : Fin 4) (hj : lineJ h p q h0 x y dy j.val = true) : LineOK h p.toBoard q h0 x y dy := by
  unfold lineJ at hj
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hj
  rcases hj with (hj | hj) | hj
  · exact ⟨j, Or.inl (cellBlack_sound hw hj)⟩
  · exact ⟨j, Or.inr (Or.inl hj)⟩
  · exact ⟨j, Or.inr (Or.inr hj)⟩

theorem lineOKB_sound {h : Nat} {p : Pos} (hw : p.WF h) {q : Fin 5} {h0 : Nat} {x y dy : Int}
    (hl : lineOKB h p q h0 x y dy = true) : LineOK h p.toBoard q h0 x y dy := by
  unfold lineOKB at hl
  simp only [Bool.or_eq_true] at hl
  rcases hl with ((hl | hl) | hl) | hl
  · exact lineJ_sound hw 0 hl
  · exact lineJ_sound hw 1 hl
  · exact lineJ_sound hw 2 hl
  · exact lineJ_sound hw 3 hl

/-! Natural-number version (coordinates shifted by 3), which is what the kernel evaluates:
integer arithmetic is not accelerated. -/

/-- Shifted row of cell `j` of the line through `(c, r)` at offset `i`, direction `d`
(`0`: horizontal, `1`: rising, `2`: falling). -/
def yN (d r i j : Nat) : Nat :=
  match d with
  | 0 => r + 3
  | 1 => r + 3 - i + j
  | _ => r + 3 + i - j

def dyOf (d : Nat) : Int :=
  match d with
  | 0 => 0
  | 1 => 1
  | _ => -1

def lineJN (h : Nat) (p : Pos) (q h0 X Y : Nat) : Bool :=
  (decide (3 ≤ X ∧ X < 8 ∧ 3 ≤ Y ∧ Y < h + 3) && (p.bm (X - 3)).testBit (Y - 3)) ||
  decide (X = q + 3 ∧ h0 + 3 < Y ∧ (Y - 3 - h0) % 2 = 1) ||
  !decide (3 ≤ X ∧ X < 8 ∧ 3 ≤ Y ∧ Y < h + 3)

theorem lineJN_core {h : Nat} {p : Pos} (hw : p.WF h) {q : Fin 5} {h0 X Y : Nat} {x y : Int}
    (ex : (X : Int) = x + 3) (ey : (Y : Int) = y + 3) (hl : lineJN h p q.val h0 X Y = true) :
    cellAtInt h p.toBoard x y = some .black ∨ Claimed q h0 x y ∨
      ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (h : Int)) := by
  have hq := q.isLt
  unfold lineJN at hl
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hl
  rcases hl with (⟨a1, a5⟩ | a1) | hout
  · left
    apply cellBlack_sound hw
    unfold cellBlack
    have e1 : x.toNat = X - 3 := by omega
    have e2 : y.toNat = Y - 3 := by omega
    rw [e1, e2, a5]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
    omega
  · right; left
    exact ⟨by omega, by omega, by omega⟩
  · right; right
    intro hin
    apply hout
    omega

theorem lineJN_sound {h : Nat} {p : Pos} (hw : p.WF h) {q : Fin 5} {h0 c r d : Nat} (hd : d < 3)
    (i j : Fin 4) (hc : c < 5)
    (hl : lineJN h p q.val h0 (c + 3 - i.val + j.val) (yN d r i.val j.val) = true) :
    LineOK h p.toBoard q h0 ((c : Int) - (i.val : Int) * 1) ((r : Int) - (i.val : Int) * dyOf d)
      (dyOf d) := by
  have hi := i.isLt
  have hj := j.isLt
  have ey : ((yN d r i.val j.val : Nat) : Int) =
      (r : Int) - (i.val : Int) * dyOf d + (j.val : Int) * dyOf d + 3 := by
    have hd' : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd' with rfl | rfl | rfl <;> simp only [yN, dyOf] <;> omega
  have ex : ((c + 3 - i.val + j.val : Nat) : Int) =
      (c : Int) - (i.val : Int) * 1 + (j.val : Int) * 1 + 3 := by omega
  exact ⟨j, lineJN_core hw ex ey hl⟩

def linesDeadB (h : Nat) (p : Pos) (q : Fin 5) (h0 c r : Nat) : Bool :=
  ([0, 1, 2] : List Nat).all fun d => ([0, 1, 2, 3] : List Nat).all fun i =>
    ([0, 1, 2, 3] : List Nat).any fun j => lineJN h p q.val h0 (c + 3 - i + j) (yN d r i j)

theorem linesDeadB_sound {h : Nat} {p : Pos} (hw : p.WF h) {q : Fin 5} {h0 : Nat} {c : Fin 5}
    {r : Nat} (hl : linesDeadB h p q h0 c.val r = true) : LinesDead h p.toBoard q h0 c r := by
  unfold linesDeadB at hl
  rw [List.all_eq_true] at hl
  intro dy hdy i
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
  have hi := i.isLt
  obtain ⟨d, hd3, hdmem, hdy'⟩ : ∃ d, d < 3 ∧ d ∈ ([0, 1, 2] : List Nat) ∧ dyOf d = dy := by
    rcases hdy with rfl | rfl | rfl
    · exact ⟨0, by omega, by simp, rfl⟩
    · exact ⟨1, by omega, by simp, rfl⟩
    · exact ⟨2, by omega, by simp, rfl⟩
  have h1 := hl d hdmem
  rw [List.all_eq_true] at h1
  have h2 := h1 i.val (by simp; omega)
  rw [List.any_eq_true] at h2
  obtain ⟨j, hjm, hj⟩ := h2
  have hj4 : j < 4 := by simp at hjm; omega
  rw [← hdy']
  exact lineJN_sound hw hd3 i ⟨j, hj4⟩ c.isLt hj

def excB (p : Pos) (c r : Nat) : Bool :=
  Nat.blt r (p.ht c) && !(p.bm c).testBit r && (r == 0 || !(p.bm c).testBit (r - 1))

def potB (h : Nat) (p : Pos) (c r : Nat) : Bool :=
  r == p.ht c && Nat.blt (p.ht c) h && (p.ht c == 0 || !(p.bm c).testBit (p.ht c - 1))

theorem white_bit {ht bm r : Nat} (hs : stone (decC ht bm) r = some .white) :
    r < ht ∧ bm.testBit r = false := by
  rw [stone_decC] at hs
  by_cases hr : r < ht
  · rw [if_pos hr] at hs
    refine ⟨hr, ?_⟩
    cases hb : bm.testBit r
    · rfl
    · rw [hb] at hs; cases hs
  · rw [if_neg hr] at hs; cases hs

theorem excB_complete {p : Pos} {c : Fin 5} {r : Nat} (he : Exceptional p.toBoard c r) :
    excB p c.val r = true := by
  obtain ⟨h1, h2⟩ := he
  obtain ⟨a1, a2⟩ := white_bit (ht := p.ht c.val) (bm := p.bm c.val) h1
  unfold excB
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨a1, a2⟩, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (white_bit (ht := p.ht c.val) (bm := p.bm c.val) h2).2

theorem potB_complete {h : Nat} {p : Pos} {c : Fin 5} {r : Nat} (he : PotExc h p.toBoard c r) :
    potB h p c.val r = true := by
  obtain ⟨h1, h2, h3⟩ := he
  rw [Pos.height] at h1 h2 h3
  unfold potB
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨h1, h2⟩, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (white_bit (ht := p.ht c.val) (bm := p.bm c.val) h3).2

def allUpTo : Nat → (Nat → Bool) → Bool
  | 0, f => f 0
  | n + 1, f => f (n + 1) && allUpTo n f

theorem allUpTo_sound : ∀ (n : Nat) (f : Nat → Bool), allUpTo n f = true → ∀ r, r ≤ n → f r = true
  | 0, f, h, r, hr => by have : r = 0 := by omega
                         subst this; exact h
  | n + 1, f, h, r, hr => by
    unfold allUpTo at h
    rw [Bool.and_eq_true] at h
    by_cases e : r = n + 1
    · subst e; exact h.1
    · exact allUpTo_sound n f h.2 r (by omega)

def cellsOK (h : Nat) (p : Pos) (q : Fin 5) (h0 c : Nat) : Bool :=
  allUpTo h fun r => !(excB p c r || potB h p c r) || linesDeadB h p q h0 c r

def ntrB (h : Nat) (p : Pos) (c : Nat) : Bool :=
  !(Nat.blt (p.ht c) h) ||
    !(Nat.ble 3 (p.ht c) && !(p.bm c).testBit (p.ht c - 1) && !(p.bm c).testBit (p.ht c - 2) &&
      !(p.bm c).testBit (p.ht c - 3))

def colB (h : Nat) (p : Pos) (q : Fin 5) (c : Nat) : Bool :=
  ntrB h p c && cellsOK h p q (p.ht q.val) c

def claimQ (h : Nat) (p : Pos) (q : Fin 5) : Bool :=
  h % 2 == 0 && p.wfB h && (h - p.ht q.val) % 2 == 1 &&
    colB h p q 0 && colB h p q 1 && colB h p q 2 && colB h p q 3 && colB h p q 4

def claimB (h : Nat) (p : Pos) : Bool :=
  claimQ h p 0 || claimQ h p 1 || claimQ h p 2 || claimQ h p 3 || claimQ h p 4

theorem fin5c (c : Fin 5) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  revert c; decide

theorem claimQ_sound {h : Nat} {p : Pos} {q : Fin 5} (hq : claimQ h p q = true) :
    ClaimHyp h p.toBoard q := by
  unfold claimQ at hq
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨⟨⟨⟨⟨⟨he, hwf⟩, hodd⟩, c0⟩, c1⟩, c2⟩, c3⟩, c4⟩ := hq
  have hw := Pos.wfB_sound hwf
  have hcol : ∀ c : Fin 5, colB h p q c.val = true := by
    intro c
    obtain rfl | rfl | rfl | rfl | rfl := fin5c c
    exacts [c0, c1, c2, c3, c4]
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · intro c; rw [Pos.height]; exact (hw c.val).2
  · rw [Pos.height]; exact hodd
  · intro c hlt ht
    rw [Pos.height] at hlt
    have hc := hcol c
    unfold colB ntrB at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.ble_eq,
      decide_eq_false_iff_not] at hc
    obtain ⟨t0, t1, t2, t3⟩ := ht
    rw [Pos.height] at t0 t1 t2 t3
    have b1 := (white_bit (ht := p.ht c.val) (bm := p.bm c.val) t1).2
    have b2 := (white_bit (ht := p.ht c.val) (bm := p.bm c.val) t2).2
    have b3 := (white_bit (ht := p.ht c.val) (bm := p.bm c.val) t3).2
    rcases hc.1 with hc1 | hc1
    · rw [show (p.ht c.val).blt h = true from by rw [Nat.blt_eq]; exact hlt] at hc1; cases hc1
    · rw [show Nat.ble 3 (p.ht c.val) = true from by rw [Nat.ble_eq]; exact t0, b1, b2, b3] at hc1
      cases hc1
  · intro c r hcell
    rw [Pos.height]
    have hc := hcol c
    unfold colB cellsOK at hc
    rw [Bool.and_eq_true] at hc
    have hr : r ≤ h := by
      rcases hcell with he' | hp'
      · have := stone_bound _ _ _ he'.1
        rw [Pos.height] at this
        have := (hw c.val).2
        omega
      · obtain ⟨h1, h2, -⟩ := hp'
        rw [Pos.height] at h1 h2
        omega
    have := allUpTo_sound h _ hc.2 r hr
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with hno | hyes
    · rcases hcell with he' | hp'
      · rw [excB_complete he'] at hno; simp at hno
      · rw [potB_complete hp'] at hno; simp at hno
    · exact linesDeadB_sound hw hyes

theorem claimB_sound {h : Nat} {p : Pos} (hc : claimB h p = true) : ∃ q, ClaimHyp h p.toBoard q := by
  unfold claimB at hc
  simp only [Bool.or_eq_true] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  exacts [⟨0, claimQ_sound hc⟩, ⟨1, claimQ_sound hc⟩, ⟨2, claimQ_sound hc⟩, ⟨3, claimQ_sound hc⟩,
    ⟨4, claimQ_sound hc⟩]

#print axioms claimB_sound

end C4W5
