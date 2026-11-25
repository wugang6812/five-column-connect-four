import C4W5.Cert.Real

/-!
# Certificate containers and roots

`CTree`: a search tree of positions with reply words.  `Pos.run`: build a root from a move list while
checking that nobody makes a four on the way.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- A search tree of packed entries `w = key * 3125 + rep` (one numeral per position keeps the
generated files small and fast to elaborate). -/
inductive CTree where
  | leaf : CTree
  | node (l : CTree) (w : Nat) (r : CTree) : CTree

def keyOf (p : Pos) : Nat :=
  ((((((((p.b0 * 4294967311 + p.b1) * 4294967311 + p.b2) * 4294967311 + p.b3) * 4294967311 + p.b4) * 67 +
    p.h0) * 67 + p.h1) * 67 + p.h2) * 67 + p.h3) * 67 + p.h4

/-- Decode a key (inverse of `keyOf` on small positions; no inverse property is needed).
The multipliers are odd on purpose: forcing a numeral with a long run of trailing zero bits is
pathologically slow in the kernel. -/
def unpack (k : Nat) : Pos :=
  ⟨k / 1350125107 / 340282371674628239222339420534358459841,
   k / 1350125107 / 79228163344367823809576701231 % 4294967311,
   k / 1350125107 / 18446744202558570721 % 4294967311,
   k / 1350125107 / 4294967311 % 4294967311,
   k / 1350125107 % 4294967311,
   k / 20151121 % 67, k / 300763 % 67, k / 4489 % 67, k / 67 % 67, k % 67⟩

/-- The same, with every intermediate value forced. -/
def withUnpack {α : Sort _} (k : Nat) (f : Pos → α) : α := forceP (unpack k) f

@[simp] theorem withUnpack_eq {α : Sort _} (k : Nat) (f : Pos → α) : withUnpack k f = f (unpack k) := by
  simp [withUnpack]

def Pos.beq (p q : Pos) : Bool :=
  p.b0 == q.b0 && p.b1 == q.b1 && p.b2 == q.b2 && p.b3 == q.b3 && p.b4 == q.b4 &&
  p.h0 == q.h0 && p.h1 == q.h1 && p.h2 == q.h2 && p.h3 == q.h3 && p.h4 == q.h4

theorem Pos.eq_of_beq {p q : Pos} (h : p.beq q = true) : p = q := by
  unfold Pos.beq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h
  cases p; cases q; simp_all

/-- `In t p rep`: the tree holds position `p` with reply word `rep`. -/
inductive CTree.In : CTree → Pos → Nat → Prop
  | here (l w r) : CTree.In (.node l w r) (unpack (w / 3125)) (w % 3125)
  | left (l w r) {p q} : CTree.In l p q → CTree.In (.node l w r) p q
  | right (l w r) {p q} : CTree.In r p q → CTree.In (.node l w r) p q

def CTree.memK : CTree → Nat → Pos → Bool
  | .leaf, _, _ => false
  | .node l w r, k, p =>
    force (w / 3125) fun kq =>
    if k == kq then withUnpack kq fun q => q.beq p else if k < kq then l.memK k p else r.memK k p

def CTree.memB (t : CTree) (p : Pos) : Bool := force (keyOf p) fun k => t.memK k p

theorem CTree.memK_sound : ∀ (t : CTree) (k : Nat) (p : Pos), t.memK k p = true → ∃ rep, t.In p rep
  | .leaf, _, _, h => by simp [CTree.memK] at h
  | .node l w r, k, p, h => by
    unfold CTree.memK at h
    rw [force_eq] at h
    by_cases h1 : (k == w / 3125) = true
    · rw [if_pos h1, withUnpack_eq] at h
      have := Pos.eq_of_beq h
      subst this
      exact ⟨w % 3125, .here l w r⟩
    · rw [if_neg h1] at h
      by_cases h2 : k < w / 3125
      · rw [if_pos h2] at h
        obtain ⟨q, hq⟩ := CTree.memK_sound l k p h
        exact ⟨q, .left l w r hq⟩
      · rw [if_neg h2] at h
        obtain ⟨q, hq⟩ := CTree.memK_sound r k p h
        exact ⟨q, .right l w r hq⟩

def CTree.allOK (h : Nat) (memf : Pos → Bool) : CTree → Bool
  | .leaf => true
  | .node l w r => (withUnpack (w / 3125) fun pos => stepOK h memf pos (w % 3125)) && l.allOK h memf && r.allOK h memf

theorem CTree.allOK_sound {h : Nat} {memf : Pos → Bool} :
    ∀ (t : CTree), t.allOK h memf = true → ∀ p rep, t.In p rep → stepOK h memf p rep = true
  | .leaf, _, _, _, hin => by cases hin
  | .node l w r, hall, p, q, hin => by
    unfold CTree.allOK at hall
    simp only [Bool.and_eq_true, withUnpack_eq] at hall
    cases hin with
    | here => exact hall.1.1
    | left _ _ _ hl => exact CTree.allOK_sound l hall.1.2 p q hl
    | right _ _ _ hr => exact CTree.allOK_sound r hall.2 p q hr

theorem allOK_node {h : Nat} {memf : Pos → Bool} {l r : CTree} {w : Nat}
    (h1 : stepOK h memf (unpack (w / 3125)) (w % 3125) = true) (h2 : l.allOK h memf = true)
    (h3 : r.allOK h memf = true) : (CTree.node l w r).allOK h memf = true := by
  unfold CTree.allOK; rw [withUnpack_eq, h1, h2, h3]; rfl

theorem CTree.memB_sound (t : CTree) (p : Pos) (h : t.memB p = true) : ∃ rep, t.In p rep := by
  unfold CTree.memB at h; rw [force_eq] at h; exact CTree.memK_sound t _ p h

/-- A single self-contained certificate tree. -/
theorem tree_safe {h : Nat} (t : CTree) (hall : t.allOK h t.memB = true) {p : Pos}
    (hp : t.memB p = true) (hnw : ¬ HasFour h p.toBoard .white) : Safe h p.toBoard := by
  apply cert_safe (fun q => ∃ rep, t.In q rep) _ (CTree.memB_sound t p hp) hnw
  rintro q ⟨rep, hin⟩
  exact ⟨rep, t.memB, fun q' hq' => CTree.memB_sound t q' hq', CTree.allOK_sound t hall q rep hin⟩

/-! ## Roots from move lists -/

def playList (b : Board 5) : Player → List (Fin 5) → Board 5
  | _, [] => b
  | pl, c :: cs => playList (play b c pl) (opponent pl) cs

/-- Play the moves, failing if a move is illegal or somebody has a four afterwards. -/
def Pos.run (h : Nat) : Pos → Player → List (Fin 5) → Option Pos
  | p, _, [] => some p
  | p, pl, c :: cs =>
    if Nat.blt (p.ht c.val) h then
      let q := p.push c.val pl
      if q.hasFourF .white || q.hasFourF .black then none else Pos.run h q (opponent pl) cs
    else none

theorem hasFour_empty (h : Nat) (p : Player) : ¬ HasFour h (emptyBoard 5) p := by
  intro hf
  obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
  obtain ⟨c, -, -, -, hs⟩ := cellAtInt_some (hdir 0)
  have := stone_bound _ _ _ hs
  simp [emptyBoard] at this

theorem Pos.run_spec {h : Nat} : ∀ (ms : List (Fin 5)) (p : Pos) (pl : Player) (q : Pos),
    Pos.run h p pl ms = some q → p.WF h → ¬ HasFour h p.toBoard .white → ¬ HasFour h p.toBoard .black →
    q.toBoard = playList p.toBoard pl ms ∧ ¬ HasFour h q.toBoard .white ∧ ¬ HasFour h q.toBoard .black ∧
      q.WF h
  | [], p, pl, q, hr, hwf, hw, hb => by
    simp only [Pos.run, Option.some.injEq] at hr
    subst hr; exact ⟨rfl, hw, hb, hwf⟩
  | c :: cs, p, pl, q, hr, hwf, hw, hb => by
    simp only [Pos.run] at hr
    by_cases hleg : Nat.blt (p.ht c.val) h = true
    · rw [if_pos hleg] at hr
      have hwf1 : (p.push c.val pl).WF h := Pos.WF_push hwf c pl (by simpa using hleg)
      by_cases hwin : ((p.push c.val pl).hasFourF .white || (p.push c.val pl).hasFourF .black) = true
      · rw [if_pos hwin] at hr; cases hr
      · rw [if_neg hwin] at hr
        have hb1 := Pos.toBoard_push hwf c pl
        have hw' : ¬ HasFour h (p.push c.val pl).toBoard .white := by
          intro hf
          apply hwin
          rw [(hasFourF_iff hwf1 .white).mpr hf]; rfl
        have hb' : ¬ HasFour h (p.push c.val pl).toBoard .black := by
          intro hf
          apply hwin
          rw [(hasFourF_iff hwf1 .black).mpr hf]; simp
        obtain ⟨e, h1⟩ := Pos.run_spec cs _ _ q hr hwf1 hw' hb'
        refine ⟨?_, h1⟩
        rw [e, hb1]; rfl
    · rw [if_neg hleg] at hr; cases hr

/-- Root of a certificate, from the empty board. -/
theorem root_of_run' {h : Nat} {ms : List (Fin 5)} {q : Pos}
    (hr : Pos.run h Pos.empty .black ms = some q) :
    q.toBoard = playList (emptyBoard 5) .black ms ∧ ¬ HasFour h q.toBoard .white ∧
      ¬ HasFour h q.toBoard .black ∧ q.WF h := by
  have := Pos.run_spec ms Pos.empty .black q hr (Pos.WF_empty h)
    (by rw [Pos.toBoard_empty]; exact hasFour_empty h _)
    (by rw [Pos.toBoard_empty]; exact hasFour_empty h _)
  rw [Pos.toBoard_empty] at this
  exact this

theorem root_of_run {h : Nat} {ms : List (Fin 5)} {q : Pos}
    (hr : Pos.run h Pos.empty .black ms = some q) :
    q.toBoard = playList (emptyBoard 5) .black ms ∧ ¬ HasFour h q.toBoard .white :=
  ⟨(root_of_run' hr).1, (root_of_run' hr).2.1⟩

/-- The form used by generated certificate files. -/
theorem safe_of_tree {h : Nat} (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q) (hall : t.allOK h t.memB = true)
    (hq : t.memB q = true) : Safe h (playList (emptyBoard 5) .black ms) := by
  obtain ⟨e, hnw⟩ := root_of_run hr
  rw [← e]; exact tree_safe t hall hq hnw

#print axioms safe_of_tree

end C4W5
