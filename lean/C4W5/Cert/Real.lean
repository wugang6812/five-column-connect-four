import C4W5.Cert.Fast

/-!
# Certificates for real boards

A certificate is a set of positions (White to move), each with Black's reply to every White move.
`colOK` checks one White move; `stepOK` checks a position.  `cert_safe`: if every position of the set
passes, Black does not lose from any of them.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

def Pos.total (p : Pos) : Nat := p.h0 + p.h1 + p.h2 + p.h3 + p.h4

def Pos.fullF (h : Nat) (p : Pos) : Bool :=
  p.h0 == h && p.h1 == h && p.h2 == h && p.h3 == h && p.h4 == h

theorem Pos.totalStones_eq (p : Pos) : Connect4.NarrowBoards.totalStones p.toBoard = p.total := by
  simp [Connect4.NarrowBoards.totalStones, Fin.sum_univ_five, Pos.toBoard, Pos.ht, Pos.total]

theorem Pos.fullF_sound {h : Nat} {p : Pos} (hf : p.fullF h = true) : BoardFull h p.toBoard := by
  unfold Pos.fullF at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hf
  intro c
  rw [Pos.height]
  fin_cases c <;> simp [Pos.ht, *]

/-- Black's reply to White's move in column `c`, read from the packed reply word. -/
def replyOf (rep c : Nat) : Nat := (rep / 5 ^ c) % 5

/-- White plays column `c` (if legal); is the position after Black's recorded reply fine? -/
def colOK (h : Nat) (memf : Pos → Bool) (pos : Pos) (rep c : Nat) : Bool :=
  if h ≤ pos.ht c then true else
  forceP (pos.push c .white) fun p1 =>
  !p1.hasFourQ .white &&
  (if p1.fullF h then true else
    force (replyOf rep c) fun e =>
    Nat.blt (p1.ht e) h &&
    (forceP (p1.push e .black) fun p2 =>
     p2.hasFourQ .black || memf p2))

def stepOK (h : Nat) (memf : Pos → Bool) (pos : Pos) (rep : Nat) : Bool :=
  pos.wfB h && pos.total % 2 == 1 && colOK h memf pos rep 0 && colOK h memf pos rep 1 &&
  colOK h memf pos rep 2 && colOK h memf pos rep 3 && colOK h memf pos rep 4

theorem stepOK_col {h : Nat} {memf : Pos → Bool} {pos : Pos} {rep : Nat}
    (hs : stepOK h memf pos rep = true) (c : Fin 5) : colOK h memf pos rep c.val = true := by
  unfold stepOK at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨-, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hs
  fin_cases c <;> assumption

theorem stepOK_wf {h : Nat} {memf : Pos → Bool} {pos : Pos} {rep : Nat}
    (hs : stepOK h memf pos rep = true) : pos.WF h := by
  unfold stepOK at hs
  simp only [Bool.and_eq_true] at hs
  exact Pos.wfB_sound hs.1.1.1.1.1.1

theorem stepOK_toMove {h : Nat} {memf : Pos → Bool} {pos : Pos} {rep : Nat}
    (hs : stepOK h memf pos rep = true) : toMove pos.toBoard = .white := by
  unfold stepOK at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  unfold toMove
  rw [Pos.totalStones_eq, if_neg (by omega)]

theorem safeFor_of_blackFour {h : Nat} {b : Board 5} (hnw : ¬ HasFour h b .white)
    (hb : HasFour h b .black) (k : Nat) : SafeFor h .black k b := by
  cases k with
  | zero => exact hnw
  | succ k => exact ⟨hnw, Or.inl hb⟩

/-- **Soundness of real-board certificates.** -/
theorem cert_safeFor {h : Nat} (I : Pos → Prop)
    (hI : ∀ p, I p → ∃ (rep : Nat) (memf : Pos → Bool),
      (∀ q, memf q = true → I q) ∧ stepOK h memf p rep = true) :
    ∀ k p, I p → ¬ HasFour h p.toBoard .white → SafeFor h .black k p.toBoard := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hp hnw
    obtain ⟨rep, memf, hmem, hstep⟩ := hI p hp
    have htm := stepOK_toMove hstep
    have hwf := stepOK_wf hstep
    cases k with
    | zero => exact hnw
    | succ k =>
      refine ⟨hnw, Or.inr (Or.inr ?_)⟩
      have hne : ¬ toMove p.toBoard = .black := by rw [htm]; decide
      rw [if_neg hne, htm]
      intro c hc
      have hcol := stepOK_col hstep c
      unfold colOK at hcol
      have hlt' : p.ht c.val < h := by
        have : (p.toBoard c).length < h := hc
        rwa [Pos.height] at this
      have hlt : ¬ h ≤ p.ht c.val := by omega
      rw [if_neg hlt] at hcol
      simp only [forceP_eq, force_eq, Pos.hasFourQ_eq] at hcol
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcol
      obtain ⟨hw, hrest⟩ := hcol
      have hwf1 : (p.push c.val .white).WF h := Pos.WF_push hwf c .white hlt'
      have hb1 : (p.push c.val .white).toBoard = play p.toBoard c .white := Pos.toBoard_push hwf c .white
      have hnw1 : ¬ HasFour h (play p.toBoard c .white) .white := by
        intro hf
        rw [← hb1, ← hasFourF_iff hwf1, hw] at hf
        exact Bool.noConfusion hf
      cases k with
      | zero => exact hnw1
      | succ k =>
        refine ⟨hnw1, ?_⟩
        by_cases hfull : (p.push c.val .white).fullF h = true
        · exact Or.inr (Or.inl (by rw [← hb1]; exact Pos.fullF_sound hfull))
        · rw [if_neg hfull] at hrest
          simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true] at hrest
          obtain ⟨hleg, hfin⟩ := hrest
          refine Or.inr (Or.inr ?_)
          have htb : toMove (play p.toBoard c .white) = .black := toMove_play_white htm c
          rw [if_pos htb, htb]
          let e : Fin 5 := ⟨replyOf rep c.val, Nat.mod_lt _ (by decide)⟩
          have hwf2 : ((p.push c.val .white).push e.val .black).WF h := Pos.WF_push hwf1 e .black hleg
          have hb2 : ((p.push c.val .white).push e.val .black).toBoard =
              play (play p.toBoard c .white) e .black := by
            rw [Pos.toBoard_push hwf1, hb1]
          have hnw2 : ¬ HasFour h (play (play p.toBoard c .white) e .black) .white :=
            fun hf => hnw1 (hasFour_play_other (by decide) hf)
          refine ⟨e, ?_, ?_⟩
          · show ((play p.toBoard c .white) e).length < h
            rw [← hb1, Pos.height]; exact hleg
          · rcases hfin with hwin | hm
            · exact safeFor_of_blackFour hnw2 (by rw [← hb2]; exact (hasFourF_iff hwf2 _).mp hwin) k
            · have := ih k (by omega) _ (hmem _ hm) (by rw [hb2]; exact hnw2)
              rw [hb2] at this; exact this

theorem cert_safe {h : Nat} (I : Pos → Prop)
    (hI : ∀ p, I p → ∃ (rep : Nat) (memf : Pos → Bool),
      (∀ q, memf q = true → I q) ∧ stepOK h memf p rep = true)
    {p : Pos} (hp : I p) (hnw : ¬ HasFour h p.toBoard .white) : Safe h p.toBoard :=
  fun k => cert_safeFor I hI k p hp hnw

#print axioms cert_safe

end C4W5
