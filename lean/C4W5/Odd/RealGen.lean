import C4W5.Base.Mirror
import C4W5.Odd.FastKey
import C4W5.Odd.ClaimBitsGen

/-!
# Color-Polymorphic Real-Board Steps & Pruned Certificate Checkers (`RealGen`)

Generalizes `C4W5/Base/Steps.lean` and `C4W5/Cert/Real.lean` + `Tree.lean` to an arbitrary
defender `me : Player` (`opp := opponent me`) with:
1. Opening step & mirror symmetry lemmas (`safeP_mirror`, `safeP_me_step`, `safeP_opp_step`, `safeP_opp_reply`).
2. Zero-node direct `ClaimOdd` / `ClaimEven` root theorems (`safeP_of_claimOdd_run`, `safeP_of_claimEven_run`),
   closing `H = 1` and `H = 3` in 0 tree nodes.
3. Leaf-pruned `CTree` real-board checker (`safeP_of_real_tree`, using O(log N) `rmem` + `fastOdd`/`fastEven`).
4. Unlabeled explicit-controller real-board checker (`safeP_of_explicit_real_tree`, using O(log N) `rumem`
   with **zero stored reply bytes**).

Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

/-! ## Opening Step & Mirror Symmetry Lemmas for Arbitrary Defender `me` -/

theorem mirror_ofColsG (a b c d e : List Player) :
    mirror (ofCols a b c d e) = ofCols e d c b a := by
  funext i; fin_cases i <;> rfl

theorem toMove_of_evenG {b : Board 5} (he : totalStones b % 2 = 0) : toMove b = .black := by
  unfold toMove; rw [if_pos he]

theorem toMove_of_oddG {b : Board 5} (ho : totalStones b % 2 = 1) : toMove b = .white := by
  unfold toMove; rw [if_neg (by omega)]

theorem toMove_of_totalParity {p : Pos} {pl : Player} (ht : p.total % 2 = turnParity pl) :
    toMove p.toBoard = pl := by
  unfold toMove
  rw [Pos.totalStones_eq]
  cases pl with
  | black => simp only [turnParity] at ht; rw [if_pos ht]
  | white => simp only [turnParity] at ht; rw [if_neg (by omega)]

theorem safeP_noOppFour {h : Nat} {me : Player} {b : Board 5} (hs : SafeP h me b) :
    ¬ HasFour h b (opponent me) :=
  hs 0

theorem safeP_mirror {h : Nat} {me : Player} {b : Board 5} (hs : SafeP h me b) :
    SafeP h me (mirror b) :=
  fun k => safeFor_mirror me k b (hs k)

theorem safeP_of_mirror {h : Nat} {me : Player} {b : Board 5} (hs : SafeP h me (mirror b)) :
    SafeP h me b := by
  have := safeP_mirror hs
  rwa [mirror_mirror] at this

theorem safeP_me_step {h : Nat} {me : Player} {b : Board 5} (ht : toMove b = me)
    {e : Fin 5} (he : Legal h b e) (hs : SafeP h me (play b e me)) :
    SafeP h me b := by
  have hno : ¬ HasFour h b (opponent me) :=
    fun hf => safeP_noOppFour hs (hasFour_play_mono hf e me)
  intro k
  cases k with
  | zero => exact hno
  | succ k =>
    refine ⟨hno, Or.inr (Or.inr ?_)⟩
    rw [if_pos ht]
    exact ⟨e, he, by rw [ht]; exact hs k⟩

theorem safeP_opp_step {h : Nat} {me : Player} {b : Board 5} (ht : toMove b = opponent me)
    (hno : ¬ HasFour h b (opponent me))
    (H : ∀ c, Legal h b c → SafeP h me (play b c (opponent me))) :
    SafeP h me b := by
  intro k
  cases k with
  | zero => exact hno
  | succ k =>
    refine ⟨hno, Or.inr (Or.inr ?_)⟩
    rw [if_neg (by rw [ht]; exact (ne_opponent me).symm)]
    intro c hc
    rw [ht]; exact H c hc k

theorem safeP_opp_reply {h : Nat} {me : Player} {b : Board 5} (ht : toMove b = opponent me)
    (hex : ∃ c, Legal h b c)
    (H : ∀ c, Legal h b c → ∃ e, Legal h (play b c (opponent me)) e ∧
      SafeP h me (play (play b c (opponent me)) e me)) :
    SafeP h me b := by
  have hchild : ∀ c, Legal h b c → SafeP h me (play b c (opponent me)) := fun c hc => by
    obtain ⟨e, he, hs⟩ := H c hc
    have htm1 : toMove (play b c (opponent me)) = me := by
      rw [toMove_play, ht, opponent_involution]
    exact safeP_me_step htm1 he hs
  obtain ⟨c0, hc0⟩ := hex
  have hno : ¬ HasFour h b (opponent me) := fun hf =>
    safeP_noOppFour (hchild c0 hc0) (hasFour_play_mono hf c0 (opponent me))
  exact safeP_opp_step ht hno hchild

/-! ## Zero-Node Direct `Claim` Root Theorems (Closes `H = 1` and `H = 3` Directly) -/

theorem safeP_of_claimOdd_run {h : Nat} {me : Player} (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q)
    (ht : q.total % 2 = turnParity (opponent me))
    (hc : fastOdd me h q = true) :
    SafeP h me (playList (emptyBoard 5) .black ms) := by
  obtain ⟨heq, hnw, hnb, _⟩ := root_of_run' hr
  rw [← heq]
  obtain ⟨col, hclaim⟩ := fastOdd_sound hc
  have hno : ¬ HasFour h q.toBoard (opponent me) := by cases me <;> simp only [opponent] <;> assumption
  have hnm : ¬ HasFour h q.toBoard me := by cases me <;> assumption
  exact claim_odd_safe hclaim (toMove_of_totalParity ht) hno hnm

theorem safeP_of_claimEven_run {h : Nat} {me : Player} (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q)
    (ht : q.total % 2 = turnParity (opponent me))
    (hc : fastEven me h q = true) :
    SafeP h me (playList (emptyBoard 5) .black ms) := by
  obtain ⟨heq, hnw, hnb, _⟩ := root_of_run' hr
  rw [← heq]
  have hno : ¬ HasFour h q.toBoard (opponent me) := by cases me <;> simp only [opponent] <;> assumption
  have hnm : ¬ HasFour h q.toBoard me := by cases me <;> assumption
  exact claim_even_safe (fastEven_sound hc) (toMove_of_totalParity ht) hno hnm

/-! ## Color-Polymorphic Leaf-Pruned Real-Board Checker -/

def colOKRG (h : Nat) (me : Player) (dest : Pos → Bool) (pos : Pos)
    (replyFn : Pos → Nat → Nat) (c : Nat) : Bool :=
  if Nat.ble h (pos.ht c) then true else
  forceP (pos.push c (opponent me)) fun p1 =>
  !p1.hasFourQ (opponent me) &&
  (if p1.fullF h then true else
    force (replyFn p1 c % 5) fun e =>
    Nat.blt (p1.ht e) h &&
    (forceP (p1.push e me) fun p2 =>
      p2.hasFourQ me || dest p2))

def stepOKRG (h : Nat) (me : Player) (dest : Pos → Bool)
    (replyFn : Pos → Nat → Nat) (pos : Pos) : Bool :=
  pos.wfB h && (pos.total % 2 == turnParity (opponent me)) &&
  colOKRG h me dest pos replyFn 0 &&
  colOKRG h me dest pos replyFn 1 &&
  colOKRG h me dest pos replyFn 2 &&
  colOKRG h me dest pos replyFn 3 &&
  colOKRG h me dest pos replyFn 4

private theorem stepOKRG_col {h : Nat} {me : Player} {dest : Pos → Bool}
    {replyFn : Pos → Nat → Nat} {pos : Pos}
    (hs : stepOKRG h me dest replyFn pos = true) (c : Fin 5) :
    colOKRG h me dest pos replyFn c.val = true := by
  unfold stepOKRG at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨-, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hs
  fin_cases c <;> assumption

private theorem stepOKRG_wf {h : Nat} {me : Player} {dest : Pos → Bool}
    {replyFn : Pos → Nat → Nat} {pos : Pos}
    (hs : stepOKRG h me dest replyFn pos = true) : pos.WF h := by
  unfold stepOKRG at hs
  simp only [Bool.and_eq_true] at hs
  exact Pos.wfB_sound hs.1.1.1.1.1.1

private theorem stepOKRG_toMove {h : Nat} {me : Player} {dest : Pos → Bool}
    {replyFn : Pos → Nat → Nat} {pos : Pos}
    (hs : stepOKRG h me dest replyFn pos = true) : toMove pos.toBoard = opponent me := by
  unfold stepOKRG at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact toMove_of_totalParity hs.1.1.1.1.1.2

private theorem safeFor_of_meFour {h : Nat} {me : Player} {b : Board 5}
    (hno : ¬ HasFour h b (opponent me)) (hme : HasFour h b me) (k : Nat) :
    SafeFor h me k b := by
  cases k with
  | zero => exact hno
  | succ _ => exact ⟨hno, Or.inl hme⟩

def RealLeafSound (h : Nat) (me : Player) (Leaf : Board 5 → Prop) : Prop :=
  ∀ {R : Board 5},
    toMove R = opponent me → ¬ HasFour h R (opponent me) → ¬ HasFour h R me →
    Leaf R → SafeP h me R

theorem claimOdd_realLeafSound (h : Nat) (me : Player) :
    RealLeafSound h me (fun R => ∃ q : Fin 5, ClaimOddHyp me h R q) := by
  intro R htm hno hnm ⟨q, hy⟩
  exact claim_odd_safe hy htm hno hnm

theorem claimEven_realLeafSound (h : Nat) (me : Player) :
    RealLeafSound h me (ClaimEvenHyp me h) := by
  intro R htm hno hnm hy
  exact claim_even_safe hy htm hno hnm

/-- Reflect a checked reply into board semantics before using any induction hypothesis.
    The opponent's move is checked for a first four even when it fills the board. -/
private theorem realColumnStep {h : Nat} {me : Player} {p : Pos} {c : Fin 5}
    {dest : Pos → Bool} {replyFn : Pos → Nat → Nat}
    (hwf : p.WF h) (hc : Legal h p.toBoard c)
    (hcheck : colOKRG h me dest p replyFn c.val = true) :
    ¬ HasFour h (play p.toBoard c (opponent me)) (opponent me) ∧
      (BoardFull h (play p.toBoard c (opponent me)) ∨
        ∃ e : Fin 5, Legal h (play p.toBoard c (opponent me)) e ∧
          ∃ q : Pos, q.toBoard = play (play p.toBoard c (opponent me)) e me ∧
            q.WF h ∧ (q.hasFourF me = true ∨ dest q = true)) := by
  have hc' : p.ht c.val < h := by
    change (p.toBoard c).length < h at hc
    rwa [Pos.height] at hc
  have hlt : ¬ (Nat.ble h (p.ht c.val) = true) := by
    rw [Nat.ble_eq]
    omega
  let p₁ := p.push c.val (opponent me)
  have hw₁ : p₁.WF h := Pos.WF_push hwf c (opponent me) hc'
  have hboard₁ : p₁.toBoard = play p.toBoard c (opponent me) :=
    Pos.toBoard_push hwf c (opponent me)
  unfold colOKRG at hcheck
  rw [if_neg hlt, forceP_eq, Bool.and_eq_true, Bool.not_eq_true', Pos.hasFourQ_eq] at hcheck
  obtain ⟨hno, hnext⟩ := hcheck
  refine ⟨?_, ?_⟩
  · intro hf
    rw [← hboard₁, ← hasFourF_iff hw₁, hno] at hf
    exact Bool.noConfusion hf
  · by_cases hfull : (p.push c.val (opponent me)).fullF h = true
    · exact Or.inl (by rw [← hboard₁]; exact Pos.fullF_sound hfull)
    · rw [if_neg hfull, force_eq, Bool.and_eq_true, Nat.blt_eq, forceP_eq,
          Bool.or_eq_true, Pos.hasFourQ_eq] at hnext
      obtain ⟨hleg, hnext⟩ := hnext
      let e : Fin 5 := ⟨replyFn p₁ c.val % 5, Nat.mod_lt _ (by decide)⟩
      let p₂ := p₁.push e.val me
      have hw₂ : p₂.WF h := Pos.WF_push hw₁ e me hleg
      have hboard₂ : p₂.toBoard = play (play p.toBoard c (opponent me)) e me := by
        change (p₁.push e.val me).toBoard = _
        rw [Pos.toBoard_push hw₁, hboard₁]
      refine Or.inr ⟨e, ?_, p₂, hboard₂, hw₂, hnext⟩
      change ((play p.toBoard c (opponent me)) e).length < h
      rw [← hboard₁, Pos.height]
      exact hleg

theorem cert_safeP_real {h : Nat} {me : Player} {Leaf : Board 5 → Prop}
    (hLeaf : RealLeafSound h me Leaf)
    (I : Pos → Prop)
    (hI : ∀ p, I p → ∃ (replyFn : Pos → Nat → Nat) (dest : Pos → Bool),
      (∀ q, dest q = true → I q ∨ Leaf q.toBoard) ∧
      stepOKRG h me dest replyFn p = true) :
    ∀ k p, I p → ¬ HasFour h p.toBoard (opponent me) → ¬ HasFour h p.toBoard me →
      SafeFor h me k p.toBoard := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro p hp hno hnm
    cases k with
    | zero => exact hno
    | succ k₁ =>
      obtain ⟨replyFn, dest, hdest, hcheck⟩ := hI p hp
      have htm := stepOKRG_toMove hcheck
      refine ⟨hno, Or.inr (Or.inr ?_)⟩
      rw [if_neg (by rw [htm]; exact (ne_opponent me).symm), htm]
      intro c hc
      obtain ⟨hno₁, hnext⟩ := realColumnStep (stepOKRG_wf hcheck) hc (stepOKRG_col hcheck c)
      cases k₁ with
      | zero => exact hno₁
      | succ k₂ =>
        refine ⟨hno₁, ?_⟩
        rcases hnext with hfull | ⟨e, he, q, hq, hwq, hnext⟩
        · exact Or.inr (Or.inl hfull)
        · have htm₁ : toMove (play p.toBoard c (opponent me)) = me := by
            rw [toMove_play, htm, opponent_involution]
          refine Or.inr (Or.inr ?_)
          rw [if_pos htm₁, htm₁]
          refine ⟨e, he, ?_⟩
          rw [← hq]
          have hno₂ : ¬ HasFour h q.toBoard (opponent me) := by
            rw [hq]
            exact fun hf => hno₁ (hasFour_play_other_gen (ne_opponent me) hf)
          by_cases hwin : q.hasFourF me = true
          · exact safeFor_of_meFour hno₂ ((hasFourF_iff hwq me).mp hwin) k₂
          · have hnm₂ : ¬ HasFour h q.toBoard me := fun hf => hwin ((hasFourF_iff hwq me).mpr hf)
            have haccepted : dest q = true := hnext.resolve_left hwin
            rcases hdest q haccepted with hi | hl
            · exact ih k₂ (by omega) q hi hno₂ hnm₂
            · have htm₂ : toMove q.toBoard = opponent me := by rw [hq, toMove_play, htm₁]
              exact hLeaf htm₂ hno₂ hnm₂ hl k₂

/-! ## Concrete Tree Wrappers: Labeled (`rmem`) and Unlabeled Explicit (`rumem`) -/

def realDest (t : CTree) (leafB : Pos → Bool) (q : Pos) : Bool :=
  rmem t q || leafB q

def realCheckW (h : Nat) (me : Player) (t : CTree) (leafB : Pos → Bool) (w : Nat) : Bool :=
  withUnpack9 (w / 3125) fun pos =>
    stepOKRG h me (realDest t leafB) (fun _ c => replyOf (w % 3125) c) pos

theorem safeP_of_real_tree {h : Nat} {me : Player} {Leaf : Board 5 → Prop}
    (hLeaf : RealLeafSound h me Leaf) {leafB : Pos → Bool}
    (hleafB : ∀ q, leafB q = true → Leaf q.toBoard)
    (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q)
    (hall : treeAllOK (realCheckW h me t leafB) t = true)
    (hq : rmem t q = true) :
    SafeP h me (playList (emptyBoard 5) .black ms) := by
  obtain ⟨heq, hnw, hnb, _⟩ := root_of_run' hr
  rw [← heq]
  have hno : ¬ HasFour h q.toBoard (opponent me) := by cases me <;> simp only [opponent] <;> assumption
  have hnm : ¬ HasFour h q.toBoard me := by cases me <;> assumption
  intro k
  refine cert_safeP_real hLeaf (fun p => ∃ w, TIn t w ∧ unpack9 (w / 3125) = p) ?_ k q
    (rmem_sound hq) hno hnm
  rintro p ⟨w, hin, rfl⟩
  have hw := treeAllOK_sound hall hin
  simp only [realCheckW, withUnpack9_eq] at hw
  refine ⟨fun _ c => replyOf (w % 3125) c, realDest t leafB, ?_, hw⟩
  intro q' hq'
  unfold realDest at hq'
  rw [Bool.or_eq_true] at hq'
  rcases hq' with hm | hl
  · exact Or.inl (rmem_sound hm)
  · exact Or.inr (hleafB q' hl)

def realUDest (t : CTree) (leafB : Pos → Bool) (q : Pos) : Bool :=
  rumem t q || leafB q

def realUCheckW (h : Nat) (me : Player) (t : CTree) (leafB : Pos → Bool)
    (replyFn : Pos → Nat → Nat) (w : Nat) : Bool :=
  withUnpack9 w fun pos =>
    stepOKRG h me (realUDest t leafB) replyFn pos

theorem safeP_of_explicit_real_tree {h : Nat} {me : Player} {Leaf : Board 5 → Prop}
    (hLeaf : RealLeafSound h me Leaf) {leafB : Pos → Bool}
    (hleafB : ∀ q, leafB q = true → Leaf q.toBoard)
    (replyFn : Pos → Nat → Nat)
    (t : CTree) (ms : List (Fin 5)) (q : Pos)
    (hr : Pos.run h Pos.empty .black ms = some q)
    (hall : treeAllOK (realUCheckW h me t leafB replyFn) t = true)
    (hq : rumem t q = true) :
    SafeP h me (playList (emptyBoard 5) .black ms) := by
  obtain ⟨heq, hnw, hnb, _⟩ := root_of_run' hr
  rw [← heq]
  have hno : ¬ HasFour h q.toBoard (opponent me) := by cases me <;> simp only [opponent] <;> assumption
  have hnm : ¬ HasFour h q.toBoard me := by cases me <;> assumption
  intro k
  refine cert_safeP_real hLeaf (fun p => ∃ w, TIn t w ∧ unpack9 w = p) ?_ k q
    (rumem_sound hq) hno hnm
  rintro p ⟨w, hin, rfl⟩
  have hw := treeAllOK_sound hall hin
  simp only [realUCheckW, withUnpack9_eq] at hw
  refine ⟨replyFn, realUDest t leafB, ?_, hw⟩
  intro q' hq'
  unfold realUDest at hq'
  rw [Bool.or_eq_true] at hq'
  rcases hq' with hm | hl
  · exact Or.inl (rumem_sound hm)
  · exact Or.inr (hleafB q' hl)

#print axioms safeP_of_real_tree
#print axioms safeP_of_explicit_real_tree

end C4W5Gen
