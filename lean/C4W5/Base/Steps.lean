import C4W5.Base.Safety

/-!
# One-move steps of the safety game

`Safe h b` is `CanAvoidLoss h .black b` from `Connect4.NarrowBoards`.  The proof tree is assembled with
three lemmas: `safe_black_step` (Black names a move), `safe_white_step` (every White move is answered)
and `safe_white_reply` (every White move is answered by a named Black reply).
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

variable {w h : Nat}

set_option linter.deprecated false

abbrev Safe (h : Nat) (b : Board w) : Prop := CanAvoidLoss h .black b

theorem cellAtInt_fin (b : Board w) (c : Fin w) (y : Int) (h0 : 0 ≤ y) (h1 : y < (h : Int)) :
    cellAtInt h b (c.val : Int) y = stone (b c) y.toNat := by
  have hc := c.isLt
  unfold cellAtInt
  rw [dif_pos (by omega), if_pos ⟨h0, h1⟩]
  congr 2

/-- Stones already on the board are not changed by a move. -/
theorem cellAtInt_play_of_some {b : Board w} {x y : Int} {p : Player}
    (hs : cellAtInt h b x y = some p) (c : Fin w) (q : Player) :
    cellAtInt h (play b c q) x y = some p := by
  obtain ⟨d, hx, hy0, hyh, hst⟩ := cellAtInt_some hs
  rw [hx, cellAtInt_fin _ d y hy0 hyh]
  by_cases hdc : d = c
  · subst hdc
    rw [play_eq, stone_append, if_pos (stone_bound _ _ _ hst)]
    exact hst
  · rw [play_ne b c d q hdc]; exact hst

theorem hasFourDir_play_mono {b : Board w} {p : Player} {x y dx dy : Int}
    (hf : HasFourDir h b p x y dx dy) (c : Fin w) (q : Player) :
    HasFourDir h (play b c q) p x y dx dy :=
  fun i => cellAtInt_play_of_some (hf i) c q

/-- A four stays a four after any further move. -/
theorem hasFour_play_mono {b : Board w} {p : Player} (hf : HasFour h b p) (c : Fin w) (q : Player) :
    HasFour h (play b c q) p := by
  rcases hf with ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩
  · exact Or.inl ⟨x, y, hasFourDir_play_mono hf c q⟩
  · exact Or.inr (Or.inl ⟨x, y, hasFourDir_play_mono hf c q⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, hasFourDir_play_mono hf c q⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, hasFourDir_play_mono hf c q⟩))

theorem safe_noWhiteFour {b : Board w} (hs : Safe h b) : ¬ HasFour h b .white := hs 0

/-- Black to move: one named move into a safe position suffices. -/
theorem safe_black_step {b : Board w} (ht : toMove b = .black) {e : Fin w} (he : Legal h b e)
    (hs : Safe h (play b e .black)) : Safe h b := by
  have hnw : ¬ HasFour h b .white := fun hf => safe_noWhiteFour hs (hasFour_play_mono hf e .black)
  intro k
  cases k with
  | zero => exact hnw
  | succ k =>
    refine ⟨hnw, Or.inr (Or.inr ?_)⟩
    rw [if_pos ht]
    exact ⟨e, he, by rw [ht]; exact hs k⟩

/-- White to move: every legal White move leads to a safe position. -/
theorem safe_white_step {b : Board w} (ht : toMove b = .white) (hnw : ¬ HasFour h b .white)
    (H : ∀ c, Legal h b c → Safe h (play b c .white)) : Safe h b := by
  intro k
  cases k with
  | zero => exact hnw
  | succ k =>
    refine ⟨hnw, Or.inr (Or.inr ?_)⟩
    have hne : ¬ toMove b = .black := by rw [ht]; decide
    rw [if_neg hne]
    intro c hc
    rw [ht]; exact H c hc k

theorem toMove_play_white {b : Board w} (ht : toMove b = .white) (c : Fin w) :
    toMove (play b c .white) = .black := by
  rw [toMove_play, ht]; rfl

theorem toMove_play_black {b : Board w} (ht : toMove b = .black) (c : Fin w) :
    toMove (play b c .black) = .white := by
  rw [toMove_play, ht]; rfl

/-- White to move, with a legal move available: every White move has a named safe Black reply. -/
theorem safe_white_reply {b : Board w} (ht : toMove b = .white) (hex : ∃ c, Legal h b c)
    (H : ∀ c, Legal h b c → ∃ e, Legal h (play b c .white) e ∧
      Safe h (play (play b c .white) e .black)) : Safe h b := by
  have hchild : ∀ c, Legal h b c → Safe h (play b c .white) := fun c hc => by
    obtain ⟨e, he, hs⟩ := H c hc
    exact safe_black_step (toMove_play_white ht c) he hs
  obtain ⟨c0, hc0⟩ := hex
  have hnw : ¬ HasFour h b .white := fun hf =>
    safe_noWhiteFour (hchild c0 hc0) (hasFour_play_mono hf c0 .white)
  exact safe_white_step ht hnw hchild

end C4W5
