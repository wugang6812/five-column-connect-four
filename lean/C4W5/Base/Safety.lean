import C4W5.Base.Defs

/-!
# The invariant principle

Every "Black does not lose" statement in the proof tree is proved by exhibiting a set of positions
that contains the root, contains no White four, and is closed under "any White move / some Black move".
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

variable {w : Nat}

set_option linter.deprecated false

/-- Safety invariant for Black. -/
structure BlackInvariant (h : Nat) (I : Board w → Prop) : Prop where
  noWhiteFour : ∀ b, I b → ¬ HasFour h b .white
  step : ∀ b, I b → HasFour h b .black ∨ BoardFull h b ∨
    (if toMove b = .black then ∃ c, Legal h b c ∧ I (play b c .black)
     else ∀ c, Legal h b c → I (play b c .white))

theorem canAvoidLoss_of_invariant {h : Nat} {I : Board w → Prop}
    (hI : BlackInvariant h I) {b : Board w} (hb : I b) : CanAvoidLoss h .black b := by
  intro k
  induction k generalizing b with
  | zero => exact hI.noWhiteFour b hb
  | succ k ih =>
    refine ⟨hI.noWhiteFour b hb, ?_⟩
    rcases hI.step b hb with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · refine Or.inr (Or.inr ?_)
      by_cases ht : toMove b = .black
      · rw [if_pos ht] at h3 ⊢
        obtain ⟨c, hc, hn⟩ := h3
        exact ⟨c, hc, by rw [ht]; exact ih hn⟩
      · rw [if_neg ht] at h3 ⊢
        have hw : toMove b = .white := by
          cases hm : toMove b with
          | black => exact absurd hm ht
          | white => rfl
        intro c hc
        rw [hw]; exact ih (h3 c hc)

end C4W5
