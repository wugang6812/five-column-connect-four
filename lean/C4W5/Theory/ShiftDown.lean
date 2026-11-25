import C4W5.Theory.Stretch
import C4W5.Base.Steps

/-!
# Shift-down lemma (下移引理, THEORY.md §2; precise form in ENDGAME_CRITERIA.md §0)

A White stone is *exceptional* if it is on the bottom row or rests on a White stone.
If no cell of a White four is exceptional, the four cells directly below form a Black four.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

variable {w : Nat}

set_option linter.deprecated false

def Exceptional (b : Board w) (c : Fin w) (r : Nat) : Prop :=
  stone (b c) r = some .white ∧ (r = 0 ∨ stone (b c) (r - 1) = some .white)

/-- **Shift-down lemma**, line form: if no cell of a White line is exceptional, the cells directly
below form a Black line of the same shape (any direction, including vertical). -/
theorem shift_down_line {h : Nat} {b : Board w} {x y dx dy : Int}
    (hf : HasFourDir h b .white x y dx dy)
    (hne : ∀ (i : Fin 4) (c : Fin w), x + (i : Int) * dx = (c.val : Int) →
      ¬ Exceptional b c (y + (i : Int) * dy).toNat) :
    HasFourDir h b .black x (y - 1) dx dy := by
  intro i
  obtain ⟨c, hx, hy0, hyh, hs⟩ := cellAtInt_some (hf i)
  have hlen := stone_bound _ _ _ hs
  have hnot := hne i c hx
  have hr : (y + (i : Int) * dy).toNat ≠ 0 := fun e => hnot ⟨hs, Or.inl e⟩
  obtain ⟨p, hp⟩ := stone_some_of_lt (b c) ((y + (i : Int) * dy).toNat - 1) (by omega)
  have hpb : p = .black := by
    cases p with
    | black => rfl
    | white => exact absurd ⟨hs, Or.inr hp⟩ hnot
  have e : y - 1 + (i : Int) * dy = y + (i : Int) * dy - 1 := by omega
  rw [e, hx, cellAtInt_fin b c _ (by omega) (by omega)]
  have e2 : (y + (i : Int) * dy - 1).toNat = (y + (i : Int) * dy).toNat - 1 := by omega
  rw [e2, hp, hpb]

/-- Contrapositive, the form used by the zone theorem and the endgame criteria: if Black has no
four, every White line contains an exceptional White stone. -/
theorem exists_exceptional_in_line {h : Nat} {b : Board w} {x y dx dy : Int}
    (hdir : (dx = 0 ∧ dy = 1) ∨ (dx = 1 ∧ dy = 0) ∨ (dx = 1 ∧ dy = 1) ∨ (dx = 1 ∧ dy = -1))
    (hnb : ¬ HasFour h b .black) (hf : HasFourDir h b .white x y dx dy) :
    ∃ (i : Fin 4) (c : Fin w), x + (i : Int) * dx = (c.val : Int) ∧
      Exceptional b c (y + (i : Int) * dy).toNat := by
  by_contra hcon
  have hne : ∀ (i : Fin 4) (c : Fin w), x + (i : Int) * dx = (c.val : Int) →
      ¬ Exceptional b c (y + (i : Int) * dy).toNat := fun i c hx he => hcon ⟨i, c, hx, he⟩
  have hb := shift_down_line hf hne
  apply hnb
  rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨x, y - 1, hb⟩
  · exact Or.inr (Or.inl ⟨x, y - 1, hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y - 1, hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y - 1, hb⟩))

theorem shift_down_dir {h : Nat} {b : Board w} {x y dx dy : Int}
    (hf : HasFourDir h b .white x y dx dy) (hne : ∀ c r, ¬ Exceptional b c r) :
    HasFourDir h b .black x (y - 1) dx dy :=
  shift_down_line hf (fun _ c _ => hne c _)

/-- If White has a four and no White stone is exceptional, Black has a four (one row lower). -/
theorem blackFour_of_whiteFour_of_no_exceptional {h : Nat} {b : Board w}
    (hf : HasFour h b .white) (hne : ∀ c r, ¬ Exceptional b c r) : HasFour h b .black := by
  rcases hf with ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩
  · exact Or.inl ⟨x, y - 1, shift_down_dir hf hne⟩
  · exact Or.inr (Or.inl ⟨x, y - 1, shift_down_dir hf hne⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y - 1, shift_down_dir hf hne⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y - 1, shift_down_dir hf hne⟩))

#print axioms exists_exceptional_in_line

end C4W5
