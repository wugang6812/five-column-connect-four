import C4W5.Theory.Stretch
import C4W5.Base.Steps

/-!
# Generalized Color-Polymorphic Shift-Down Lemma (`ShiftDownGen`)

Generalizes `C4W5/Theory/ShiftDown.lean` to an arbitrary attacker `opp : Player`
(with defender `opponent opp`). Works identically for:
- Even-height Black (`opp = .white`)
- Odd-height Black  (`opp = .white`)
- Odd-height White  (`opp = .black`)

Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

variable {w : Nat}

set_option linter.deprecated false

/-- An attacker stone `opp` is *exceptional* if it rests on the floor (`r = 0`)
    or directly atop another attacker stone `opp`. -/
def ExceptionalP (opp : Player) (b : Board w) (c : Fin w) (r : Nat) : Prop :=
  stone (b c) r = some opp ∧ (r = 0 ∨ stone (b c) (r - 1) = some opp)

theorem player_eq_or_eq_opponent (opp p : Player) : p = opp ∨ p = opponent opp := by
  cases opp <;> cases p <;> simp [opponent]

/-- **Generalized shift-down lemma (line form)**: if no cell of an attacker (`opp`)
    four-in-a-row is exceptional, the four cells directly below form a defender
    (`opponent opp`) four-in-a-row of the exact same shape. -/
theorem shift_down_line_gen {h : Nat} {b : Board w} {opp : Player} {x y dx dy : Int}
    (hf : HasFourDir h b opp x y dx dy)
    (hne : ∀ (i : Fin 4) (c : Fin w), x + (i : Int) * dx = (c.val : Int) →
      ¬ ExceptionalP opp b c (y + (i : Int) * dy).toNat) :
    HasFourDir h b (opponent opp) x (y - 1) dx dy := by
  intro i
  obtain ⟨c, hx, hy0, hyh, hs⟩ := cellAtInt_some (hf i)
  have hlen := stone_bound _ _ _ hs
  have hnot := hne i c hx
  have hr : (y + (i : Int) * dy).toNat ≠ 0 := fun e => hnot ⟨hs, Or.inl e⟩
  obtain ⟨p, hp⟩ := stone_some_of_lt (b c) ((y + (i : Int) * dy).toNat - 1) (by omega)
  have hpdef : p = opponent opp := by
    rcases player_eq_or_eq_opponent opp p with rfl | hdef
    · exact absurd ⟨hs, Or.inr hp⟩ hnot
    · exact hdef
  have e : y - 1 + (i : Int) * dy = y + (i : Int) * dy - 1 := by omega
  rw [e, hx, cellAtInt_fin b c _ (by omega) (by omega)]
  have e2 : (y + (i : Int) * dy - 1).toNat = (y + (i : Int) * dy).toNat - 1 := by omega
  rw [e2, hp, hpdef]

/-- **Contrapositive form**: if defender (`opponent opp`) has no four-in-a-row,
    every attacker (`opp`) four-in-a-row contains at least one exceptional `opp` stone. -/
theorem exists_exceptional_in_line_gen {h : Nat} {b : Board w} {opp : Player} {x y dx dy : Int}
    (hdir : (dx = 0 ∧ dy = 1) ∨ (dx = 1 ∧ dy = 0) ∨ (dx = 1 ∧ dy = 1) ∨ (dx = 1 ∧ dy = -1))
    (hnd : ¬ HasFour h b (opponent opp)) (hf : HasFourDir h b opp x y dx dy) :
    ∃ (i : Fin 4) (c : Fin w), x + (i : Int) * dx = (c.val : Int) ∧
      ExceptionalP opp b c (y + (i : Int) * dy).toNat := by
  by_contra hcon
  have hne : ∀ (i : Fin 4) (c : Fin w), x + (i : Int) * dx = (c.val : Int) →
      ¬ ExceptionalP opp b c (y + (i : Int) * dy).toNat := fun i c hx he => hcon ⟨i, c, hx, he⟩
  have hdef := shift_down_line_gen hf hne
  apply hnd
  rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨x, y - 1, hdef⟩
  · exact Or.inr (Or.inl ⟨x, y - 1, hdef⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y - 1, hdef⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y - 1, hdef⟩))

theorem shift_down_dir_gen {h : Nat} {b : Board w} {opp : Player} {x y dx dy : Int}
    (hf : HasFourDir h b opp x y dx dy) (hne : ∀ c r, ¬ ExceptionalP opp b c r) :
    HasFourDir h b (opponent opp) x (y - 1) dx dy :=
  shift_down_line_gen hf (fun _ c _ => hne c _)

/-- If attacker `opp` has a four and no `opp` stone is exceptional,
    defender `opponent opp` already has a four one row lower. -/
theorem defenderFour_of_attackerFour_of_no_exceptional {h : Nat} {b : Board w} {opp : Player}
    (hf : HasFour h b opp) (hne : ∀ c r, ¬ ExceptionalP opp b c r) :
    HasFour h b (opponent opp) := by
  rcases hf with ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩
  · exact Or.inl ⟨x, y - 1, shift_down_dir_gen hf hne⟩
  · exact Or.inr (Or.inl ⟨x, y - 1, shift_down_dir_gen hf hne⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y - 1, shift_down_dir_gen hf hne⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y - 1, shift_down_dir_gen hf hne⟩))

#print axioms exists_exceptional_in_line_gen

end C4W5Gen
