import C4W5.Tree.Chain

/-!
# First player does not lose on five columns, every even height — reduced to the cells

`Certificates` lists every statement that is not yet proved inside Lean.  The final theorem is proved
from it with no other assumption.  Each field is to be discharged by one of the theory files
(zone theorem, stretch theorem, Top theorem) plus a kernel-checked certificate; when a field has been
proved it is removed from this structure.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- After 3, W1, B1 (White to move). -/
def P311 : B5 := ofCols [.white, .black] [] [.black] [] []
/-- After 3, W2, B2 (White to move). -/
def P322 : B5 := ofCols [] [.white, .black] [.black] [] []

/-- The opening: Black 3; White's five replies. -/
theorem empty_safe_of {h : Nat} (h4 : 4 ≤ h) (c311 : Safe h P311) (c322 : Safe h P322)
    (t0 : Safe h (T 0)) : Safe h (emptyBoard 5) := by
  rw [emptyBoard_eq]
  apply safe_black_step (e := 2) (toMove_of_even (by simp [totalStones_ofCols]))
    (by simp [Legal]; omega)
  rw [play_ofCols_2]
  apply safe_white_reply (toMove_of_odd (by simp [totalStones_ofCols])) ⟨0, by simp [Legal]; omega⟩
  intro c hc
  obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c
  · refine ⟨0, by simp [Legal, play_ofCols_0]; omega, ?_⟩
    simp only [play_ofCols_0, List.nil_append, List.cons_append]; exact c311
  · refine ⟨1, by simp [Legal, play_ofCols_1]; omega, ?_⟩
    simp only [play_ofCols_1, List.nil_append, List.cons_append]; exact c322
  · refine ⟨2, by simp [Legal, play_ofCols_2]; omega, ?_⟩
    simp only [play_ofCols_2, List.nil_append, List.cons_append]; exact t0
  · refine ⟨3, by simp [Legal, play_ofCols_3]; omega, ?_⟩
    have e : play (play (ofCols [] [] ([] ++ [Player.black]) [] []) 3 .white) 3 .black = mirror P322 := by
      simp only [P322, play_ofCols_3, mirror_ofCols, List.nil_append, List.cons_append]
    rw [e]; exact safe_mirror c322
  · refine ⟨4, by simp [Legal, play_ofCols_4]; omega, ?_⟩
    have e : play (play (ofCols [] [] ([] ++ [Player.black]) [] []) 4 .white) 4 .black = mirror P311 := by
      simp only [P311, play_ofCols_4, mirror_ofCols, List.nil_append, List.cons_append]
    rw [e]; exact safe_mirror c311

/-- Everything that is not yet proved in Lean. -/
structure Certificates : Prop where
  /-- Height 2. -/
  small2 : Safe 2 (emptyBoard 5)
  /-- After 3, W1, B1: every even height ≥ 4. -/
  c311 : ∀ m : Nat, 2 ≤ m → Safe (2 * m) P311
  /-- After 3, W2, B2: every even height ≥ 4. -/
  c322 : ∀ m : Nat, 2 ≤ m → Safe (2 * m) P322
  /-- 333 at heights 4…12 (direct computation). -/
  t0_small : ∀ m : Nat, 2 ≤ m → m ≤ 6 → Safe (2 * m) (T 0)
  /-- The cells below the chain, heights ≥ 14. -/
  chain : ∀ m : Nat, 7 ≤ m → ChainCells m

/-- **Main theorem, conditional on the listed cells.**  On five columns and every even height the
first player does not lose.  Same definitions as `Connect4.FourColumns.black_nonloss_four_columns`. -/
theorem black_nonloss_five_columns_of (C : Certificates) {h : Nat} (h2 : 2 ≤ h) (hh : h % 2 = 0) :
    CanAvoidLoss h .black (emptyBoard 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, h = 2 * m := ⟨h / 2, by omega⟩
  by_cases hm1 : m = 1
  · subst hm1; exact C.small2
  · have hm2 : 2 ≤ m := by omega
    apply empty_safe_of (by omega) (C.c311 m hm2) (C.c322 m hm2)
    by_cases hm6 : m ≤ 6
    · exact C.t0_small m hm2 hm6
    · exact T0_safe (by omega) (C.chain m (by omega))

#print axioms black_nonloss_five_columns_of

end C4W5
