import C4W5.Compact.Contracts

/-! Preserve the historical central opening types without importing Tree.DrawBase.
    The core argument is the historical CentralOpening's five-way split, supplied
    here by the compact Contracts layer instead of its full legacy table chain. -/
namespace C4W5.Compact
open Connect4 (Player)
open Connect4.NarrowBoards

abbrev centerOpening : Board 5 := play (emptyBoard 5) 2 .black

theorem same_column_reply_of (C : Certificates) {m : Nat} (hm : 2 ≤ m) (c : Fin 5) :
    Legal (2*m) (play centerOpening c .white) c ∧
    Safe (2*m) (play (play centerOpening c .white) c .black) := by
  have t0 : Safe (2*m) (T 0) := by
    by_cases small : m ≤ 6
    · exact C.t0_small m hm small
    · exact T0_safe (by omega) (C.chain m (by omega))
  unfold centerOpening
  rw [emptyBoard_eq, play_ofCols_2]
  constructor
  · obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;>
      simp [Legal, play_ofCols_0, play_ofCols_1, play_ofCols_2, play_ofCols_3, play_ofCols_4] <;> omega
  · obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c
    · simp only [play_ofCols_0, List.nil_append, List.cons_append]
      exact C.c311 m hm
    · simp only [play_ofCols_1, List.nil_append, List.cons_append]
      exact C.c322 m hm
    · simp only [play_ofCols_2, List.nil_append, List.cons_append]
      exact t0
    · simpa only [P322, mirror_ofCols, play_ofCols_2, play_ofCols_3,
        List.nil_append, List.cons_append] using safe_mirror (C.c322 m hm)
    · simpa only [P311, mirror_ofCols, play_ofCols_2, play_ofCols_4,
        List.nil_append, List.cons_append] using safe_mirror (C.c311 m hm)

private theorem white_after_black_first (m : Nat) (hm : 1 ≤ m) (c : Fin 5) :
    CanAvoidLoss (2*m) .white (play (emptyBoard 5) c .black) := by
  have noWhite : ¬ HasFour (2*m) (emptyBoard 5) .white := FiveAllis.no_four_empty5 _
  have room : ¬ BoardFull (2*m) (emptyBoard 5) := by
    intro full
    have h0 := full (0 : Fin 5)
    simp [emptyBoard] at h0
    omega
  intro k
  have branches := (FiveAllis.white_nonloss_five m hm (k+1)).2
  have allMoves : ∀ e : Fin 5, Legal (2*m) (emptyBoard 5) e →
      SafeFor (2*m) .white k (play (emptyBoard 5) e .black) := by
    simpa [noWhite, room, FiveAllis.toMove_empty] using branches
  exact allMoves c (by simp [Legal,emptyBoard]; omega)

theorem draw_after_center_of (C : Certificates) (h2 : Safe 2 centerOpening) {m : Nat}
    (hm : 1 ≤ m) : IsDraw (2*m) centerOpening := by
  constructor
  · by_cases small : m = 1
    · subst m; exact h2
    · apply safe_white_reply (by rw [toMove_play_black (FiveAllis.toMove_empty 5)])
        ⟨0, by simp [centerOpening, Legal, play, emptyBoard, Function.update]; omega⟩
      intro c _
      exact ⟨c, same_column_reply_of C (by omega) c⟩
  · exact white_after_black_first m hm 2

#print axioms same_column_reply_of
#print axioms draw_after_center_of
end C4W5.Compact
