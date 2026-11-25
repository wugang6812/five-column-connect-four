import WindowStretchExtra
import C4W5.Tree.StretchRoots
import C4W5.Tree.Sides

namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards

def stopPos : Pos := ⟨0, 170, 5, 1, 0, 0, 9, 3, 1, 0⟩

theorem stop_pos : stopPos.toBoard = Top 5 := by
  funext c
  obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl

theorem stop_play : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3] = Top 5 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, Top, centre, wb, opponent]

/-- Original Top family for every even height at least ten, with a sound extra certificate leaf. -/
theorem top_of_extra_window_bank (F : SFormat) (t : Bank)
    {L : Nat → Board 5 → Prop} (extra : Nat → Pos → Bool)
    (extraSound : ∀ h p, extra h p = true → L h p.toBoard)
    (extraLift : LeafSound 2 L)
    (ok : all F.radix (scheckExtraRow 2 F t extra) t = true)
    (root : smem F t 10 stopPos = true)
    (m : Nat) (hm : 5 ≤ m) : Safe (2*m) (Top m) := by
  have hs := seq_Top m hm
  have htm : toMove (Top m) = .white := by
    apply toMove_of_odd
    simp [Top, totalStones_ofCols, centre]; omega
  have hnw : ¬ HasFour (2*m) (Top m) .white := by
    intro hf
    have hn := (hs.hasFour_iff (by omega) .white).mpr hf
    rw [← stop_play] at hn
    exact no_four_of_run _ (by decide +kernel) hn
  rw [← stop_pos] at hs
  exact stretch_safe_of_extra_bank (by omega) F t extra extraSound extraLift ok root htm hnw hs

#print axioms top_of_extra_window_bank
end C4W5.WindowBank
