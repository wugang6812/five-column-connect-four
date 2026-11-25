import C4W5.Tree.Main
import C4W5.Allis.Strategy
import C4W5.Compact.Cert.H2_compact
import C4W5.Compact.Cert.H4_311_compact
import C4W5.Compact.Cert.H4_322_compact
import C4W5.Compact.Cert.H4_333_compact
import C4W5.Compact.Cert.H6_311_prefer_leaf
import C4W5.Compact.Cert.H6_322_prefer_leaf
import C4W5.Compact.Cert.H6_333_prefer_leaf

/-! Empty-board even draw through height 6, without historical generated modules. -/
namespace C4W5.Compact
open Connect4 (Player opponent)
open Connect4.NarrowBoards

theorem play311 : playList (emptyBoard 5) .black [2, 0, 0] = P311 := by
  simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_2, P311, opponent]

theorem play322 : playList (emptyBoard 5) .black [2, 1, 1] = P322 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, P322, opponent]

theorem play333 : playList (emptyBoard 5) .black [2, 2, 2] = T 0 := by
  simp [playList, emptyBoard_eq, play_ofCols_2, T, centre, wb, opponent]

theorem safe2 : Safe 2 (emptyBoard 5) := by
  apply safe_black_step (e := 2)
    (by rw [emptyBoard_eq]; exact toMove_of_even (by simp [totalStones_ofCols]))
    (by simp [Legal, emptyBoard])
  exact C4W5Gen.EvenCompact.H2_3.safe

theorem safe311_4 : Safe 4 P311 := play311 ▸ C4W5Gen.EvenClaimPilot.H4_311_known_dag.safe
theorem safe322_4 : Safe 4 P322 := play322 ▸ C4W5Gen.EvenClaimPilot.H4_322_known_dag.safe
theorem safe333_4 : Safe 4 (T 0) := play333 ▸ C4W5Gen.EvenClaimPilot.H4_333_known_dag.safe
theorem safe311_6 : Safe 6 P311 := play311 ▸ C4W5Gen.EvenClaimPilot.H6_311_prefer_leaf.safe
theorem safe322_6 : Safe 6 P322 := play322 ▸ C4W5Gen.EvenClaimPilot.H6_322_prefer_leaf.safe
theorem safe333_6 : Safe 6 (T 0) := play333 ▸ C4W5Gen.EvenClaimPilot.H6_333_prefer_leaf.safe

theorem white_nonloss {h : Nat} (h2 : 2 ≤ h) (he : h % 2 = 0) :
    CanAvoidLoss h .white (emptyBoard 5) := by
  have hh : 2 * (h / 2) = h := by omega
  simpa only [hh] using FiveAllis.white_nonloss_five (h / 2) (by omega)

theorem draw_of_black_safe {h : Nat} (h2 : 2 ≤ h) (he : h % 2 = 0)
    (hs : Safe h (emptyBoard 5)) : IsDraw h (emptyBoard 5) :=
  ⟨hs, white_nonloss h2 he⟩

theorem even_draw_le6 {h : Nat} (h2 : 2 ≤ h) (he : h % 2 = 0) (h6 : h ≤ 6) :
    IsDraw h (emptyBoard 5) := by
  apply draw_of_black_safe h2 he
  have cases : h = 2 ∨ h = 4 ∨ h = 6 := by omega
  rcases cases with rfl | rfl | rfl
  · exact safe2
  · exact empty_safe_of (by omega) safe311_4 safe322_4 safe333_4
  · exact empty_safe_of (by omega) safe311_6 safe322_6 safe333_6

#print axioms even_draw_le6
end C4W5.Compact
