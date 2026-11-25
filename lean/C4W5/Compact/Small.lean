import C4W5.Compact.SmallCore
import C4W5.Compact.Cert.H8_322_known_dag
import EvenClaimSharded.H8_311_known_dag.Main
import EvenClaimSharded.H8_333_known_dag.Main

/-! Empty-board even draw through height 8 using only compact candidate certificates. -/
namespace C4W5.Compact
open Connect4.NarrowBoards

theorem safe311_8 : Safe 8 P311 := play311 ▸ C4W5Gen.EvenClaimSharded.H8_311_known_dag.safe
theorem safe322_8 : Safe 8 P322 := play322 ▸ C4W5Gen.EvenClaimPilot.H8_322_known_dag.safe
theorem safe333_8 : Safe 8 (T 0) := play333 ▸ C4W5Gen.EvenClaimSharded.H8_333_known_dag.safe

theorem even_draw_le8 {h : Nat} (h2 : 2 ≤ h) (he : h % 2 = 0) (h8 : h ≤ 8) :
    IsDraw h (emptyBoard 5) := by
  by_cases h6 : h ≤ 6
  · exact even_draw_le6 h2 he h6
  · have hh : h = 8 := by omega
    subst h
    exact draw_of_black_safe (by omega) (by omega)
      (empty_safe_of (by omega) safe311_8 safe322_8 safe333_8)

#print axioms even_draw_le8
end C4W5.Compact
