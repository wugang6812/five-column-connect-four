import WindowStretch
import C4W5.Tree.GFam

namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-- The original top-extension for G(3), using packed data in place of SG3.t. -/
theorem g3_of_window_bank (F : SFormat) (t : Bank)
    (ok : all F.radix (scheckRow 2 F t) t = true) (root : smem F t 14 g3p = true)
    (m : Nat) (hm : 7 ≤ m) : Safe (2*m) (G 3) := by
  have hq : g3p.toBoard = G 3 := by
    funext c
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  have e : 14 + 2 * (m-7) = 2*m := by omega
  have hs : SEq 2 14 g3p.toBoard (2*m) (G 3) := by
    rw [hq, ← e]
    exact seq_G3 (m-7)
  have hnw : ¬ HasFour (2*m) (G 3) .white := by
    intro hf
    have hn := (hs.hasFour_iff (by omega) .white).mpr hf
    rw [hq, ← G3_play] at hn
    exact no_four_of_run _ (by decide +kernel) hn
  exact stretch_safe_of_bank (by omega) F t ok root (toMove_G 3) hnw hs

#print axioms g3_of_window_bank
end C4W5.WindowBank
