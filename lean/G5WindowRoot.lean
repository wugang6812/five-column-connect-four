import WindowStretch
import C4W5.Tree.GZone

namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards
set_option linter.deprecated false

theorem g5_zone_of_window_bank (F : SZFormat) (t : Bank)
    (ok : all F.radix (szcheckRow 2 F t) t = true)
    (root : szmem F t 14 g5p ⟨0, 0, 0, 0, 0⟩ = true) (m b : Nat) (hb : 5 ≤ b) (hbm : b + 3 ≤ m) :
    Safe (2 * m) (G b) := by
  have hlen : ∀ c, (G b c).length ≤ 2 * b + 4 := fun c => by
    have := G_len b (by omega) c; omega
  have hq : g5p.toBoard = G 5 := by
    funext c; obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  have hs : SEq 2 14 g5p.toBoard (2 * b + 4) (trunc (2 * b + 4) (G b)) := by
    rw [trunc_short hlen, hq]; exact seq_G_wall 4 (by omega) b hb
  have hs' : SEq 2 14 (G 5) (2 * b + 4) (G b) := seq_G_wall 4 (by omega) b hb
  have nf : ∀ p, ¬ HasFour 14 (G 5) p := by
    intro p hf
    rw [← G5_play] at hf
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
      (show (Pos.run 14 Pos.empty .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1]).isSome = true by decide)
    obtain ⟨e, hw, hb', -⟩ := root_of_run' hq
    rw [← e] at hf
    cases p
    · exact hb' hf
    · exact hw hf
  have nfb : ∀ p, ¬ HasFour (2 * m) (G b) p := fun p hf =>
    nf p ((hs'.hasFour_iff (by omega) p).mpr (hasFour_lower hlen hf))
  have hlab : (⟨0, 0, 0, 0, 0⟩ : Lab5).fn = labs (2 * m) (2 * b + 4) (G b) := by
    funext c
    have := hlen c
    simp only [labs, labOf]
    rw [if_pos this]
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  exact sz_safe_of_bank (by omega) F t ok (by omega) (by omega) (by omega) (toMove_G b)
    (nfb .white) (nfb .black) (G_discE b _ (by omega)) (G_tcol b _ _ (by omega) (by omega))
    (fun c => by have := hlen c; omega) root hlab hs


#print axioms g5_zone_of_window_bank
end C4W5.WindowBank
