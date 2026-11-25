import WindowStretchExtra

namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-- Generic tight/mid G(5) lift. This theorem assumes the full bank has checked;
    it does not assert a generated-bank acceptance that has not yet happened. -/
theorem g5_wall_of_extra_window_bank (F : SFormat) (t : Bank)
    {L : Nat → Board 5 → Prop} (extra : Nat → Pos → Bool)
    (extraSound : ∀ h p, extra h p = true → L h p.toBoard)
    (extraLift : LeafSound 2 L)
    (ok : all F.radix (scheckExtraRow 2 F t extra) t = true)
    (g : Nat) (hg : g = 2 ∨ g = 4)
    (root : smem F t (10 + g) g5p = true) (b : Nat) (hb : 5 ≤ b) :
    Safe (2 * b + g) (G b) := by
  have hq : g5p.toBoard = G 5 := by
    funext c
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  have hs : SEq 2 (10 + g) g5p.toBoard (2 * b + g) (G b) := by
    rw [hq]; exact seq_G_wall g (by omega) b hb
  have hnw : ¬ HasFour (2 * b + g) (G b) .white := by
    intro hf
    have hn := (hs.hasFour_iff (by omega) .white).mpr hf
    rw [hq, ← G5_play] at hn
    have run : (Pos.run (10 + g) Pos.empty .black
      [2,2,2,1,1,1,1,1,1,1,1,1,1,3,1]).isSome = true := by
      rcases hg with rfl | rfl <;> decide +kernel
    exact no_four_of_run _ run hn
  exact stretch_safe_of_extra_bank (by omega) F t extra extraSound extraLift ok root
    (toMove_G b) hnw hs

#print axioms g5_wall_of_extra_window_bank
end C4W5.WindowBank
