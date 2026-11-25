import C4W5.Odd.Gen.W5_B1W2.Main
import C4W5.Odd.Gen.W5_B2W2.Main
import C4W5.Odd.Gen.W5_B3W2.Main
import C4W5.Odd.Gen.W7_B1W2.Main
import C4W5.Odd.Gen.W7_B2W3.Main
import C4W5.Odd.Gen.W7_B3W2.Main
import C4W5.Odd.Gen.W9_B2W3_B4W2.Main
import C4W5.Odd.Gen.W9_B2W3_B3W3.Main
import C4W5.Odd.Gen.WZ7_B3W2.Main
import C4W5.Odd.Gen.WZ7_B1W2.Main
import C4W5.Odd.Gen.WZ7_B2W3_B1W3.Main
import C4W5.Odd.Gen.WZ7_B2W3_B2W2.Main
import C4W5.Odd.Gen.WZ7_B2W3_B5W3.Main
import C4W5.Odd.Gen.WZ9_B2W3_B4W2.Main
import C4W5.Odd.Gen.WZ9_B2W3_B3W3.Main

/-!
# Second-Player Non-Loss on All Odd Heights `5 × (2m+1)` (`OddWhite`)

Proves `odd_white_nonloss : ∀ {h : Nat}, 1 ≤ h → h % 2 = 1 → CanAvoidLoss h .white (emptyBoard 5)`
using `ClaimOdd` leaf pruning and horizontal
mirror symmetry (`safeP_mirror` for `B4` and `B5`):
- `h = 1, 3`: 0-node direct `ClaimOdd` evaluation (`safeP_of_claimOdd_run`).
- `h = 5`: finite pruned trees `W5_B1W2` (99), `W5_B2W2` (2,656), `W5_B3W2` (16).
- `h = 7`: finite pruned trees `W7_B1W2` (326), `W7_B2W3` (14,124), `W7_B3W2` (22).
- `h = 9`: `K = 7` zone certificates (`7 + 2 ≤ 9`) for `B1W2`, `B3W2`, and `B2W3·{B1W3, B2W2, B5W3}`,
           plus finite pruned trees `W9_B2W3_B4W2` (10,668) and `W9_B2W3_B3W3` (20,593).
- All odd `h ≥ 11`: the same five `K = 7` certificates and two lifted `K = 9` certificates.

The two `K = 9` certificates never stand in for an `h = 9` real-board proof: lifting
requires `K + 2 ≤ h`. The two finite H9 certificates fill exactly this gap.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

private theorem mirror_emptyBoard5 : mirror (emptyBoard 5) = emptyBoard 5 := by
  funext c; rfl

private theorem mirror_playList2 (c w : Fin 5) :
    mirror (playList (emptyBoard 5) .black [c, w]) =
      play (play (emptyBoard 5) c.rev .black) w.rev .white := by
  symm
  calc
    play (play (emptyBoard 5) c.rev .black) w.rev .white
      = play (play (mirror (emptyBoard 5)) c.rev .black) w.rev .white := by
          rw [mirror_emptyBoard5]
    _ = play (mirror (play (emptyBoard 5) c.rev.rev .black)) w.rev .white := by
          rw [play_mirror]
    _ = mirror (play (play (emptyBoard 5) c.rev.rev .black) w.rev.rev .white) := by
          rw [play_mirror]
    _ = mirror (playList (emptyBoard 5) .black [c, w]) := by
          simp only [Fin.rev_rev, playList, opponent]

/-- Generic first-ply opening reducer for White on `emptyBoard 5`, deriving `B4` (`3`) and `B5` (`4`)
    from `B2` (`1`) and `B1` (`0`) by horizontal reflection (`safeP_mirror`). -/
theorem empty_white_safe_of {h : Nat} (h1 : 1 ≤ h)
    (c01 : SafeP h .white (playList (emptyBoard 5) .black [0, 1]))
    (c1w : ∃ w : Fin 5, Legal h (play (emptyBoard 5) 1 .black) w ∧
      SafeP h .white (playList (emptyBoard 5) .black [1, w]))
    (c21 : SafeP h .white (playList (emptyBoard 5) .black [2, 1])) :
    SafeP h .white (emptyBoard 5) := by
  have htm : toMove (emptyBoard 5) = .black := by
    rw [emptyBoard_eq]
    exact toMove_of_evenG (by simp [totalStones_ofCols])
  apply safeP_opp_reply (me := .white) htm ⟨0, by simp [Legal, emptyBoard] <;> omega⟩
  intro c _
  fin_cases c
  · refine ⟨1, ?_, c01⟩
    simp [Legal, emptyBoard_eq, play_ofCols_0] <;> omega
  · obtain ⟨w, hw_leg, hw_safe⟩ := c1w
    exact ⟨w, hw_leg, hw_safe⟩
  · refine ⟨1, ?_, c21⟩
    simp [Legal, emptyBoard_eq, play_ofCols_2] <;> omega
  · obtain ⟨w, hw_leg, hw_safe⟩ := c1w
    refine ⟨w.rev, ?_, ?_⟩
    · change Legal h (play (emptyBoard 5) (3 : Fin 5) .black) w.rev
      have hm : play (emptyBoard 5) (3 : Fin 5) .black = mirror (play (emptyBoard 5) 1 .black) := by
        funext i; fin_cases i <;> rfl
      rw [hm, legal_mirror, Fin.rev_rev]
      exact hw_leg
    · change SafeP h .white (play (play (emptyBoard 5) (3 : Fin 5) .black) w.rev .white)
      have hm := mirror_playList2 1 w
      have hr : (1 : Fin 5).rev = 3 := by decide
      rw [hr] at hm
      rw [← hm]
      exact safeP_mirror hw_safe
  · refine ⟨3, ?_, ?_⟩
    · simp [Legal, emptyBoard_eq, play_ofCols_4] <;> omega
    · change SafeP h .white (play (play (emptyBoard 5) (4 : Fin 5) .black) (3 : Fin 5) .white)
      have hm := mirror_playList2 0 1
      have hr0 : (0 : Fin 5).rev = 4 := by decide
      have hr1 : (1 : Fin 5).rev = 3 := by decide
      rw [hr0, hr1] at hm
      rw [← hm]
      exact safeP_mirror c01

/-- Second-ply opening reducer after `B2 · W3` (`[1, 2]`) for `h ≥ 9`. -/
theorem b2w3_white_safe_of {h : Nat} (h9 : 9 ≤ h)
    (d0 : SafeP h .white (playList (emptyBoard 5) .black [1, 2, 0, 2]))
    (d1 : SafeP h .white (playList (emptyBoard 5) .black [1, 2, 1, 1]))
    (d2 : SafeP h .white (playList (emptyBoard 5) .black [1, 2, 2, 2]))
    (d3 : SafeP h .white (playList (emptyBoard 5) .black [1, 2, 3, 1]))
    (d4 : SafeP h .white (playList (emptyBoard 5) .black [1, 2, 4, 2])) :
    SafeP h .white (playList (emptyBoard 5) .black [1, 2]) := by
  have hb_eq : playList (emptyBoard 5) .black [1, 2] = ofCols [] [.black] [.white] [] [] := by
    simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, opponent]
  have htm : toMove (playList (emptyBoard 5) .black [1, 2]) = .black := by
    rw [hb_eq]
    exact toMove_of_evenG (by simp [totalStones_ofCols])
  have hex : ∃ c : Fin 5, Legal h (playList (emptyBoard 5) .black [1, 2]) c := by
    refine ⟨0, ?_⟩
    rw [hb_eq]; simp [Legal] <;> omega
  apply safeP_opp_reply (me := .white) htm hex
  intro c _
  fin_cases c
  · refine ⟨2, ?_, d0⟩
    rw [hb_eq]; simp [Legal, play_ofCols_0] <;> omega
  · refine ⟨1, ?_, d1⟩
    rw [hb_eq]; simp [Legal, play_ofCols_1] <;> omega
  · refine ⟨2, ?_, d2⟩
    rw [hb_eq]; simp [Legal, play_ofCols_2] <;> omega
  · refine ⟨1, ?_, d3⟩
    rw [hb_eq]; simp [Legal, play_ofCols_3] <;> omega
  · refine ⟨2, ?_, d4⟩
    rw [hb_eq]; simp [Legal, play_ofCols_4] <;> omega

/-! ## Finite Base Heights `h = 1, 3, 5, 7, 9` -/

private def posW_01 : Pos := ⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩
private def posW_12 : Pos := ⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩
private def posW_21 : Pos := ⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩

private theorem white_h1 : SafeP 1 .white (emptyBoard 5) := by
  refine empty_white_safe_of (by decide) ?_ ?_ ?_
  · exact safeP_of_claimOdd_run [0, 1] posW_01 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine ⟨2, by simp [Legal, emptyBoard_eq, play_ofCols_1], ?_⟩
    exact safeP_of_claimOdd_run [1, 2] posW_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact safeP_of_claimOdd_run [2, 1] posW_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem white_h3 : SafeP 3 .white (emptyBoard 5) := by
  refine empty_white_safe_of (by decide) ?_ ?_ ?_
  · exact safeP_of_claimOdd_run [0, 1] posW_01 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine ⟨2, by simp [Legal, emptyBoard_eq, play_ofCols_1], ?_⟩
    exact safeP_of_claimOdd_run [1, 2] posW_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact safeP_of_claimOdd_run [2, 1] posW_21 (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem white_h5 : SafeP 5 .white (emptyBoard 5) :=
  empty_white_safe_of (by decide)
    W5_B1W2.safe
    ⟨1, by simp [Legal, emptyBoard_eq, play_ofCols_1], W5_B2W2.safe⟩
    W5_B3W2.safe

private theorem white_h7 : SafeP 7 .white (emptyBoard 5) :=
  empty_white_safe_of (by decide)
    W7_B1W2.safe
    ⟨2, by simp [Legal, emptyBoard_eq, play_ofCols_1], W7_B2W3.safe⟩
    W7_B3W2.safe

/-- The common Zone assembly for `h ≥ 9`. Only the middle two continuations need
    separate finite (H9) and lifted (H≥11) sources. -/
private theorem white_zone_with_two {h : Nat} (h9 : 9 ≤ h) (ho : h % 2 = 1)
    (d2 : SafeP h .white (playList (emptyBoard 5) .black [1, 2, 2, 2]))
    (d3 : SafeP h .white (playList (emptyBoard 5) .black [1, 2, 3, 1])) :
    SafeP h .white (emptyBoard 5) := by
  have hgap : 7 + 2 ≤ h := h9
  have hp7 : 7 % 2 = h % 2 := by omega
  refine empty_white_safe_of (by omega)
    (WZ7_B1W2.safe h hp7 hgap)
    ?_
    (WZ7_B3W2.safe h hp7 hgap)
  refine ⟨2, by simp [Legal, emptyBoard_eq, play_ofCols_1] <;> omega, ?_⟩
  exact b2w3_white_safe_of h9
    (WZ7_B2W3_B1W3.safe h hp7 hgap)
    (WZ7_B2W3_B2W2.safe h hp7 hgap)
    d2 d3
    (WZ7_B2W3_B5W3.safe h hp7 hgap)

private theorem white_h9 : SafeP 9 .white (emptyBoard 5) :=
  white_zone_with_two (by decide) (by decide)
    W9_B2W3_B3W3.safe
    W9_B2W3_B4W2.safe

private theorem white_odd_ge_eleven {h : Nat} (h11 : 11 ≤ h) (ho : h % 2 = 1) :
    SafeP h .white (emptyBoard 5) := by
  have hgap : 9 + 2 ≤ h := h11
  have hp9 : 9 % 2 = h % 2 := by omega
  exact white_zone_with_two (by omega) ho
    (WZ9_B2W3_B3W3.safe h hp9 hgap)
    (WZ9_B2W3_B4W2.safe h hp9 hgap)

/-- **Odd-Height Second-Player Non-Loss Theorem**:
    On five columns and every positive odd height `h`, White does not lose from the empty board. -/
theorem odd_white_nonloss {h : Nat} (h1 : 1 ≤ h) (ho : h % 2 = 1) :
    CanAvoidLoss h .white (emptyBoard 5) := by
  by_cases e1 : h = 1
  · subst h; exact white_h1
  by_cases e3 : h = 3
  · subst h; exact white_h3
  by_cases e5 : h = 5
  · subst h; exact white_h5
  by_cases e7 : h = 7
  · subst h; exact white_h7
  by_cases e9 : h = 9
  · subst h; exact white_h9
  exact white_odd_ge_eleven (by omega) ho

#print axioms odd_white_nonloss

end C4W5Gen
