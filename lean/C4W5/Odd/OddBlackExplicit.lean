import C4W5.Odd.Gen.B5_B2.Main
import C4W5.Odd.Gen.B7_B2_Explicit.Main
import C4W5.Odd.Gen.BZ7_B2_Explicit.Main

/-!
# First-Player Non-Loss on All Odd Heights `5 × (2m+1)` (`OddBlackExplicit`)

Proves `odd_black_nonloss : ∀ {h : Nat}, 1 ≤ h → h % 2 = 1 → CanAvoidLoss h .black (emptyBoard 5)`
by opening uniformly in 1-based column 2 (`0`-based `1`):
- `h = 1, 3`: direct `ClaimEven` at the position after `B2`.
- `h = 5`: `B5_B2.safe`, a finite strategy certificate.
- `h = 7`: `B7_B2_Explicit.safe`, the real-board fixed-controller certificate.
- All odd `h ≥ 9`: `BZ7_B2_Explicit.safe`, lifting the same-parity `K = 7` Zone certificate.

The two explicit certificates store states, not reply bytes. The executable controller
is checked until an admitted exit; the safety proof uses Claim or the Zone tail at those
exits. This does not assert that the same controller remains fixed after every exit.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

private def rootB2 : Pos := ⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩

private theorem black_b2_h1 : SafeP 1 .black (playList (emptyBoard 5) .black [1]) :=
  safeP_of_claimEven_run [1] rootB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem black_b2_h3 : SafeP 3 .black (playList (emptyBoard 5) .black [1]) :=
  safeP_of_claimEven_run [1] rootB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem black_b2_odd {h : Nat} (h1 : 1 ≤ h) (ho : h % 2 = 1) :
    SafeP h .black (playList (emptyBoard 5) .black [1]) := by
  by_cases e1 : h = 1
  · subst h; exact black_b2_h1
  by_cases e3 : h = 3
  · subst h; exact black_b2_h3
  by_cases e5 : h = 5
  · subst h; exact B5_B2.safe
  by_cases e7 : h = 7
  · subst h; exact B7_B2_Explicit.safe
  have hgap : 7 + 2 ≤ h := by omega
  exact BZ7_B2_Explicit.safe h (by omega) hgap

/-- **Odd-Height First-Player Non-Loss Theorem**:
    On five columns and every positive odd height `h`, Black does not lose from the empty board. -/
theorem odd_black_nonloss {h : Nat} (h1 : 1 ≤ h) (ho : h % 2 = 1) :
    CanAvoidLoss h .black (emptyBoard 5) := by
  have htm : toMove (emptyBoard 5) = .black := by
    rw [emptyBoard_eq]
    exact toMove_of_evenG (by simp [totalStones_ofCols])
  have hleg : Legal h (emptyBoard 5) 1 := by
    simp [Legal, emptyBoard] <;> omega
  apply safeP_me_step htm hleg
  change SafeP h .black (playList (emptyBoard 5) .black [1])
  exact black_b2_odd h1 ho

#print axioms odd_black_nonloss

end C4W5Gen
