import C4W5.Odd.OddBlackExplicit
import C4W5.Odd.OddWhite

/-!
# Five-Column Odd-Height Connect Four Is a Draw (`C4W5.Odd.Main`)

Colab input filename: `OddMain.lean`; install as `C4W5/Odd/Main.lean`.

Combines:
- `odd_black_nonloss` (direct Claim entries, a finite H=5 strategy tree, and
  explicit-controller reachable sets with Claim/Zone exits)
- `odd_white_nonloss` (direct Claim entries, finite and Zone certificates, and reflection)

to establish `five_columns_odd_draw : ∀ {h : Nat}, 1 ≤ h → h % 2 = 1 → IsDraw h (emptyBoard 5)`
and the conditional assembly lemma `five_columns_draw_of_even`. It assumes the positive-even
result as a premise: this odd-only module neither imports nor builds the even certificate tree.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-- A height-zero board has no in-bounds cell, independently of the column words. -/
private theorem noFour_zero (b : Board 5) (p : Player) : ¬ HasFour 0 b p := by
  have noDir (x y dx dy : Int) : ¬ HasFourDir 0 b p x y dx dy := by
    intro hdir
    obtain ⟨_, _, hlo, hhi, _⟩ := cellAtInt_some (hdir (0 : Fin 4))
    omega
  intro hfour
  rcases hfour with ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩ | ⟨x, y, h⟩
  · exact noDir x y 0 1 h
  · exact noDir x y 1 0 h
  · exact noDir x y 1 1 h
  · exact noDir x y 1 (-1) h

/-- **Main Odd-Height Theorem**:
    On five columns, Gravity Connect Four `5 × h` is a game-theoretic draw from the empty board
    for every positive odd height `h = 2m + 1` (`h ≥ 1`). -/
theorem five_columns_odd_draw {h : Nat} (h1 : 1 ≤ h) (ho : h % 2 = 1) :
    IsDraw h (emptyBoard 5) :=
  ⟨odd_black_nonloss h1 ho, odd_white_nonloss h1 ho⟩

/-- Neither player has a forced win at any horizon on `5 × (2m+1)`. -/
theorem five_columns_odd_neither_player_wins {h : Nat} (h1 : 1 ≤ h) (ho : h % 2 = 1) :
    (¬ ∃ k, WinFor h Player.black k (emptyBoard 5)) ∧
    (¬ ∃ k, WinFor h Player.white k (emptyBoard 5)) :=
  draw_excludes_forced_wins (five_columns_odd_draw h1 ho)

/-- Height `0` base case: the `5 × 0` board is already full with zero stones. -/
theorem five_columns_zero_draw : IsDraw 0 (emptyBoard 5) := by
  have hnf : ∀ p : Player, ¬ HasFour 0 (emptyBoard 5) p := noFour_zero (emptyBoard 5)
  have hfull : BoardFull 0 (emptyBoard 5) := fun _ => rfl
  have hsafe : ∀ p : Player, CanAvoidLoss 0 p (emptyBoard 5) := by
    intro p k
    cases k with
    | zero => exact hnf (opponent p)
    | succ _ => exact ⟨hnf (opponent p), Or.inr (Or.inl hfull)⟩
  exact ⟨hsafe .black, hsafe .white⟩

/-- **All-Heights Unification Combinator**:
    Combines `h = 0` (`five_columns_zero_draw`), positive odd heights (`five_columns_odd_draw`),
    and positive even heights (`heven`) to close `IsDraw h (emptyBoard 5)` for ALL `h : Nat`. -/
theorem five_columns_draw_of_even
    (heven : ∀ {h : Nat}, 2 ≤ h → h % 2 = 0 → IsDraw h (emptyBoard 5))
    (h : Nat) : IsDraw h (emptyBoard 5) := by
  by_cases h0 : h = 0
  · subst h0; exact five_columns_zero_draw
  · by_cases he : h % 2 = 0
    · exact heven (h := h) (by omega) he
    · exact five_columns_odd_draw (by omega) (by omega)

#print axioms odd_black_nonloss
#print axioms odd_white_nonloss
#print axioms five_columns_odd_draw
#print axioms five_columns_odd_neither_player_wins
#print axioms five_columns_zero_draw
#print axioms five_columns_draw_of_even

end C4W5Gen
