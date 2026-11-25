import C4W5.Tree.StretchRoots
import C4W5.Tree.Sides
import C4W5.Cert.StretchTree
/-!
# G(3) and G(b ≥ 5) from stretch-game certificates (the certificates are supplied in `Tree/GAll.lean`)
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

theorem toMove_G (b : Nat) : toMove (G b) = .white := by
  apply toMove_of_odd
  simp [G, totalStones_ofCols, centre]; omega

theorem G3_play : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1] = G 3 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]
theorem G5_play : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1] = G 5 := by
  simp [playList, emptyBoard_eq, play_ofCols_1, play_ofCols_2, play_ofCols_3, G, centre, wb, opponent]

/-- From a stretch relation to a root held by a checked tree. -/
theorem safe_of_root (t : CTree) (ok : t.sallOK 2 t.smemB = true) {h : Nat} {q : Pos}
    (root : t.smemB h q = true) {A : Board 5} (hq : q.toBoard = A) (ms : List (Fin 5))
    (hms : playList (emptyBoard 5) .black ms = A)
    (hrun : (Pos.run h Pos.empty .black ms).isSome = true)
    {H : Nat} {R : Board 5} (htm : toMove R = .white) (hs : SEq 2 h A H R) : Safe H R := by
  have hnw : ¬ HasFour H R .white := by
    intro hf
    have := (hs.hasFour_iff (by omega) .white).mpr hf
    rw [← hms] at this
    exact no_four_of_run _ hrun this
  rw [← hq] at hs
  exact stretch_safe_of_tree (by omega) t ok root htm hnw hs

def g3p : Pos := ⟨0,106,5,0,0,0,7,3,1,0⟩
def g5p : Pos := ⟨0,1706,5,0,0,0,11,3,1,0⟩

theorem g3_of_tree (t : CTree) (ok : t.sallOK 2 t.smemB = true) (root : t.smemB 14 g3p = true)
    (m : Nat) (hm : 7 ≤ m) : Safe (2 * m) (G 3) := by
  have hs := seq_G3 (m - 7)
  have e : 14 + 2 * (m - 7) = 2 * m := by omega
  rw [e] at hs
  exact safe_of_root t ok root (by funext c; obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl)
    _ G3_play (by decide) (toMove_G 3) hs

end C4W5
