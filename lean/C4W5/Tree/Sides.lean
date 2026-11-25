import C4W5.Theory.ClaimSide
import C4W5.Tree.Chain

/-!
# Side branches T(1,b)·Wq·B4, b ≥ 3, every even height ≥ 2b+2 — no certificate

FIRST_PLAYER_THEOREM.md row 8.  The root itself satisfies criterion ZC with the fourth column claimed.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

theorem no_black_four {H : Nat} {R : Board 5} (h0 : ∀ r, stone (R 0) r ≠ some .black)
    (h4 : ∀ r, stone (R 4) r ≠ some .black)
    (hv : ∀ c r, ¬ (stone (R c) r = some .black ∧ stone (R c) (r + 1) = some .black)) :
    ¬ HasFour H R .black := by
  intro hf
  obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
  by_cases hd0 : d = 0
  · subst hd0
    have a0 := hdir 0
    have a1 := hdir 1
    simp [dxI, dyI] at a0 a1
    obtain ⟨c0, hx0, hy0, -, hs0⟩ := cellAtInt_some a0
    obtain ⟨c1, hx1, -, -, hs1⟩ := cellAtInt_some a1
    have : c1 = c0 := Fin.ext (by omega)
    subst this
    have e : (y + 1).toNat = y.toNat + 1 := by omega
    rw [e] at hs1
    exact hv c1 _ ⟨hs0, hs1⟩
  · have hdx : dxI d = 1 := by simp [dxI, hd0]
    have a0 := hdir 0
    have a3 := hdir 3
    rw [hdx] at a0 a3
    obtain ⟨c0, hx0, -, -, hs0⟩ := cellAtInt_some a0
    obtain ⟨c3, hx3, -, -, hs3⟩ := cellAtInt_some a3
    have e0 : ((0 : Fin 4) : Int) = 0 := rfl
    have e3 : (((3 : Fin 4) : Nat) : Int) = 3 := rfl
    have hc0 := c0.isLt
    have hc3 := c3.isLt
    by_cases hx : x = 0
    · have : c0 = 0 := Fin.ext (by simp at hx0; omega)
      subst this
      exact h0 _ hs0
    · have : c3 = 4 := Fin.ext (by simp at hx0 hx3; omega)
      subst this
      exact h4 _ hs3

theorem no_four_of_run {H : Nat} (ms : List (Fin 5))
    (h : (Pos.run H Pos.empty .black ms).isSome = true) :
    ¬ HasFour H (playList (emptyBoard 5) .black ms) .white := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨e, hw, -, -⟩ := root_of_run' hq
  rw [← e]; exact hw

/-- A board with the wall `(WB)^b` in the second column, a one-stone fourth column and short other
columns: safe once the two 8-row boards pass the finite checks. -/
theorem wall_family_safe (a c d e : List Player) (b H : Nat) (hb : 3 ≤ b) (hH : H % 2 = 0)
    (hbH : 2 * b + 2 ≤ H)
    (hla : a.length ≤ 4) (hlc : c.length ≤ 4) (hd : d.length = 1) (hle : e.length ≤ 4)
    (ha : ∀ r : Fin 4, stone a r ≠ some .black) (he : ∀ r : Fin 4, stone e r ≠ some .black)
    (h2 : ∀ l ∈ [a, c, d, e], ∀ r : Fin 4,
      ¬ (stone l r = some .black ∧ stone l (r + 1) = some .black))
    (hodd : (a.length + c.length + e.length) % 2 = 0)
    (hnt : ∀ l ∈ [a, c, d, e], ¬ (3 ≤ l.length ∧ stone l (l.length - 1) = some .white ∧
      stone l (l.length - 2) = some .white ∧ stone l (l.length - 3) = some .white))
    (hw3 : ¬ HasFour 8 (ofCols a (wb 3) c d e) .white)
    (hw4 : ¬ HasFour 8 (ofCols a (wb 4) c d e) .white)
    (hd3 : DeadK8 (ofCols a (wb 3) c d e) 3 1) (hd4 : DeadK8 (ofCols a (wb 4) c d e) 3 1) :
    Safe H (ofCols a (wb b) c d e) := by
  -- the bottom eight rows
  have hK : ¬ HasFour 8 (trunc 8 (ofCols a (wb b) c d e)) .white ∧
      DeadK8 (trunc 8 (ofCols a (wb b) c d e)) 3 1 := by
    by_cases hb3 : b = 3
    · subst hb3
      have : trunc 8 (ofCols a (wb 3) c d e) = ofCols a (wb 3) c d e := by
        funext i
        obtain rfl | rfl | rfl | rfl | rfl := fin5_cases i <;>
          simp only [trunc, ofCols_0, ofCols_1, ofCols_2, ofCols_3, ofCols_4]
        · apply take_short; omega
        · apply take_short; rw [wb_length]; omega
        · apply take_short; omega
        · apply take_short; omega
        · apply take_short; omega
      rw [this]; exact ⟨hw3, hd3⟩
    · have : trunc 8 (ofCols a (wb b) c d e) = ofCols a (wb 4) c d e := by
        funext i
        obtain rfl | rfl | rfl | rfl | rfl := fin5_cases i <;>
          simp only [trunc, ofCols_0, ofCols_1, ofCols_2, ofCols_3, ofCols_4]
        · apply take_short; omega
        · exact take8_wb b (by omega)
        · apply take_short; omega
        · apply take_short; omega
        · apply take_short; omega
      rw [this]; exact ⟨hw4, hd4⟩
  obtain ⟨hwK, hdK⟩ := hK
  have short : ∀ (l : List Player), l.length ≤ 4 → (∀ r : Fin 4, stone l r ≠ some .black) →
      ∀ r, stone l r ≠ some .black := by
    intro l hl h r
    by_cases hr : r < 4
    · exact h ⟨r, hr⟩
    · rw [stone_none l r (by omega)]; simp
  have pair : ∀ l ∈ [a, c, d, e], l.length ≤ 4 →
      ∀ r, ¬ (stone l r = some .black ∧ stone l (r + 1) = some .black) := by
    intro l hl hlen r
    by_cases hr : r < 4
    · exact h2 l hl ⟨r, hr⟩
    · rw [stone_none l r (by omega)]; simp
  have hE : DiscE 8 (ofCols a (wb b) c d e) := by
    intro x r hx
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x
    · have := stone_bound _ _ _ hx.1; simp only [ofCols_0] at this; omega
    · obtain ⟨h1, h2⟩ := hx
      simp only [ofCols_1] at h1 h2
      rcases h2 with rfl | h2
      · omega
      · have := wb_white h1; have := wb_white h2; omega
    · have := stone_bound _ _ _ hx.1; simp only [ofCols_2] at this; omega
    · have := stone_bound _ _ _ hx.1; simp only [ofCols_3] at this; omega
    · have := stone_bound _ _ _ hx.1; simp only [ofCols_4] at this; omega
  have hT : ∀ x, TCol 8 H (ofCols a (wb b) c d e) x := by
    intro x hlt htop
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x
    · simp only [ofCols_0]; omega
    · simp only [ofCols_1, wb_length] at htop
      rcases htop with h | h
      · omega
      · have := wb_white h; omega
    · simp only [ofCols_2]; omega
    · simp only [ofCols_3]; omega
    · simp only [ofCols_4]; omega
  have hv : Valid H (ofCols a (wb b) c d e) := by
    intro x
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x <;>
      simp only [ofCols_0, ofCols_1, ofCols_2, ofCols_3, ofCols_4, wb_length] <;> omega
  have htm : toMove (ofCols a (wb b) c d e) = .white := by
    apply toMove_of_odd
    rw [totalStones_ofCols, wb_length]; omega
  have hnb : ¬ HasFour H (ofCols a (wb b) c d e) .black := by
    apply no_black_four
    · exact short a hla ha
    · exact short e hle he
    · intro x r
      obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x
      · exact pair a (by simp) hla r
      · rintro ⟨h1, h2⟩
        have := wb_black h1; have := wb_black h2; omega
      · exact pair c (by simp) hlc r
      · exact pair d (by simp) (by omega) r
      · exact pair e (by simp) hle r
  have hnw : ¬ HasFour H (ofCols a (wb b) c d e) .white :=
    fun hf => hwK (whiteFour_low (by omega) hE hnb hf)
  have hlen3 : (ofCols a (wb b) c d e 3).length = 1 := hd
  apply claim_safe hH 3 htm hnw hnb hv (by rw [hlen3]; omega)
  · intro x hlt ht
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x
    · exact hnt a (by simp) ht
    · obtain ⟨-, h1, -, -⟩ := ht
      simp only [ofCols_1, wb_length] at h1
      have := wb_white h1; omega
    · exact hnt c (by simp) ht
    · exact hnt d (by simp) ht
    · exact hnt e (by simp) ht
  · rw [hlen3]
    exact dead_of_trunc (by omega) hE hT (fun x r hr hcell => hdK x ⟨r, by omega⟩ hcell)

/-- **T(1,b)·W1·B4**, b ≥ 3. -/
theorem side_first (b H : Nat) (hb : 3 ≤ b) (hH : H % 2 = 0) (hbH : 2 * b + 2 ≤ H) :
    Safe H (Side b 0) := by
  have e : Side b 0 = ofCols [.white] (wb b) centre [.black] [] := by
    simp [Side, T, play_ofCols_0, play_ofCols_3]
  rw [e]
  apply wall_family_safe _ _ _ _ b H hb hH hbH <;> try (simp [centre]; done)
  · decide
  · decide
  · decide
  · decide
  · have e3 : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 3] =
        ofCols [.white] (wb 3) centre [.black] [] := by
      simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2, play_ofCols_3,
        centre, wb, opponent]
    rw [← e3]; exact no_four_of_run _ (by decide)
  · have e4 : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3] =
        ofCols [.white] (wb 4) centre [.black] [] := by
      simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2, play_ofCols_3,
        centre, wb, opponent]
    rw [← e4]; exact no_four_of_run _ (by decide)
  · decide
  · decide

/-- **T(1,b)·W5·B4**, b ≥ 3. -/
theorem side_fifth (b H : Nat) (hb : 3 ≤ b) (hH : H % 2 = 0) (hbH : 2 * b + 2 ≤ H) :
    Safe H (Side b 4) := by
  have e : Side b 4 = ofCols [] (wb b) [.black, .white, .black] [.black] [.white] := by
    simp [Side, T, play_ofCols_4, play_ofCols_3, centre]
  rw [e]
  apply wall_family_safe _ _ _ _ b H hb hH hbH <;> try (simp; done)
  · decide
  · decide
  · decide
  · decide
  · have e3 : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3] =
        ofCols [] (wb 3) [.black, .white, .black] [.black] [.white] := by
      simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2, play_ofCols_3,
        play_ofCols_4, centre, wb, opponent]
    rw [← e3]; exact no_four_of_run _ (by decide)
  · have e4 : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3] =
        ofCols [] (wb 4) [.black, .white, .black] [.black] [.white] := by
      simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2, play_ofCols_3,
        play_ofCols_4, centre, wb, opponent]
    rw [← e4]; exact no_four_of_run _ (by decide)
  · decide
  · decide

/-- **T(1,b)·W3·B4**, b ≥ 3. -/
theorem side_third (b H : Nat) (hb : 3 ≤ b) (hH : H % 2 = 0) (hbH : 2 * b + 2 ≤ H) :
    Safe H (Side b 2) := by
  have e : Side b 2 = ofCols [] (wb b) [.black, .white, .black, .white] [.black] [] := by
    simp [Side, T, play_ofCols_2, play_ofCols_3, centre]
  rw [e]
  apply wall_family_safe _ _ _ _ b H hb hH hbH <;> try (simp; done)
  · decide
  · decide
  · decide
  · decide
  · have e3 : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3] =
        ofCols [] (wb 3) [.black, .white, .black, .white] [.black] [] := by
      simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2, play_ofCols_3,
        play_ofCols_4, centre, wb, opponent]
    rw [← e3]; exact no_four_of_run _ (by decide)
  · have e4 : playList (emptyBoard 5) .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3] =
        ofCols [] (wb 4) [.black, .white, .black, .white] [.black] [] := by
      simp [playList, emptyBoard_eq, play_ofCols_0, play_ofCols_1, play_ofCols_2, play_ofCols_3,
        play_ofCols_4, centre, wb, opponent]
    rw [← e4]; exact no_four_of_run _ (by decide)
  · decide
  · decide

#print axioms side_first
#print axioms side_fifth
#print axioms side_third

end C4W5
