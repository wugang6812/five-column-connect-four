import C4W5.Base.Mirror

/-!
# The chain T(1,b): assembling the proof tree (FIRST_PLAYER_THEOREM.md §2, rows 3–13)

`ChainCells m` lists, for the height `2 * m`, the cells whose proofs come from elsewhere
(zone theorem, stretch theorem, Top theorem, certificates).  From them: `T 0` (= 333) is safe.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

theorem fin5_cases (c : Fin 5) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  revert c; decide

theorem toMove_of_odd {b : Board 5} (ho : totalStones b % 2 = 1) : toMove b = .white := by
  unfold toMove; rw [if_neg (by omega)]

theorem toMove_of_even {b : Board 5} (he : totalStones b % 2 = 0) : toMove b = .black := by
  unfold toMove; rw [if_pos he]

theorem toMove_T (b : Nat) : toMove (T b) = .white := by
  apply toMove_of_odd
  simp [T, totalStones_ofCols, centre]

theorem mirror_ofCols (a b c d e : List Player) : mirror (ofCols a b c d e) = ofCols e d c b a := by
  funext i
  obtain rfl | rfl | rfl | rfl | rfl := fin5_cases i <;> rfl

/-- The cells below the chain at height `2 * m`. -/
structure ChainCells (m : Nat) : Prop where
  /-- T(1,b)·W1·B4 and T(1,b)·W5·B4, b ≥ 1. -/
  side : ∀ (b : Nat) (q : Fin 5), 1 ≤ b → b + 1 ≤ m → (q = 0 ∨ q = 4) → Safe (2 * m) (Side b q)
  /-- T(1,b)·W3·B4, b ≥ 3. -/
  side3 : ∀ b : Nat, 3 ≤ b → b + 1 ≤ m → Safe (2 * m) (Side b 2)
  /-- T(1,1)·W3·B2. -/
  s113 : Safe (2 * m) (play (play (T 1) 2 .white) 1 .black)
  /-- T(1,2)·W3·B5. -/
  s123 : Safe (2 * m) (play (play (T 2) 2 .white) 4 .black)
  /-- G(b) = T(1,b)·W4·B2, b ≥ 1. -/
  g : ∀ b : Nat, 1 ≤ b → b + 1 ≤ m → Safe (2 * m) (G b)
  /-- Top = T(1,m-1)·W2·B4. -/
  top : Safe (2 * m) (Top m)
  /-- 333·W1·B1. -/
  c33311 : Safe (2 * m) (play (play (T 0) 0 .white) 0 .black)
  /-- U = 333·W3·B2. -/
  cU : Safe (2 * m) (play (play (T 0) 2 .white) 1 .black)

theorem T_cover (b : Nat) : play (play (T b) 1 .white) 1 .black = T (b + 1) := by
  simp only [T, play_ofCols_1, wb_succ, List.append_assoc, List.singleton_append]

theorem T_w4_b2 (b : Nat) : play (play (T b) 3 .white) 1 .black = G b := by
  simp only [T, G, play_ofCols_3, play_ofCols_1, List.nil_append]

theorem T_w2_b4 (m : Nat) : play (play (T (m - 1)) 1 .white) 3 .black = Top m := by
  simp only [T, Top, play_ofCols_3, play_ofCols_1, List.nil_append]

/-- T(1,b) is safe for 1 ≤ b ≤ m − 1, by induction from the top of the wall downwards. -/
theorem T_safe_pos {m : Nat} (hm : 3 ≤ m) (C : ChainCells m) :
    ∀ n b : Nat, b + n + 1 = m → 1 ≤ b → Safe (2 * m) (T b) := by
  intro n
  induction n with
  | zero =>
    intro b hb h1
    have hbm : b = m - 1 := by omega
    apply safe_white_reply (toMove_T b) ⟨0, by simp [Legal, T]; omega⟩
    intro c hc
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c
    · exact ⟨3, by simp [Legal, T, play_ofCols_0]; omega, C.side b 0 h1 (by omega) (Or.inl rfl)⟩
    · refine ⟨3, by simp [Legal, T, play_ofCols_1]; omega, ?_⟩
      rw [hbm, T_w2_b4]; exact C.top
    · by_cases hb2 : b = 2
      · subst hb2
        exact ⟨4, by simp [Legal, T, play_ofCols_2]; omega, C.s123⟩
      · exact ⟨3, by simp [Legal, T, play_ofCols_2]; omega, C.side3 b (by omega) (by omega)⟩
    · refine ⟨1, by simp [Legal, T, play_ofCols_3]; omega, ?_⟩
      rw [T_w4_b2]; exact C.g b h1 (by omega)
    · exact ⟨3, by simp [Legal, T, play_ofCols_4]; omega, C.side b 4 h1 (by omega) (Or.inr rfl)⟩
  | succ n ih =>
    intro b hb h1
    apply safe_white_reply (toMove_T b) ⟨0, by simp [Legal, T]; omega⟩
    intro c hc
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c
    · exact ⟨3, by simp [Legal, T, play_ofCols_0]; omega, C.side b 0 h1 (by omega) (Or.inl rfl)⟩
    · refine ⟨1, by simp [Legal, T, play_ofCols_1]; omega, ?_⟩
      rw [T_cover]; exact ih (b + 1) (by omega) (by omega)
    · by_cases hb1 : b = 1
      · subst hb1
        exact ⟨1, by simp [Legal, T, play_ofCols_2, wb]; omega, C.s113⟩
      · by_cases hb2 : b = 2
        · subst hb2
          exact ⟨4, by simp [Legal, T, play_ofCols_2]; omega, C.s123⟩
        · exact ⟨3, by simp [Legal, T, play_ofCols_2]; omega, C.side3 b (by omega) (by omega)⟩
    · refine ⟨1, by simp [Legal, T, play_ofCols_3]; omega, ?_⟩
      rw [T_w4_b2]; exact C.g b h1 (by omega)
    · exact ⟨3, by simp [Legal, T, play_ofCols_4]; omega, C.side b 4 h1 (by omega) (Or.inr rfl)⟩

theorem T1_safe {m : Nat} (hm : 3 ≤ m) (C : ChainCells m) : Safe (2 * m) (T 1) :=
  T_safe_pos hm C (m - 2) 1 (by omega) (by omega)

/-- **333 is safe** at height `2 * m`, given the cells. -/
theorem T0_safe {m : Nat} (hm : 3 ≤ m) (C : ChainCells m) : Safe (2 * m) (T 0) := by
  apply safe_white_reply (toMove_T 0) ⟨0, by simp [Legal, T]; omega⟩
  intro c hc
  obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c
  · exact ⟨0, by simp [Legal, T, play_ofCols_0]; omega, C.c33311⟩
  · refine ⟨1, by simp [Legal, T, play_ofCols_1, wb]; omega, ?_⟩
    rw [T_cover]; exact T1_safe hm C
  · exact ⟨1, by simp [Legal, T, play_ofCols_2, wb]; omega, C.cU⟩
  · refine ⟨3, by simp [Legal, T, play_ofCols_3]; omega, ?_⟩
    have e : play (play (T 0) 3 .white) 3 .black = mirror (T 1) := by
      simp only [T, play_ofCols_3, mirror_ofCols, wb, List.nil_append, List.cons_append]
    rw [e]; exact safe_mirror (T1_safe hm C)
  · refine ⟨4, by simp [Legal, T, play_ofCols_4]; omega, ?_⟩
    have e : play (play (T 0) 4 .white) 4 .black = mirror (play (play (T 0) 0 .white) 0 .black) := by
      simp only [T, play_ofCols_4, play_ofCols_0, mirror_ofCols, wb, List.nil_append, List.cons_append]
    rw [e]; exact safe_mirror C.c33311

#print axioms T0_safe

end C4W5
