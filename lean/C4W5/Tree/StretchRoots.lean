import C4W5.Theory.ClaimSide
import C4W5.Theory.StretchGame
import C4W5.Tree.Chain

/-!
# The parametric families as stretches of finitely many roots

* stretching above all columns only raises the board (`seq_top`);
* stretching inside the wall `(WB)^n` at level 6 lengthens the wall by one pair (`wall_step`).
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

theorem clearCut_of {D h r : Nat} {R : Board 5} (hr : D < r) (hh : r + D < h)
    (hcol : ∀ c, ((R c).length + D < r ∨ r + D < (R c).length) ∧
      ∀ ℓ, IsDefect (R c) ℓ → ℓ + D < r ∨ r + D < ℓ) : ClearCut D h R r := by
  refine ⟨by omega, ?_⟩
  rintro ℓ (rfl | rfl | ⟨c, rfl⟩ | ⟨c, hd⟩)
  · omega
  · omega
  · exact (hcol c).1
  · exact (hcol c).2 ℓ hd

/-- A cut above every column. -/
theorem clearCut_above {D h r : Nat} {R : Board 5} (hr : D < r) (hh : r + D < h)
    (hcol : ∀ c, (R c).length + D < r) : ClearCut D h R r :=
  clearCut_of hr hh fun c => ⟨Or.inl (hcol c), fun ℓ hd => Or.inl (by have := hd.2.1; have := hcol c; omega)⟩

theorem stretch_above {r : Nat} {R : Board 5} (hcol : ∀ c, (R c).length ≤ r) : stretch R r = R := by
  funext c
  simp only [stretch, colStretch]
  rw [if_neg (by have := hcol c; omega)]

/-- Raising the board: the same position on every height `h + 2k`. -/
theorem seq_top {D r : Nat} {R : Board 5} (hr : D < r) (hcol : ∀ c, (R c).length + D < r) :
    ∀ (k h : Nat), r + D < h → SEq D h R (h + 2 * k) R
  | 0, h, _ => SEq.refl _ _
  | k + 1, h, hh => by
    have hc : ClearCut D h R r := clearCut_above hr hh hcol
    refine SEq.step r hc ?_
    rw [stretch_above (fun c => by have := hcol c; omega)]
    have e : h + 2 * (k + 1) = h + 2 + 2 * k := by omega
    rw [e]
    exact seq_top hr hcol k (h + 2) (by omega)

/-! ## The wall -/

theorem isDefect_wall {n : Nat} {t : List Player} {ℓ : Nat} (hd : IsDefect (wb n ++ t) ℓ) :
    2 * n ≤ ℓ := by
  by_contra hlt
  obtain ⟨h1, -, h3⟩ := hd
  have a1 : ℓ - 1 < (wb n).length := by rw [wb_length]; omega
  have a2 : ℓ < (wb n).length := by rw [wb_length]; omega
  have b1 : ℓ - 1 < 2 * n := by omega
  have b2 : ℓ < 2 * n := by omega
  rw [stone_app, if_pos a1, stone_app, if_pos a2, stone_wb, if_pos b1, stone_wb, if_pos b2] at h3
  have := Option.some.inj h3
  by_cases he : ℓ % 2 = 0
  · have he' : ¬ (ℓ - 1) % 2 = 0 := by omega
    rw [if_neg he', if_pos he] at this; cases this
  · have he' : (ℓ - 1) % 2 = 0 := by omega
    rw [if_pos he', if_neg he] at this; cases this

theorem isDefect_wall_white {n ℓ : Nat} : ¬ IsDefect (wb n ++ [.white]) ℓ := by
  intro hd
  have h2 := isDefect_wall hd
  obtain ⟨h1, hlen, h3⟩ := hd
  simp only [List.length_append, wb_length, List.length_cons, List.length_nil] at hlen
  have e : ℓ = 2 * n := by omega
  subst e
  have a1 : 2 * n - 1 < (wb n).length := by rw [wb_length]; omega
  have a2 : ¬ 2 * n < (wb n).length := by rw [wb_length]; omega
  have b1 : 2 * n - 1 < 2 * n := by omega
  have b3 : ¬ (2 * n - 1) % 2 = 0 := by omega
  rw [stone_app, if_pos a1, stone_app, if_neg a2, stone_wb, if_pos b1, if_neg b3, wb_length] at h3
  simp [stone] at h3

theorem colStretch_wall (k : Nat) (t : List Player) (hk : 1 ≤ k) :
    colStretch (wb (k + 3) ++ t) 6 = wb (k + 4) ++ t := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [colStretch, wb, stone]

/-- One wall step at level 6 (`D = 2`). -/
theorem wall_step (a c d e t : List Player) (k h : Nat) (hk : 1 ≤ k)
    (ha : a.length ≤ 3) (hc : c.length ≤ 3) (hd : d.length ≤ 3) (he : e.length ≤ 3)
    (hlen : 8 < 2 * (k + 3) + t.length) (hdef : ∀ ℓ, IsDefect (wb (k + 3) ++ t) ℓ → 8 < ℓ)
    (h8 : 8 < h) :
    ClearCut 2 h (ofCols a (wb (k + 3) ++ t) c d e) 6 ∧
      stretch (ofCols a (wb (k + 3) ++ t) c d e) 6 = ofCols a (wb (k + 4) ++ t) c d e := by
  constructor
  · apply clearCut_of (by omega) (by omega)
    intro x
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x
    · exact ⟨Or.inl (by simp only [ofCols_0]; omega), fun ℓ hl => Or.inl (by
        have := hl.2.1; simp only [ofCols_0] at this; omega)⟩
    · refine ⟨Or.inr (by simp only [ofCols_1, List.length_append, wb_length]; omega), fun ℓ hl => ?_⟩
      have := hdef ℓ hl; omega
    · exact ⟨Or.inl (by simp only [ofCols_2]; omega), fun ℓ hl => Or.inl (by
        have := hl.2.1; simp only [ofCols_2] at this; omega)⟩
    · exact ⟨Or.inl (by simp only [ofCols_3]; omega), fun ℓ hl => Or.inl (by
        have := hl.2.1; simp only [ofCols_3] at this; omega)⟩
    · exact ⟨Or.inl (by simp only [ofCols_4]; omega), fun ℓ hl => Or.inl (by
        have := hl.2.1; simp only [ofCols_4] at this; omega)⟩
  · funext x
    have short : ∀ l : List Player, l.length ≤ 3 → colStretch l 6 = l := by
      intro l hl; simp only [colStretch]; rw [if_neg (by omega)]
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x
    · exact short a ha
    · exact colStretch_wall k t hk
    · exact short c hc
    · exact short d hd
    · exact short e he

/-- Top(m) is a stretch of Top(5). -/
theorem seq_Top : ∀ m : Nat, 5 ≤ m → SEq 2 10 (Top 5) (2 * m) (Top m)
  | 5, _ => SEq.refl _ _
  | m + 6, _ => by
    have ih := seq_Top (m + 5) (by omega)
    have hs := wall_step [] centre [.black] [] [.white] (m + 1) (2 * (m + 5)) (by omega)
      (by simp) (by simp [centre]) (by simp) (by simp)
      (by simp only [List.length_cons, List.length_nil]; omega)
      (fun ℓ hl => absurd hl isDefect_wall_white) (by omega)
    have e1 : Top (m + 5) = ofCols [] (wb (m + 1 + 3) ++ [.white]) centre [.black] [] := by
      simp [Top]
    have e2 : Top (m + 6) = ofCols [] (wb (m + 1 + 4) ++ [.white]) centre [.black] [] := by
      simp [Top]
    have := SEq.single hs.1
    rw [hs.2, ← e1, ← e2] at this
    exact ih.trans this

/-- G(b) on height `2b + g` is a stretch of G(5) on height `10 + g`. -/
theorem seq_G_wall (g : Nat) (hg : 2 ≤ g) : ∀ b : Nat, 5 ≤ b → SEq 2 (10 + g) (G 5) (2 * b + g) (G b)
  | 5, _ => SEq.refl _ _
  | b + 6, _ => by
    have ih := seq_G_wall g hg (b + 5) (by omega)
    have hs := wall_step [] centre [.white] [] [.black] (b + 2) (2 * (b + 5) + g) (by omega)
      (by simp) (by simp [centre]) (by simp) (by simp)
      (by simp only [List.length_cons, List.length_nil]; omega)
      (fun ℓ hl => by have := isDefect_wall hl; omega) (by omega)
    have e1 : G (b + 5) = ofCols [] (wb (b + 2 + 3) ++ [.black]) centre [.white] [] := by
      simp [G]
    have e2 : G (b + 6) = ofCols [] (wb (b + 2 + 4) ++ [.black]) centre [.white] [] := by
      simp [G]
    have := SEq.single hs.1
    rw [hs.2, ← e1, ← e2] at this
    have e3 : 2 * (b + 5) + g + 2 = 2 * (b + 6) + g := by omega
    rw [e3] at this
    exact ih.trans this

theorem G_len (b : Nat) (hb : 1 ≤ b) (c : Fin 5) : (G b c).length ≤ 2 * b + 1 := by
  obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c
  all_goals (simp [G, centre]; try omega)

/-- G(b) on a high board: raise from height `2b + 8`. -/
theorem seq_G_top (b k : Nat) (hb : 1 ≤ b) : SEq 2 (2 * b + 8) (G b) (2 * b + 8 + 2 * k) (G b) :=
  seq_top (r := 2 * b + 4) (by omega) (fun c => by have := G_len b hb c; omega) k _ (by omega)

/-- G(3) on every even height ≥ 14. -/
theorem seq_G3 (k : Nat) : SEq 2 14 (G 3) (14 + 2 * k) (G 3) :=
  seq_top (r := 10) (by omega) (fun c => by have := G_len 3 (by omega) c; omega) k _ (by omega)

end C4W5
