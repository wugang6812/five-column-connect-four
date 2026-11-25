import C4W5.Cert.Pos

/-!
# Detecting fours with bit masks

`Pos.hasFourF p pl`: does colour `pl` have a four anywhere on the board?  Exact (`hasFourF_iff`).
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

def ptX (d X j : Nat) : Nat := if d = 0 then X else X + j
def ptY (d Y j : Nat) : Nat := if d = 0 then Y + j else if d = 1 then Y else if d = 2 then Y + j else Y + 3 - j
def dxI (d : Nat) : Int := if d = 0 then 0 else 1
def dyI (d : Nat) : Int := if d = 0 then 1 else if d = 1 then 0 else if d = 2 then 1 else -1

theorem hasFour_of_dir {h : Nat} {b : Board 5} {p : Player} {x y : Int} (d : Nat) (hd : d < 4)
    (hf : HasFourDir h b p x y (dxI d) (dyI d)) : HasFour h b p := by
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hd' with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨x, y, hf⟩
  · exact Or.inr (Or.inl ⟨x, y, hf⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, hf⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, hf⟩))

theorem exists_dir {h : Nat} {b : Board 5} {p : Player} (hf : HasFour h b p) :
    ∃ d, d < 4 ∧ ∃ x y, HasFourDir h b p x y (dxI d) (dyI d) := by
  rcases hf with ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩
  · exact ⟨0, by omega, x, y, hf⟩
  · exact ⟨1, by omega, x, y, hf⟩
  · exact ⟨2, by omega, x, y, hf⟩
  · exact ⟨3, by omega, x, y, hf⟩

def and4 (a b c d : Nat) : Bool := (a &&& b &&& c &&& d) != 0

theorem and4_iff (a b c d : Nat) : and4 a b c d = true ↔
    ∃ i, a.testBit i = true ∧ b.testBit i = true ∧ c.testBit i = true ∧ d.testBit i = true := by
  unfold and4
  constructor
  · intro h
    have hne : a &&& b &&& c &&& d ≠ 0 := by simpa using h
    by_contra hcon
    apply hne
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_contra hb
    apply hcon
    have : (a &&& b &&& c &&& d).testBit i = true := by
      cases hh : (a &&& b &&& c &&& d).testBit i
      · exact absurd hh hb
      · rfl
    simp only [Nat.testBit_and, Bool.and_eq_true] at this
    exact ⟨i, this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · rintro ⟨i, ha, hb, hc, hd⟩
    have : (a &&& b &&& c &&& d).testBit i = true := by
      simp only [Nat.testBit_and, Bool.and_eq_true]; exact ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
    have hne : a &&& b &&& c &&& d ≠ 0 := by
      intro h0; rw [h0, Nat.zero_testBit] at this; exact Bool.noConfusion this
    simpa using hne

/-- Line test for direction `d` starting in column `x`. -/
def lineB (p : Pos) (pl : Player) (d x : Nat) : Bool :=
  match d with
  | 0 => and4 (p.mask pl x) (p.mask pl x >>> 1) (p.mask pl x >>> 2) (p.mask pl x >>> 3)
  | 1 => and4 (p.mask pl x) (p.mask pl (x + 1)) (p.mask pl (x + 2)) (p.mask pl (x + 3))
  | 2 => and4 (p.mask pl x) (p.mask pl (x + 1) >>> 1) (p.mask pl (x + 2) >>> 2) (p.mask pl (x + 3) >>> 3)
  | _ => and4 (p.mask pl x >>> 3) (p.mask pl (x + 1) >>> 2) (p.mask pl (x + 2) >>> 1) (p.mask pl (x + 3))

theorem lineB_iff (p : Pos) (pl : Player) (d x : Nat) (hd : d < 4) :
    lineB p pl d x = true ↔
      ∃ Y, ∀ j, j < 4 → (p.mask pl (ptX d x j)).testBit (ptY d Y j) = true := by
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hd' with rfl | rfl | rfl | rfl <;>
    (simp only [lineB]; rw [and4_iff]; (try simp only [Nat.testBit_shiftRight]); constructor)
  all_goals first
    | (rintro ⟨i, h0, h1, h2, h3⟩
       refine ⟨i, fun j hj => ?_⟩
       have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
       rcases hj' with rfl | rfl | rfl | rfl <;> simp_all [ptX, ptY, Nat.add_comm])
    | (rintro ⟨Y, hY⟩
       have h0 := hY 0 (by omega)
       have h1 := hY 1 (by omega)
       have h2 := hY 2 (by omega)
       have h3 := hY 3 (by omega)
       refine ⟨Y, ?_⟩
       simp_all [ptX, ptY, Nat.add_comm])

def Pos.hasFourF (p : Pos) (pl : Player) : Bool :=
  [0, 1, 2, 3, 4].any (lineB p pl 0) || [0, 1].any (lineB p pl 1) || [0, 1].any (lineB p pl 2) ||
    [0, 1].any (lineB p pl 3)

theorem hasFourF_cases {p : Pos} {pl : Player} :
    p.hasFourF pl = true ↔ ∃ d x, d < 4 ∧ ptX d x 3 ≤ 4 ∧ lineB p pl d x = true := by
  unfold Pos.hasFourF
  simp only [Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (((⟨x, hx, hl⟩ | ⟨x, hx, hl⟩) | ⟨x, hx, hl⟩) | ⟨x, hx, hl⟩)
    · exact ⟨0, x, by omega, by simp at hx; simp [ptX]; omega, hl⟩
    · exact ⟨1, x, by omega, by simp at hx; simp [ptX]; omega, hl⟩
    · exact ⟨2, x, by omega, by simp at hx; simp [ptX]; omega, hl⟩
    · exact ⟨3, x, by omega, by simp at hx; simp [ptX]; omega, hl⟩
  · rintro ⟨d, x, hd, hx, hl⟩
    have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hd' with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl ⟨x, by simp [ptX] at hx; simp; omega, hl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨x, by simp [ptX] at hx; simp; omega, hl⟩))
    · exact Or.inl (Or.inr ⟨x, by simp [ptX] at hx; simp; omega, hl⟩)
    · exact Or.inr ⟨x, by simp [ptX] at hx; simp; omega, hl⟩

/-- Integer start row of the line whose lowest-indexed bit row is `Y`. -/
def y0N (d Y : Nat) : Int := if d = 3 then (Y : Int) + 3 else (Y : Int)

theorem pt_bound {d X j : Nat} (hX : ptX d X 3 ≤ 4) (hj : j < 4) : ptX d X j < 5 := by
  unfold ptX at *; split at hX <;> simp_all <;> omega

/-- **Exactness of the mask test.** -/
theorem hasFourF_iff {H : Nat} {p : Pos} (hw : p.WF H) (pl : Player) :
    p.hasFourF pl = true ↔ HasFour H p.toBoard pl := by
  rw [hasFourF_cases]
  constructor
  · rintro ⟨d, x, hd, hx, hl⟩
    obtain ⟨Y, hY⟩ := (lineB_iff p pl d x hd).mp hl
    apply hasFour_of_dir d hd (x := (x : Int)) (y := y0N d Y)
    intro i
    have hi := i.isLt
    have hcol := pt_bound hx hi
    have e1 : (x : Int) + (i.val : Int) * dxI d = ((⟨ptX d x i.val, hcol⟩ : Fin 5).val : Int) := by
      have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
      rcases hd' with rfl | rfl | rfl | rfl <;> simp [ptX, dxI]
    have e2 : y0N d Y + (i.val : Int) * dyI d = ((ptY d Y i.val : Nat) : Int) := by
      have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
      rcases hd' with rfl | rfl | rfl | rfl <;> simp [ptY, dyI, y0N] <;> omega
    rw [e1, e2, cell_iff hw]
    exact ⟨by omega, by simpa using hY i.val hi⟩
  · intro hf
    obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
    -- column and row bounds from the four cells
    have hc : ∀ i : Fin 4, ∃ c : Fin 5, x + (i.val : Int) * dxI d = (c.val : Int) ∧
        0 ≤ y + (i.val : Int) * dyI d ∧
        (p.mask pl c.val).testBit (y + (i.val : Int) * dyI d).toNat = true := by
      intro i
      obtain ⟨c, hx, hy0, -, -⟩ := cellAtInt_some (hdir i)
      have := hdir i
      rw [hx, cell_iff hw] at this
      exact ⟨c, hx, this.1, this.2⟩
    obtain ⟨c0, hx0, hy0, -⟩ := hc 0
    obtain ⟨c3, hx3, hy3, -⟩ := hc 3
    have e3 : ((3 : Fin 4).val : Int) = 3 := rfl
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] at hx0 hy0
    rw [e3] at hx3 hy3
    have h0 := c0.isLt
    have h3 := c3.isLt
    refine ⟨d, c0.val, hd, ?_, ?_⟩
    · have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
      rcases hd' with rfl | rfl | rfl | rfl <;> simp [ptX, dxI] at hx3 ⊢ <;> omega
    · rw [lineB_iff p pl d c0.val hd]
      refine ⟨(if d = 3 then y - 3 else y).toNat, fun j hj => ?_⟩
      obtain ⟨c, hx, hy, hbit⟩ := hc ⟨j, hj⟩
      have ec : ptX d c0.val j = c.val := by
        have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
        rcases hd' with rfl | rfl | rfl | rfl <;> simp [ptX, dxI] at hx ⊢ <;> omega
      have er : ptY d (if d = 3 then y - 3 else y).toNat j = (y + (j : Int) * dyI d).toNat := by
        have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
        rcases hd' with rfl | rfl | rfl | rfl <;> simp [ptY, dyI] at hy hy3 ⊢ <;> omega
      rw [ec, er]; exact hbit

/-- Cells other than the new one are unchanged by a move. -/
theorem cellAtInt_play_ne {h : Nat} (b : Board 5) (c : Fin 5) (q : Player) (x y : Int)
    (hne : ¬ (x = (c.val : Int) ∧ y = ((b c).length : Int))) :
    cellAtInt h (play b c q) x y = cellAtInt h b x y := by
  unfold cellAtInt
  by_cases hx : 0 ≤ x ∧ x < ((5 : Nat) : Int)
  · rw [dif_pos hx, dif_pos hx]
    by_cases hy : 0 ≤ y ∧ y < (h : Int)
    · rw [if_pos hy, if_pos hy]
      by_cases hc : (⟨x.toNat, by omega⟩ : Fin 5) = c
      · rw [hc, play_eq, stone_append]
        have hxc : x = (c.val : Int) := by rw [← hc]; simp; omega
        have hyl : y.toNat ≠ (b c).length := by
          intro e; apply hne; exact ⟨hxc, by omega⟩
        by_cases hlt : y.toNat < (b c).length
        · rw [if_pos hlt]
        · rw [if_neg hlt, if_neg hyl, stone_none _ _ (by omega)]
      · rw [play_ne b c _ q hc]
    · rw [if_neg hy, if_neg hy]
  · rw [dif_neg hx, dif_neg hx]

/-- A move of colour `q` cannot create a four of the other colour. -/
theorem hasFour_play_other {h : Nat} {b : Board 5} {c : Fin 5} {p q : Player} (hpq : p ≠ q)
    (hnew : HasFour h (play b c q) p) : HasFour h b p := by
  obtain ⟨d, hd, x, y, hf⟩ := exists_dir hnew
  apply hasFour_of_dir d hd (x := x) (y := y)
  intro i
  have hi := hf i
  by_cases hh : x + (i : Int) * dxI d = (c.val : Int) ∧ y + (i : Int) * dyI d = ((b c).length : Int)
  · exfalso
    obtain ⟨e, hx, hy0, hyh, hs⟩ := cellAtInt_some hi
    have hec : e = c := by apply Fin.ext; omega
    rw [hec, play_eq, stone_append, if_neg (by omega), if_pos (by omega)] at hs
    exact hpq (Option.some.inj hs).symm
  · rw [← cellAtInt_play_ne b c q _ _ hh]; exact hi

end C4W5
