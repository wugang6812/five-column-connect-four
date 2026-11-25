import C4W5.Base.Safety

/-!
# Stretch theorem (STRETCH_THEOREM.md)

Levels `0..h`; level `ℓ` is the boundary between rows `ℓ` and `ℓ+1` (1-based rows), i.e. between list
indices `ℓ-1` and `ℓ`.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

variable {w : Nat}

set_option linter.deprecated false

/-! ## List lemmas about `stone` -/

theorem stone_some_of_lt (l : List Player) (n : Nat) (hn : n < l.length) :
    ∃ p, stone l n = some p := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a l ih =>
    cases n with
    | zero => exact ⟨a, rfl⟩
    | succ n => exact ih n (by simpa using hn)

theorem stone_app (l₁ l₂ : List Player) (n : Nat) :
    stone (l₁ ++ l₂) n = if n < l₁.length then stone l₁ n else stone l₂ (n - l₁.length) := by
  induction l₁ generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp [stone]
    | succ n => simpa [stone] using ih n

theorem stone_take (l : List Player) (r n : Nat) (hn : n < r) :
    stone (l.take r) n = stone l n := by
  induction l generalizing r n with
  | nil => simp [stone]
  | cons a l ih =>
    cases r with
    | zero => omega
    | succ r =>
      cases n with
      | zero => simp [stone]
      | succ n => simpa [stone] using ih r n (by omega)

theorem stone_drop (l : List Player) (r n : Nat) :
    stone (l.drop r) n = stone l (n + r) := by
  induction l generalizing r with
  | nil => simp [stone]
  | cons a l ih =>
    cases r with
    | zero => simp
    | succ r =>
      simp only [List.drop_succ_cons]
      exact ih r

/-! ## Defects, landmarks, clear cuts -/

/-- Rows `ℓ` and `ℓ+1` (1-based) of the column carry the same colour. -/
def IsDefect (l : List Player) (ℓ : Nat) : Prop :=
  1 ≤ ℓ ∧ ℓ < l.length ∧ stone l (ℓ - 1) = stone l ℓ

def Landmark (h : Nat) (b : Board w) (ℓ : Nat) : Prop :=
  ℓ = 0 ∨ ℓ = h ∨ (∃ c, (b c).length = ℓ) ∨ (∃ c, IsDefect (b c) ℓ)

/-- Level `r` lies on the board and no landmark is within distance `D` of it. -/
def ClearCut (D h : Nat) (b : Board w) (r : Nat) : Prop :=
  r ≤ h ∧ ∀ ℓ, Landmark h b ℓ → ℓ + D < r ∨ r + D < ℓ

/-- In an alternating stretch, cells two rows apart have the same colour. -/
theorem stone_alt2 (l : List Player) (m : Nat) (hm : m + 2 < l.length)
    (h1 : ¬ IsDefect l (m + 1)) (h2 : ¬ IsDefect l (m + 2)) :
    stone l m = stone l (m + 2) := by
  obtain ⟨a, ha⟩ := stone_some_of_lt l m (by omega)
  obtain ⟨b, hb⟩ := stone_some_of_lt l (m + 1) (by omega)
  obtain ⟨c, hc⟩ := stone_some_of_lt l (m + 2) (by omega)
  have hab : a ≠ b := by
    intro e; apply h1
    refine ⟨by omega, by omega, ?_⟩
    simp only [Nat.add_sub_cancel]; rw [ha, hb, e]
  have hbc : b ≠ c := by
    intro e; apply h2
    refine ⟨by omega, by omega, ?_⟩
    show stone l (m + 1) = stone l (m + 2)
    rw [hb, hc, e]
  rw [ha, hc]
  cases a <;> cases b <;> cases c <;> simp_all

/-! ## Stretching a column -/

/-- Insert two rows above level `r` in a column that passes through. -/
def colStretch (l : List Player) (r : Nat) : List Player :=
  if r < l.length then
    l.take r ++ ((stone l r).toList ++ ((stone l (r - 1)).toList ++ l.drop r))
  else l

def stretch (b : Board w) (r : Nat) : Board w := fun c => colStretch (b c) r

theorem stone_colStretch (l : List Player) (r n : Nat) (hr : 1 ≤ r) (hl : r < l.length) :
    stone (colStretch l r) n =
      if n < r then stone l n else if n = r then stone l r
      else if n = r + 1 then stone l (r - 1) else stone l (n - 2) := by
  obtain ⟨a, ha⟩ := stone_some_of_lt l r hl
  obtain ⟨b, hb⟩ := stone_some_of_lt l (r - 1) (by omega)
  have hlen : (l.take r).length = r := by simp; omega
  simp only [colStretch, if_pos hl, ha, hb, Option.toList_some]
  rw [stone_app, hlen]
  by_cases h1 : n < r
  · simp only [if_pos h1]; exact stone_take l r n h1
  · simp only [if_neg h1]
    by_cases h2 : n = r
    · subst h2; simp [stone]
    · simp only [if_neg h2]
      by_cases h3 : n = r + 1
      · subst h3; simp [stone]
      · simp only [if_neg h3]
        obtain ⟨k, rfl⟩ : ∃ k, n = r + 2 + k := ⟨n - (r + 2), by omega⟩
        have e1 : r + 2 + k - r = k + 2 := by omega
        have e2 : r + 2 + k - 2 = k + r := by omega
        rw [e1, e2]
        show stone (l.drop r) k = stone l (k + r)
        exact stone_drop l r k

/-! ## Clear cuts, column by column -/

/-- What a clear cut at level `r` says about one column: it is low, or it passes through and
alternates on the window. -/
def ColClear (D r : Nat) (l : List Player) : Prop :=
  (l.length + D < r) ∨ (r + D < l.length ∧ ∀ ℓ, r ≤ ℓ + D → ℓ ≤ r + D → ¬ IsDefect l ℓ)

theorem colClear_of_clearCut {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (c : Fin w) :
    ColClear D r (b c) := by
  have htop := hc.2 (b c).length (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))
  rcases htop with h1 | h2
  · exact Or.inl h1
  · refine Or.inr ⟨h2, fun ℓ h3 h4 hd => ?_⟩
    have := hc.2 ℓ (Or.inr (Or.inr (Or.inr ⟨c, hd⟩)))
    omega

theorem clearCut_bounds {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) :
    D < r ∧ r + D < h := by
  have h0 := hc.2 0 (Or.inl rfl)
  have hh := hc.2 h (Or.inr (Or.inl rfl))
  have := hc.1
  omega

/-- (i) The stretched column agrees with the original on indices `≤ r + D`. -/
theorem colStretch_low {D r : Nat} {l : List Player} (hD : 1 ≤ D) (hr : D < r)
    (hcl : ColClear D r l) (n : Nat) (hn : n ≤ r + D) :
    stone (colStretch l r) n = stone l n := by
  rcases hcl with hlow | ⟨hth, hnd⟩
  · have : ¬ r < l.length := by omega
    simp [colStretch, this]
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [stone_colStretch l (r' + 1) n (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    by_cases h1 : n < r' + 1
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : n = r' + 1
      · rw [if_pos h2, h2]
      · rw [if_neg h2]
        by_cases h3 : n = r' + 1 + 1
        · rw [if_pos h3, h3]
          exact stone_alt2 l r' (by omega) (hnd (r' + 1) (by omega) (by omega))
            (hnd (r' + 2) (by omega) (by omega))
        · rw [if_neg h3]
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          simp only [Nat.add_sub_cancel]
          exact stone_alt2 l m (by omega) (hnd (m + 1) (by omega) (by omega))
            (hnd (m + 2) (by omega) (by omega))

/-- (ii) The stretched column agrees with the original shifted up by two on indices `≥ r - D + 1`. -/
theorem colStretch_high {D r : Nat} {l : List Player} (hD : 1 ≤ D) (hr : D < r)
    (hcl : ColClear D r l) (n : Nat) (hn : r + 1 ≤ n + D) :
    stone (colStretch l r) n = stone l (n - 2) := by
  rcases hcl with hlow | ⟨hth, hnd⟩
  · have : ¬ r < l.length := by omega
    simp only [colStretch, if_neg this]
    rw [stone_none l n (by omega), stone_none l (n - 2) (by omega)]
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [stone_colStretch l (r' + 1) n (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    by_cases h1 : m + 2 < r' + 1
    · rw [if_pos h1]
      exact (stone_alt2 l m (by omega) (hnd (m + 1) (by omega) (by omega))
        (hnd (m + 2) (by omega) (by omega))).symm
    · rw [if_neg h1]
      by_cases h2 : m + 2 = r' + 1
      · rw [if_pos h2, ← h2]
        exact (stone_alt2 l m (by omega) (hnd (m + 1) (by omega) (by omega))
          (hnd (m + 2) (by omega) (by omega))).symm
      · rw [if_neg h2]
        by_cases h3 : m + 2 = r' + 1 + 1
        · rw [if_pos h3]
          have : m = r' := by omega
          rw [this]
        · rw [if_neg h3]

/-! ## Lemma A: stretching preserves fours -/

theorem cell_low {D h r : Nat} {b : Board w} (hD : 1 ≤ D) (hc : ClearCut D h b r)
    (x y : Int) (hy : y ≤ r + D) :
    cellAtInt (h + 2) (stretch b r) x y = cellAtInt h b x y := by
  have hb := clearCut_bounds hc
  unfold cellAtInt
  by_cases hx : 0 ≤ x ∧ x < (w : Int)
  · rw [dif_pos hx, dif_pos hx]
    by_cases hy0 : 0 ≤ y
    · rw [if_pos (by omega), if_pos (by omega)]
      exact colStretch_low hD hb.1 (colClear_of_clearCut hc _) y.toNat (by omega)
    · rw [if_neg (by omega), if_neg (by omega)]
  · rw [dif_neg hx, dif_neg hx]

theorem cell_high {D h r : Nat} {b : Board w} (hD : 1 ≤ D) (hc : ClearCut D h b r)
    (x y : Int) (hy : (r : Int) + 1 ≤ y + D) :
    cellAtInt (h + 2) (stretch b r) x y = cellAtInt h b x (y - 2) := by
  have hb := clearCut_bounds hc
  unfold cellAtInt
  by_cases hx : 0 ≤ x ∧ x < (w : Int)
  · rw [dif_pos hx, dif_pos hx]
    by_cases hy1 : y < (h : Int) + 2
    · rw [if_pos (by omega), if_pos (by omega)]
      have e : (y - 2).toNat = y.toNat - 2 := by omega
      rw [e]
      exact colStretch_high hD hb.1 (colClear_of_clearCut hc _) y.toNat (by omega)
    · rw [if_neg (by omega), if_neg (by omega)]
  · rw [dif_neg hx, dif_neg hx]

theorem dir_fwd {D h r : Nat} {b : Board w} (hD : 1 ≤ D) (hc : ClearCut D h b r) {p : Player}
    {x y dx dy : Int} (hdy : dy = 0 ∨ dy = 1 ∨ dy = -1) (hf : HasFourDir h b p x y dx dy) :
    HasFourDir (h + 2) (stretch b r) p x y dx dy ∨
    HasFourDir (h + 2) (stretch b r) p x (y + 2) dx dy := by
  by_cases hall : y ≤ r + D ∧ y + 3 * dy ≤ r + D
  · left; intro i
    have hi := i.isLt
    rw [cell_low hD hc _ _ (by rcases hdy with rfl | rfl | rfl <;> omega)]
    exact hf i
  · right; intro i
    have hi := i.isLt
    rw [cell_high hD hc _ _ (by rcases hdy with rfl | rfl | rfl <;> omega)]
    have e : y + 2 + (i : Int) * dy - 2 = y + (i : Int) * dy := by
      rcases hdy with rfl | rfl | rfl <;> omega
    rw [e]; exact hf i

theorem dir_bwd {D h r : Nat} {b : Board w} (hD : 2 ≤ D) (hc : ClearCut D h b r) {p : Player}
    {x y dx dy : Int} (hdy : dy = 0 ∨ dy = 1 ∨ dy = -1)
    (hf : HasFourDir (h + 2) (stretch b r) p x y dx dy) :
    HasFourDir h b p x y dx dy ∨ HasFourDir h b p x (y - 2) dx dy := by
  by_cases hall : y ≤ r + D ∧ y + 3 * dy ≤ r + D
  · left; intro i
    have hi := i.isLt
    rw [← cell_low (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> omega)]
    exact hf i
  · right; intro i
    have hi := i.isLt
    have e : y - 2 + (i : Int) * dy = y + (i : Int) * dy - 2 := by
      rcases hdy with rfl | rfl | rfl <;> omega
    rw [e, ← cell_high (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> omega)]
    exact hf i

/-- **Lemma A** (for `D ≥ 2`, the precision used by all computations).  Stretching at a clear cut
preserves the existence of a four, for either colour, in both directions. -/
theorem hasFour_stretch_iff {D h r : Nat} {b : Board w} (hD : 2 ≤ D)
    (hc : ClearCut D h b r) (p : Player) :
    HasFour h b p ↔ HasFour (h + 2) (stretch b r) p := by
  constructor
  · rintro (⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩)
    · rcases dir_fwd (by omega) hc (Or.inr (Or.inl rfl)) hf with h1 | h1
      exacts [Or.inl ⟨x, y, h1⟩, Or.inl ⟨x, y + 2, h1⟩]
    · rcases dir_fwd (by omega) hc (Or.inl rfl) hf with h1 | h1
      exacts [Or.inr (Or.inl ⟨x, y, h1⟩), Or.inr (Or.inl ⟨x, y + 2, h1⟩)]
    · rcases dir_fwd (by omega) hc (Or.inr (Or.inl rfl)) hf with h1 | h1
      exacts [Or.inr (Or.inr (Or.inl ⟨x, y, h1⟩)), Or.inr (Or.inr (Or.inl ⟨x, y + 2, h1⟩))]
    · rcases dir_fwd (by omega) hc (Or.inr (Or.inr rfl)) hf with h1 | h1
      exacts [Or.inr (Or.inr (Or.inr ⟨x, y, h1⟩)), Or.inr (Or.inr (Or.inr ⟨x, y + 2, h1⟩))]
  · rintro (⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩ | ⟨x, y, hf⟩)
    · rcases dir_bwd hD hc (Or.inr (Or.inl rfl)) hf with h1 | h1
      exacts [Or.inl ⟨x, y, h1⟩, Or.inl ⟨x, y - 2, h1⟩]
    · rcases dir_bwd hD hc (Or.inl rfl) hf with h1 | h1
      exacts [Or.inr (Or.inl ⟨x, y, h1⟩), Or.inr (Or.inl ⟨x, y - 2, h1⟩)]
    · rcases dir_bwd hD hc (Or.inr (Or.inl rfl)) hf with h1 | h1
      exacts [Or.inr (Or.inr (Or.inl ⟨x, y, h1⟩)), Or.inr (Or.inr (Or.inl ⟨x, y - 2, h1⟩))]
    · rcases dir_bwd hD hc (Or.inr (Or.inr rfl)) hf with h1 | h1
      exacts [Or.inr (Or.inr (Or.inr ⟨x, y, h1⟩)), Or.inr (Or.inr (Or.inr ⟨x, y - 2, h1⟩))]

#print axioms hasFour_stretch_iff

end C4W5
