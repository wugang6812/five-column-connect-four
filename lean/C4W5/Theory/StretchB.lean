import C4W5.Theory.Stretch

/-!
# Stretching: landmarks, commutation with moves (towards Lemma B)
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

variable {w : Nat}

set_option linter.deprecated false

theorem list_ext_stone : ∀ (l₁ l₂ : List Player), (∀ n, stone l₁ n = stone l₂ n) → l₁ = l₂
  | [], [], _ => rfl
  | [], b :: l₂, h => by have := h 0; simp [stone] at this
  | a :: l₁, [], h => by have := h 0; simp [stone] at this
  | a :: l₁, b :: l₂, h => by
    have h0 := h 0
    simp only [stone, Option.some.injEq] at h0
    rw [h0, list_ext_stone l₁ l₂ (fun n => by simpa [stone] using h (n + 1))]

theorem stone_lt_iff (l : List Player) (n : Nat) : n < l.length ↔ ∃ p, stone l n = some p := by
  constructor
  · exact stone_some_of_lt l n
  · rintro ⟨p, hp⟩; exact stone_bound l n p hp

theorem colStretch_length (l : List Player) (r : Nat) (hr : 1 ≤ r) :
    (colStretch l r).length = if r < l.length then l.length + 2 else l.length := by
  by_cases h : r < l.length
  · rw [if_pos h]
    obtain ⟨a, ha⟩ := stone_some_of_lt l r h
    obtain ⟨b, hb⟩ := stone_some_of_lt l (r - 1) (by omega)
    simp only [colStretch, if_pos h, ha, hb, Option.toList_some, List.length_append, List.length_take,
      List.length_drop, List.length_cons, List.length_nil]
    omega
  · rw [if_neg h]; simp [colStretch, h]

/-- Defects of a stretched through-column. -/
theorem isDefect_colStretch {l : List Player} {r : Nat} (hr : 1 ≤ r) (hl : r < l.length)
    (hnd : ¬ IsDefect l r) (ℓ : Nat) :
    IsDefect (colStretch l r) ℓ ↔ (IsDefect l ℓ ∧ ℓ < r) ∨ (∃ ℓ', IsDefect l ℓ' ∧ r < ℓ' ∧ ℓ = ℓ' + 2) := by
  have hne : stone l (r - 1) ≠ stone l r := fun e => hnd ⟨hr, hl, e⟩
  unfold IsDefect
  rw [colStretch_length l r hr, if_pos hl, stone_colStretch l r _ hr hl, stone_colStretch l r _ hr hl]
  by_cases h1 : ℓ < r
  · have e1 : ℓ - 1 < r := by omega
    simp only [if_pos e1, if_pos h1]
    constructor
    · rintro ⟨a, -, c⟩; exact Or.inl ⟨⟨a, by omega, c⟩, h1⟩
    · rintro (⟨⟨a, b, c⟩, -⟩ | ⟨ℓ', -, h2, h3⟩)
      · exact ⟨a, by omega, c⟩
      · omega
  · by_cases h2 : ℓ = r
    · subst h2
      have e1 : ℓ - 1 < ℓ := by omega
      simp only [if_pos e1, if_neg (lt_irrefl ℓ)]
      constructor
      · rintro ⟨-, -, c⟩; exact absurd c hne
      · rintro (⟨-, h⟩ | ⟨ℓ', -, h2, h3⟩) <;> omega
    · by_cases h3 : ℓ = r + 1
      · subst h3
        have e0 : r + 1 - 1 = r := by omega
        simp only [e0, if_neg (lt_irrefl r), if_neg (show ¬ r + 1 < r by omega),
          if_neg (show ¬ r + 1 = r by omega)]
        constructor
        · rintro ⟨-, -, c⟩; exact absurd c.symm hne
        · rintro (⟨-, h⟩ | ⟨ℓ', -, h2, h3⟩) <;> omega
      · by_cases h4 : ℓ = r + 2
        · subst h4
          have e0 : r + 2 - 1 = r + 1 := by omega
          have e2 : r + 2 - 2 = r := by omega
          simp only [e0, e2, if_neg (show ¬ r + 1 < r by omega), if_neg (show ¬ r + 1 = r by omega),
            if_neg (show ¬ r + 2 < r by omega), if_neg (show ¬ r + 2 = r by omega),
            if_neg (show ¬ r + 2 = r + 1 by omega)]
          constructor
          · rintro ⟨-, -, c⟩; exact absurd c hne
          · rintro (⟨-, h⟩ | ⟨ℓ', -, h2, h3⟩) <;> omega
        · have e1 : ¬ ℓ - 1 < r := by omega
          have e2 : ¬ ℓ - 1 = r := by omega
          have e3 : ¬ ℓ - 1 = r + 1 := by omega
          have e4 : ℓ - 1 - 2 = ℓ - 2 - 1 := by omega
          simp only [if_neg e1, if_neg e2, if_neg e3, if_neg h1, if_neg h2, if_neg h3, e4]
          constructor
          · rintro ⟨a, b, c⟩
            exact Or.inr ⟨ℓ - 2, ⟨by omega, by omega, c⟩, by omega, by omega⟩
          · rintro (⟨-, h⟩ | ⟨ℓ', ⟨a, b, c⟩, h5, h6⟩)
            · omega
            · subst h6
              have e5 : ℓ' + 2 - 2 = ℓ' := by omega
              rw [e5]; exact ⟨by omega, by omega, c⟩

/-! ## Landmarks of a stretched board -/

theorem stretch_length {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (c : Fin w) :
    (stretch b r c).length = if r < (b c).length then (b c).length + 2 else (b c).length :=
  colStretch_length _ _ (by have := clearCut_bounds hc; omega)

theorem not_defect_of_clear {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (c : Fin w) :
    ¬ IsDefect (b c) r := by
  intro hd
  have := hc.2 r (Or.inr (Or.inr (Or.inr ⟨c, hd⟩)))
  omega

theorem top_of_clear {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (c : Fin w) :
    (b c).length + D < r ∨ r + D < (b c).length :=
  hc.2 _ (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))

/-- **Landmarks after stretching**: those below the cut stay, those above move up by two. -/
theorem landmark_stretch {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (ℓ : Nat) :
    Landmark (h + 2) (stretch b r) ℓ ↔
      (Landmark h b ℓ ∧ ℓ < r) ∨ (∃ ℓ', Landmark h b ℓ' ∧ r < ℓ' ∧ ℓ = ℓ' + 2) := by
  have hb := clearCut_bounds hc
  constructor
  · rintro (h0 | h1 | ⟨c, h2⟩ | ⟨c, h3⟩)
    · exact Or.inl ⟨Or.inl h0, by omega⟩
    · exact Or.inr ⟨h, Or.inr (Or.inl rfl), by omega, h1⟩
    · rw [stretch_length hc] at h2
      have ht := top_of_clear hc c
      by_cases hlt : r < (b c).length
      · rw [if_pos hlt] at h2
        exact Or.inr ⟨(b c).length, Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)), hlt, h2.symm⟩
      · rw [if_neg hlt] at h2
        exact Or.inl ⟨Or.inr (Or.inr (Or.inl ⟨c, h2⟩)), by omega⟩
    · have ht := top_of_clear hc c
      by_cases hlt : r < (b c).length
      · have := (isDefect_colStretch (by omega) hlt (not_defect_of_clear hc c) ℓ).mp h3
        rcases this with ⟨hd, hl⟩ | ⟨ℓ', hd, hl, he⟩
        · exact Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨c, hd⟩)), hl⟩
        · exact Or.inr ⟨ℓ', Or.inr (Or.inr (Or.inr ⟨c, hd⟩)), hl, he⟩
      · have e : stretch b r c = b c := by simp [stretch, colStretch, hlt]
        rw [e] at h3
        exact Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨c, h3⟩)), by have := h3.2.1; omega⟩
  · rintro (⟨hl, hlt⟩ | ⟨ℓ', hl, hlt, rfl⟩)
    · rcases hl with h0 | h1 | ⟨c, h2⟩ | ⟨c, h3⟩
      · exact Or.inl h0
      · omega
      · refine Or.inr (Or.inr (Or.inl ⟨c, ?_⟩))
        rw [stretch_length hc, if_neg (by omega)]; exact h2
      · have ht := top_of_clear hc c
        refine Or.inr (Or.inr (Or.inr ⟨c, ?_⟩))
        by_cases hth : r < (b c).length
        · exact (isDefect_colStretch (by omega) hth (not_defect_of_clear hc c) ℓ).mpr (Or.inl ⟨h3, hlt⟩)
        · have e : stretch b r c = b c := by simp [stretch, colStretch, hth]
          rw [e]; exact h3
    · rcases hl with h0 | h1 | ⟨c, h2⟩ | ⟨c, h3⟩
      · omega
      · exact Or.inr (Or.inl (by omega))
      · refine Or.inr (Or.inr (Or.inl ⟨c, ?_⟩))
        rw [stretch_length hc, if_pos (by omega)]; omega
      · refine Or.inr (Or.inr (Or.inr ⟨c, ?_⟩))
        have hth : r < (b c).length := by have := h3.2.1; omega
        exact (isDefect_colStretch (by omega) hth (not_defect_of_clear hc c) _).mpr (Or.inr ⟨ℓ', h3, hlt, rfl⟩)

/-- Cuts at or below the stretched cut: clear before iff clear after. -/
theorem clear_stretch_low {D h r s : Nat} {b : Board w} (hc : ClearCut D h b r) (hs : s ≤ r) :
    ClearCut D (h + 2) (stretch b r) s ↔ ClearCut D h b s := by
  have hb := clearCut_bounds hc
  constructor
  · rintro ⟨-, H⟩
    refine ⟨by omega, fun ℓ hl => ?_⟩
    have hcl := hc.2 ℓ hl
    rcases hcl with h1 | h1
    · exact H ℓ ((landmark_stretch hc ℓ).mpr (Or.inl ⟨hl, by omega⟩))
    · omega
  · rintro ⟨-, H⟩
    refine ⟨by omega, fun ℓ hl => ?_⟩
    rcases (landmark_stretch hc ℓ).mp hl with ⟨hl', -⟩ | ⟨ℓ', hl', hlt, rfl⟩
    · exact H ℓ hl'
    · have := hc.2 ℓ' hl'; omega

/-- Cuts at or above the stretched cut move up by two. -/
theorem clear_stretch_high {D h r s : Nat} {b : Board w} (hc : ClearCut D h b r) (hs : r ≤ s) :
    ClearCut D (h + 2) (stretch b r) (s + 2) ↔ ClearCut D h b s := by
  have hb := clearCut_bounds hc
  constructor
  · rintro ⟨hle, H⟩
    refine ⟨by omega, fun ℓ hl => ?_⟩
    have hcl := hc.2 ℓ hl
    rcases hcl with h1 | h1
    · omega
    · have := H (ℓ + 2) ((landmark_stretch hc _).mpr (Or.inr ⟨ℓ, hl, by omega, rfl⟩)); omega
  · rintro ⟨hle, H⟩
    refine ⟨by omega, fun ℓ hl => ?_⟩
    rcases (landmark_stretch hc ℓ).mp hl with ⟨hl', hlt⟩ | ⟨ℓ', hl', hlt, rfl⟩
    · have := hc.2 ℓ hl'; omega
    · have := H ℓ' hl'; omega

/-- Just above a stretched cut everything is clear. -/
theorem clear_stretch_mid {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) :
    ClearCut D (h + 2) (stretch b r) (r + 1) := by
  have hb := clearCut_bounds hc
  refine ⟨by omega, fun ℓ hl => ?_⟩
  rcases (landmark_stretch hc ℓ).mp hl with ⟨hl', hlt⟩ | ⟨ℓ', hl', hlt, rfl⟩
  · have := hc.2 ℓ hl'; omega
  · have := hc.2 ℓ' hl'; omega

/-! ## Moves and stretches -/

theorem stone_append_list (l : List Player) (p : Player) (n : Nat) (hn : n < l.length) :
    stone (l ++ [p]) n = stone l n := by
  rw [stone_append, if_pos hn]

theorem colStretch_append {l : List Player} {r : Nat} (hr : 1 ≤ r) (hl : r < l.length) (p : Player) :
    colStretch (l ++ [p]) r = colStretch l r ++ [p] := by
  apply list_ext_stone
  intro n
  have hl' : r < (l ++ [p]).length := by simp; omega
  rw [stone_colStretch (l ++ [p]) r n hr hl', stone_append (colStretch l r) p n,
    colStretch_length l r hr, if_pos hl, stone_colStretch l r n hr hl]
  simp only [stone_append]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- **A move commutes with a stretch at any clear cut.** -/
theorem play_stretch {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (c : Fin w) (p : Player) :
    play (stretch b r) c p = stretch (play b c p) r := by
  have hb := clearCut_bounds hc
  funext d
  by_cases hd : d = c
  · subst hd
    simp only [play_eq, stretch]
    rcases top_of_clear hc d with ht | ht
    · have e1 : colStretch (b d) r = b d := by simp [colStretch]; omega
      have e2 : colStretch (b d ++ [p]) r = b d ++ [p] := by simp [colStretch]; omega
      rw [e1, e2]
    · rw [colStretch_append (by omega) (by omega)]
  · simp only [stretch, play_ne _ _ _ _ hd]

/-- Landmarks after a move: the old ones and the new top. -/
theorem landmark_play {h : Nat} {b : Board w} (c : Fin w) (p : Player) (ℓ : Nat)
    (hl : Landmark h (play b c p) ℓ) : Landmark h b ℓ ∨ ℓ = (b c).length + 1 := by
  rcases hl with h0 | h1 | ⟨d, h2⟩ | ⟨d, h3⟩
  · exact Or.inl (Or.inl h0)
  · exact Or.inl (Or.inr (Or.inl h1))
  · by_cases hd : d = c
    · subst hd; rw [play_eq] at h2; right; simp at h2; omega
    · rw [play_ne _ _ _ _ hd] at h2; exact Or.inl (Or.inr (Or.inr (Or.inl ⟨d, h2⟩)))
  · by_cases hd : d = c
    · subst hd
      rw [play_eq] at h3
      obtain ⟨a, bb, cc⟩ := h3
      simp only [List.length_append, List.length_cons, List.length_nil] at bb
      by_cases he : ℓ = (b d).length
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨d, he.symm⟩)))
      · left
        refine Or.inr (Or.inr (Or.inr ⟨d, a, by omega, ?_⟩))
        rw [stone_append_list _ _ _ (by omega), stone_append_list _ _ _ (by omega)] at cc
        exact cc
    · rw [play_ne _ _ _ _ hd] at h3; exact Or.inl (Or.inr (Or.inr (Or.inr ⟨d, h3⟩)))

/-- A clear cut stays clear after a move unless it is within `D` of the new top. -/
theorem clear_play {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (c : Fin w) (p : Player)
    (hfar : (b c).length + 1 + D < r ∨ r + D < (b c).length + 1) : ClearCut D h (play b c p) r := by
  refine ⟨hc.1, fun ℓ hl => ?_⟩
  rcases landmark_play c p ℓ hl with h1 | h1
  · exact hc.2 ℓ h1
  · omega

/-- Two adjacent clear cuts give the same stretched board. -/
theorem stretch_succ {D h r : Nat} {b : Board w} (hc : ClearCut D h b r) (hc' : ClearCut D h b (r + 1)) :
    stretch b r = stretch b (r + 1) := by
  have hb := clearCut_bounds hc
  funext c
  simp only [stretch]
  rcases top_of_clear hc c with ht | ht
  · have ht' := top_of_clear hc' c
    have e1 : colStretch (b c) r = b c := by simp [colStretch]; omega
    have e2 : colStretch (b c) (r + 1) = b c := by simp [colStretch]; omega
    rw [e1, e2]
  · have ht' := top_of_clear hc' c
    have hl1 : r + 1 < (b c).length := by omega
    apply list_ext_stone
    intro n
    rw [stone_colStretch _ r n (by omega) (by omega), stone_colStretch _ (r + 1) n (by omega) hl1]
    have halt : stone (b c) (r - 1) = stone (b c) (r + 1) := by
      have := stone_alt2 (b c) (r - 1) (by omega)
        (by have := not_defect_of_clear hc c; rwa [show r - 1 + 1 = r by omega])
        (by have := not_defect_of_clear hc' c; rwa [show r - 1 + 2 = r + 1 by omega])
      rwa [show r - 1 + 2 = r + 1 by omega] at this
    have hcase : n < r ∨ n = r ∨ n = r + 1 ∨ n = r + 2 ∨ r + 3 ≤ n := by omega
    rcases hcase with h1 | rfl | rfl | rfl | h1
    · rw [if_pos h1, if_pos (by omega)]
    · simp
    · simp [halt]
    · simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]

/-- Row map of a stretch: row `n` of the stretched column shows row `phi r n` of the original. -/
def phi (r n : Nat) : Nat := if n < r then n else if n = r then r else if n = r + 1 then r - 1 else n - 2

theorem stone_phi (l : List Player) (r n : Nat) (hr : 1 ≤ r) (hl : r < l.length) :
    stone (colStretch l r) n = stone l (phi r n) := by
  rw [stone_colStretch l r n hr hl]; unfold phi; split_ifs <;> rfl

theorem phi_lt {r n : Nat} (h : n < r) : phi r n = n := by unfold phi; rw [if_pos h]
theorem phi_self (r : Nat) : phi r r = r := by unfold phi; rw [if_neg (lt_irrefl r), if_pos rfl]
theorem phi_succ (r : Nat) : phi r (r + 1) = r - 1 := by
  unfold phi; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem phi_gt {r n : Nat} (h : r + 2 ≤ n) : phi r n = n - 2 := by
  unfold phi; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem phi_comm (a b n : Nat) (hab : a + 2 ≤ b) : phi a (phi (b + 2) n) = phi b (phi a n) := by
  have hcase : n < a ∨ n = a ∨ n = a + 1 ∨ (a + 2 ≤ n ∧ n < b + 2) ∨ n = b + 2 ∨ n = b + 3 ∨ b + 4 ≤ n := by
    omega
  rcases hcase with h | h | h | ⟨h1, h2⟩ | h | h | h
  · rw [phi_lt (show n < b + 2 by omega), phi_lt h, phi_lt (show n < b by omega)]
  · rw [h, phi_lt (show a < b + 2 by omega), phi_self, phi_lt (show a < b by omega)]
  · rw [h, phi_lt (show a + 1 < b + 2 by omega), phi_succ, phi_lt (show a - 1 < b by omega)]
  · rw [phi_lt h2, phi_gt h1, phi_lt (show n - 2 < b by omega)]
  · rw [h, phi_self, phi_gt (show a + 2 ≤ b + 2 by omega), show b + 2 - 2 = b by omega, phi_self]
  · rw [h, show b + 3 = b + 2 + 1 by omega, phi_succ, show b + 2 - 1 = b + 1 by omega,
      phi_gt (show a + 2 ≤ b + 1 by omega), phi_gt (show a + 2 ≤ b + 2 + 1 by omega),
      show b + 2 + 1 - 2 = b + 1 by omega, phi_succ]
    omega
  · rw [phi_gt (show b + 2 + 2 ≤ n by omega), phi_gt (show a + 2 ≤ n - 2 by omega),
      phi_gt (show a + 2 ≤ n by omega), phi_gt (show b + 2 ≤ n - 2 by omega)]

/-- Stretches at two different clear cuts commute (with the obvious shift). -/
theorem stretch_comm {D h a b : Nat} {X : Board w} (ha : ClearCut D h X a) (hb : ClearCut D h X b)
    (hab : a + 2 ≤ b) : stretch (stretch X a) (b + 2) = stretch (stretch X b) a := by
  have hba := clearCut_bounds ha
  funext c
  simp only [stretch]
  rcases top_of_clear ha c with ht | ht
  · have e1 : colStretch (X c) a = X c := by simp [colStretch]; omega
    have e2 : colStretch (X c) b = X c := by simp [colStretch]; omega
    have e3 : colStretch (X c) (b + 2) = X c := by simp [colStretch]; omega
    rw [e1, e2, e3, e1]
  · rcases top_of_clear hb c with ht' | ht'
    · have e2 : colStretch (X c) b = X c := by simp [colStretch]; omega
      have hlen := colStretch_length (X c) a (by omega)
      rw [if_pos (by omega)] at hlen
      have hnot : ¬ b + 2 < (colStretch (X c) a).length := by rw [hlen]; omega
      have e3 : colStretch (colStretch (X c) a) (b + 2) = colStretch (X c) a := by
        rw [colStretch, if_neg hnot]
      rw [e2, e3]
    · have hla := colStretch_length (X c) a (by omega)
      rw [if_pos (by omega)] at hla
      have hlb := colStretch_length (X c) b (by omega)
      rw [if_pos (by omega)] at hlb
      apply list_ext_stone
      intro n
      rw [stone_phi _ (b + 2) n (by omega) (by rw [hla]; omega), stone_phi _ a _ (by omega) (by omega),
        stone_phi _ a n (by omega) (by rw [hlb]; omega), stone_phi _ b _ (by omega) (by omega)]
      congr 1
      exact phi_comm a b n hab

/-! ## Stretch-equivalence -/

/-- `SEq D h A h' R`: the board `R` (height `h'`) is obtained from `A` (height `h`) by successive
stretches at clear cuts. -/
inductive SEq (D : Nat) : Nat → Board w → Nat → Board w → Prop
  | refl (h : Nat) (A : Board w) : SEq D h A h A
  | step {h : Nat} {A : Board w} {h' : Nat} {R : Board w} (r : Nat) :
      ClearCut D h A r → SEq D (h + 2) (stretch A r) h' R → SEq D h A h' R

theorem SEq.trans {D h h₁ h₂ : Nat} {A X R : Board w} (h1 : SEq D h A h₁ X) (h2 : SEq D h₁ X h₂ R) :
    SEq D h A h₂ R := by
  induction h1 with
  | refl => exact h2
  | step r hc _ ih => exact SEq.step r hc (ih h2)

theorem SEq.single {D h r : Nat} {A : Board w} (hc : ClearCut D h A r) :
    SEq D h A (h + 2) (stretch A r) := SEq.step r hc (SEq.refl _ _)

/-- **Lemma A along a chain of stretches.** -/
theorem SEq.hasFour_iff {D h h' : Nat} {A R : Board w} (hD : 2 ≤ D) (hs : SEq D h A h' R) (p : Player) :
    HasFour h A p ↔ HasFour h' R p := by
  induction hs with
  | refl => rfl
  | step r hc _ ih => rw [hasFour_stretch_iff hD hc p]; exact ih

theorem SEq.legal_iff {D h h' : Nat} {A R : Board w} (hs : SEq D h A h' R) (c : Fin w) :
    Legal h A c ↔ Legal h' R c := by
  induction hs with
  | refl => rfl
  | step r hc _ ih =>
    rw [← ih]
    unfold Legal
    rw [stretch_length hc]
    have hb := clearCut_bounds hc
    rcases top_of_clear hc c with ht | ht
    · rw [if_neg (by omega)]; constructor <;> intro <;> omega
    · rw [if_pos (by omega)]; constructor <;> intro <;> omega

theorem SEq.full_iff {D h h' : Nat} {A R : Board w} (hs : SEq D h A h' R) :
    BoardFull h A ↔ BoardFull h' R := by
  induction hs with
  | refl => rfl
  | step r hc _ ih =>
    rw [← ih]
    unfold BoardFull
    have hb := clearCut_bounds hc
    constructor
    · intro hf c
      rw [stretch_length hc, if_pos (by rw [hf c]; omega), hf c]
    · intro hf c
      have := hf c
      rw [stretch_length hc] at this
      rcases top_of_clear hc c with ht | ht
      · rw [if_neg (by omega)] at this; omega
      · rw [if_pos (by omega)] at this; omega

/-! ## Lemma B: a move in a stretched board -/

/-- The conclusion of Lemma B for a base board `A`: after the move, the real board is a stretch of
`A` moved, or (only if the gap above the column is exactly `2D+2`) of `A` stretched once in that gap
and then moved. -/
def PlayRel (D h : Nat) (A : Board w) (c : Fin w) (p : Player) (h' : Nat) (R' : Board w) : Prop :=
  SEq D h (play A c p) h' R' ∨
  (ClearCut D h A ((A c).length + D + 1) ∧ ¬ ClearCut D h A ((A c).length + D + 2) ∧
    SEq D (h + 2) (play (stretch A ((A c).length + D + 1)) c p) h' R')

/-- One step of the induction, for a first stretch that is not at the critical level. -/
theorem playRel_step {D h r h' : Nat} {A R' : Board w} {c : Fin w} {p : Player}
    (hc : ClearCut D h A r) (hne : r ≠ (A c).length + D + 1)
    (ih : PlayRel D (h + 2) (stretch A r) c p h' R') : PlayRel D h A c p h' R' := by
  have hb := clearCut_bounds hc
  have hlenB := stretch_length hc c
  rcases top_of_clear hc c with ht | ht
  · -- column `c` is below the cut
    rw [if_neg (by omega)] at hlenB
    have hsingle : SEq D h (play A c p) (h + 2) (play (stretch A r) c p) := by
      rw [play_stretch hc]
      exact SEq.single (clear_play hc c p (Or.inl (by omega)))
    rcases ih with ih | ⟨c1, c2, ih⟩
    · exact Or.inl (hsingle.trans ih)
    · rw [hlenB] at c1 c2 ih
      have c1' : ClearCut D h A ((A c).length + D + 1) := (clear_stretch_low hc (by omega)).mp c1
      have hr2 : r ≠ (A c).length + D + 2 := by
        intro e; apply c2; rw [← e]; exact (clear_stretch_low hc (le_refl r)).mpr hc
      have c2' : ¬ ClearCut D h A ((A c).length + D + 2) := fun hh =>
        c2 ((clear_stretch_low hc (by omega)).mpr hh)
      refine Or.inr ⟨c1', c2', ?_⟩
      have hcomm := stretch_comm c1' hc (by omega)
      rw [← hcomm] at ih
      have hr2c : ClearCut D (h + 2) (stretch A ((A c).length + D + 1)) (r + 2) :=
        (clear_stretch_high c1' (by omega)).mpr hc
      have hlenP := stretch_length c1' c
      rw [if_neg (by omega)] at hlenP
      rw [play_stretch hr2c] at ih
      exact (SEq.single (clear_play hr2c c p (Or.inl (by rw [hlenP]; omega)))).trans ih
  · -- column `c` passes through the cut
    rw [if_pos (by omega)] at hlenB
    have hsingle : SEq D h (play A c p) (h + 2) (play (stretch A r) c p) := by
      rw [play_stretch hc]
      exact SEq.single (clear_play hc c p (Or.inr (by omega)))
    rcases ih with ih | ⟨c1, c2, ih⟩
    · exact Or.inl (hsingle.trans ih)
    · rw [hlenB] at c1 c2 ih
      have e1 : (A c).length + 2 + D + 1 = (A c).length + D + 1 + 2 := by omega
      have e2 : (A c).length + 2 + D + 2 = (A c).length + D + 2 + 2 := by omega
      rw [e1] at c1 ih
      rw [e2] at c2
      have c1' : ClearCut D h A ((A c).length + D + 1) := (clear_stretch_high hc (by omega)).mp c1
      have c2' : ¬ ClearCut D h A ((A c).length + D + 2) := fun hh =>
        c2 ((clear_stretch_high hc (by omega)).mpr hh)
      refine Or.inr ⟨c1', c2', ?_⟩
      have hcomm := stretch_comm hc c1' (by omega)
      rw [hcomm] at ih
      have hrc : ClearCut D (h + 2) (stretch A ((A c).length + D + 1)) r :=
        (clear_stretch_low c1' (by omega)).mpr hc
      have hlenP := stretch_length c1' c
      rw [if_neg (by omega)] at hlenP
      rw [play_stretch hrc] at ih
      exact (SEq.single (clear_play hrc c p (Or.inr (by rw [hlenP]; omega)))).trans ih

/-- **Lemma B.** -/
theorem SEq.play {D h h' : Nat} {A R : Board w} (hs : SEq D h A h' R) (c : Fin w) (p : Player) :
    PlayRel D h A c p h' (play R c p) := by
  induction hs with
  | refl h A => exact Or.inl (SEq.refl _ _)
  | @step h A h' R r hc hrest ih =>
    by_cases hne : r = (A c).length + D + 1
    · by_cases hc' : ClearCut D h A (r + 1)
      · have e := stretch_succ hc hc'
        rw [e] at ih
        exact playRel_step hc' (by omega) ih
      · subst hne
        have hlenB := stretch_length hc c
        rw [if_neg (by omega)] at hlenB
        rcases ih with ih | ⟨c1, c2, ih⟩
        · exact Or.inr ⟨hc, hc', ih⟩
        · exfalso
          rw [hlenB] at c2
          exact c2 (clear_stretch_mid hc)
    · exact playRel_step hc hne ih

#print axioms SEq.play

end C4W5
