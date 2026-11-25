import C4W5.Theory.StretchGame
import C4W5.Cert.Tree
import C4W5.Cert.ClaimC

/-!
# Kernel-checkable certificates for the stretch game — part 1: stretching positions
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- Stretch a black mask at level `r` (rows `r`, `r-1` are repeated above row `r`). -/
def strM (b r : Nat) : Nat :=
  (b % 2 ^ r) ||| (((b >>> r) % 2) <<< r) ||| (((b >>> (r - 1)) % 2) <<< (r + 1)) ||| ((b >>> r) <<< (r + 2))

theorem testBit_mod_two (x n : Nat) : (x % 2).testBit n = (decide (n = 0) && x.testBit 0) := by
  have : x % 2 = x % 2 ^ 1 := by simp
  rw [this, Nat.testBit_mod_two_pow]
  by_cases h : n = 0
  · subst h; simp
  · have : ¬ n < 1 := by omega
    simp [h, this]

theorem testBit_strM (b r n : Nat) (hr : 1 ≤ r) : (strM b r).testBit n = b.testBit (phi r n) := by
  unfold strM
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, testBit_mod_two,
    Nat.testBit_shiftRight]
  have hcase : n < r ∨ n = r ∨ n = r + 1 ∨ r + 2 ≤ n := by omega
  rcases hcase with h | h | h | h
  · rw [phi_lt h]
    simp [h, show ¬ r ≤ n by omega, show ¬ r + 1 ≤ n by omega, show ¬ r + 2 ≤ n by omega]
  · subst h
    rw [phi_self]
    simp [show ¬ n + 1 ≤ n by omega, show ¬ n + 2 ≤ n by omega]
  · subst h
    rw [phi_succ]
    simp [show ¬ r + 1 < r by omega, show ¬ r + 2 ≤ r + 1 by omega, show r - 1 + 0 = r - 1 by omega]
  · rw [phi_gt h]
    have e : r + (n - (r + 2)) = n - 2 := by omega
    simp [show ¬ n < r by omega, show n - r ≠ 0 by omega, show n - (r + 1) ≠ 0 by omega, h, e]

theorem strM_lt {b h r : Nat} (hb : b < 2 ^ h) (hr : 1 ≤ r) (hl : r < h) : strM b r < 2 ^ (h + 2) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_strM b r i hr, phi_gt (by omega)]
  exact testBit_false_of_lt hb (by omega)

theorem decC_strM {b h r : Nat} (hr : 1 ≤ r) (hl : r < h) :
    decC (h + 2) (strM b r) = colStretch (decC h b) r := by
  apply list_ext_stone
  intro n
  rw [stone_phi _ r n hr (by simpa using hl), stone_decC, stone_decC, testBit_strM b r n hr]
  have hcase : n < r ∨ n = r ∨ n = r + 1 ∨ r + 2 ≤ n := by omega
  rcases hcase with h1 | h1 | h1 | h1
  · rw [phi_lt h1, if_pos (by omega), if_pos (by omega)]
  · subst h1; rw [phi_self, if_pos (by omega), if_pos (by omega)]
  · subst h1; rw [phi_succ, if_pos (by omega), if_pos (by omega)]
  · rw [phi_gt h1]
    by_cases h2 : n < h + 2
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- Stretch one column. -/
def strCol (b h r : Nat) : Nat × Nat := if r < h then (strM b r, h + 2) else (b, h)

/-- Stretch a position at level `r`. -/
def stretchPos (p : Pos) (r : Nat) : Pos :=
  ⟨(strCol p.b0 p.h0 r).1, (strCol p.b1 p.h1 r).1, (strCol p.b2 p.h2 r).1, (strCol p.b3 p.h3 r).1,
   (strCol p.b4 p.h4 r).1, (strCol p.b0 p.h0 r).2, (strCol p.b1 p.h1 r).2, (strCol p.b2 p.h2 r).2,
   (strCol p.b3 p.h3 r).2, (strCol p.b4 p.h4 r).2⟩

theorem stretchPos_col (p : Pos) (r : Nat) (c : Fin 5) :
    (stretchPos p r).bm c.val = (strCol (p.bm c.val) (p.ht c.val) r).1 ∧
    (stretchPos p r).ht c.val = (strCol (p.bm c.val) (p.ht c.val) r).2 := by
  fin_cases c <;> exact ⟨rfl, rfl⟩

theorem stretchPos_toBoard (p : Pos) (r : Nat) (hr : 1 ≤ r) :
    (stretchPos p r).toBoard = stretch p.toBoard r := by
  funext c
  obtain ⟨e1, e2⟩ := stretchPos_col p r c
  simp only [Pos.toBoard, stretch]
  rw [e1, e2]
  unfold strCol
  by_cases hl : r < p.ht c.val
  · rw [if_pos hl]; exact decC_strM hr hl
  · rw [if_neg hl]; simp [colStretch, hl]

theorem stretchPos_WF {H : Nat} {p : Pos} (hw : p.WF H) (r : Nat) (hr : 1 ≤ r) :
    (stretchPos p r).WF (H + 2) := by
  have key : ∀ c : Fin 5, (stretchPos p r).bm c.val < 2 ^ (stretchPos p r).ht c.val ∧
      (stretchPos p r).ht c.val ≤ H + 2 := by
    intro c
    obtain ⟨e1, e2⟩ := stretchPos_col p r c
    rw [e1, e2]
    have hc := hw c.val
    unfold strCol
    by_cases hl : r < p.ht c.val
    · rw [if_pos hl]; exact ⟨strM_lt hc.1 hr hl, by omega⟩
    · rw [if_neg hl]; exact ⟨hc.1, by omega⟩
  intro d
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ 4 ≤ d) with rfl | rfl | rfl | rfl | h4
  · exact key 0
  · exact key 1
  · exact key 2
  · exact key 3
  · have : (stretchPos p r).bm d = (stretchPos p r).bm 4 ∧ (stretchPos p r).ht d = (stretchPos p r).ht 4 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 4 := ⟨d - 4, by omega⟩
      exact ⟨rfl, rfl⟩
    rw [this.1, this.2]; exact key 4

/-! ## Landmarks as a bit mask -/

/-- Defect levels of a column: bit `ℓ` is set iff rows `ℓ-1`, `ℓ` (0-based) carry the same colour. -/
def defM (b h : Nat) : Nat := ((2 ^ (h - 1) - 1) ^^^ ((b ^^^ (b >>> 1)) % 2 ^ (h - 1))) <<< 1

theorem bitP_inj {x y : Bool} : bitP x = bitP y ↔ x = y := by
  cases x <;> cases y <;> simp [bitP]

theorem defM_iff (b h ℓ : Nat) : (defM b h).testBit ℓ = true ↔ IsDefect (decC h b) ℓ := by
  unfold defM IsDefect
  rw [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_xor, Nat.testBit_shiftRight, decC_length, stone_decC, stone_decC]
  by_cases h1 : 1 ≤ ℓ
  · have e : 1 + (ℓ - 1) = ℓ := by omega
    rw [e]
    by_cases h2 : ℓ < h
    · rw [if_pos (by omega), if_pos h2]
      simp only [Option.some.injEq, bitP_inj]
      have h3 : ℓ - 1 < h - 1 := by omega
      cases hx : b.testBit (ℓ - 1) <;> cases hy : b.testBit ℓ <;> simp [h1, h2, h3]
    · have h3 : ¬ ℓ - 1 < h - 1 := by omega
      simp [h1, h2, h3]
  · simp [h1]

def colLM (b h : Nat) : Nat := 2 ^ h ||| defM b h

/-- Bit mask of the landmark levels. -/
def Pos.LM (H : Nat) (p : Pos) : Nat :=
  2 ^ 0 ||| 2 ^ H ||| colLM p.b0 p.h0 ||| colLM p.b1 p.h1 ||| colLM p.b2 p.h2 ||| colLM p.b3 p.h3 |||
    colLM p.b4 p.h4

theorem colLM_iff (p : Pos) (c : Fin 5) (ℓ : Nat) :
    (colLM (p.bm c.val) (p.ht c.val)).testBit ℓ = true ↔
      (p.toBoard c).length = ℓ ∨ IsDefect (p.toBoard c) ℓ := by
  unfold colLM
  rw [Nat.testBit_or, Bool.or_eq_true, defM_iff, Nat.testBit_two_pow, Pos.height]
  simp only [decide_eq_true_eq, Pos.toBoard]

theorem Pos.LM_iff (H : Nat) (p : Pos) (ℓ : Nat) :
    (p.LM H).testBit ℓ = true ↔ Landmark H p.toBoard ℓ := by
  unfold Pos.LM Landmark
  simp only [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq]
  have c0 : (colLM p.b0 p.h0).testBit ℓ = true ↔
      (p.toBoard 0).length = ℓ ∨ IsDefect (p.toBoard 0) ℓ := colLM_iff p 0 ℓ
  have c1 : (colLM p.b1 p.h1).testBit ℓ = true ↔
      (p.toBoard 1).length = ℓ ∨ IsDefect (p.toBoard 1) ℓ := colLM_iff p 1 ℓ
  have c2 : (colLM p.b2 p.h2).testBit ℓ = true ↔
      (p.toBoard 2).length = ℓ ∨ IsDefect (p.toBoard 2) ℓ := colLM_iff p 2 ℓ
  have c3 : (colLM p.b3 p.h3).testBit ℓ = true ↔
      (p.toBoard 3).length = ℓ ∨ IsDefect (p.toBoard 3) ℓ := colLM_iff p 3 ℓ
  have c4 : (colLM p.b4 p.h4).testBit ℓ = true ↔
      (p.toBoard 4).length = ℓ ∨ IsDefect (p.toBoard 4) ℓ := colLM_iff p 4 ℓ
  rw [c0, c1, c2, c3, c4]
  constructor
  · rintro ((((((h | h) | h) | h) | h) | h) | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · rcases h with h | h
      exacts [Or.inr (Or.inr (Or.inl ⟨0, h⟩)), Or.inr (Or.inr (Or.inr ⟨0, h⟩))]
    · rcases h with h | h
      exacts [Or.inr (Or.inr (Or.inl ⟨1, h⟩)), Or.inr (Or.inr (Or.inr ⟨1, h⟩))]
    · rcases h with h | h
      exacts [Or.inr (Or.inr (Or.inl ⟨2, h⟩)), Or.inr (Or.inr (Or.inr ⟨2, h⟩))]
    · rcases h with h | h
      exacts [Or.inr (Or.inr (Or.inl ⟨3, h⟩)), Or.inr (Or.inr (Or.inr ⟨3, h⟩))]
    · rcases h with h | h
      exacts [Or.inr (Or.inr (Or.inl ⟨4, h⟩)), Or.inr (Or.inr (Or.inr ⟨4, h⟩))]
  · rintro (h | h | ⟨c, h⟩ | ⟨c, h⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h.symm)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h.symm)))))
    · fin_cases c
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
    · fin_cases c
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr h)

/-- Is level `r` a clear cut? (`lm` is the landmark mask.) -/
def clearM (D H lm r : Nat) : Bool :=
  Nat.ble r H && Nat.blt D r && ((lm >>> (r - D)) % 2 ^ (2 * D + 1) == 0)

theorem clearM_iff (D H : Nat) (p : Pos) (r : Nat) :
    clearM D H (p.LM H) r = true ↔ ClearCut D H p.toBoard r := by
  unfold clearM ClearCut
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun ℓ hl => ?_⟩
    by_contra hcon
    have hbit := (p.LM_iff H ℓ).mpr hl
    have : ((p.LM H >>> (r - D)) % 2 ^ (2 * D + 1)).testBit (ℓ - (r - D)) = true := by
      rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      have e : r - D + (ℓ - (r - D)) = ℓ := by omega
      rw [e, hbit]; simp; omega
    rw [h3, Nat.zero_testBit] at this
    exact Bool.noConfusion this
  · rintro ⟨h1, h2⟩
    have h0 := h2 0 (Or.inl rfl)
    refine ⟨⟨h1, by omega⟩, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases hi : i < 2 * D + 1
    · cases hb : (p.LM H).testBit (r - D + i)
      · simp
      · have := h2 _ ((p.LM_iff H _).mp hb); omega
    · simp [hi]

/-! ## Variants, contraction, and the step check -/

theorem stretchPos_low (p : Pos) (r : Nat) (c : Fin 5) (hl : ¬ r < p.ht c.val) :
    (stretchPos p r).ht c.val = p.ht c.val := by
  rw [(stretchPos_col p r c).2]; unfold strCol; rw [if_neg hl]

/-- Base positions after a move of colour `pl` in column `c` (see `Variant`). -/
def varsF (D H : Nat) (p : Pos) (c : Nat) (pl : Player) : List (Nat × Pos) :=
  force (p.LM H) fun lm =>
  (H, p.push c pl) ::
    (if clearM D H lm (p.ht c + D + 1) && !clearM D H lm (p.ht c + D + 2) then
      [(H + 2, (stretchPos p (p.ht c + D + 1)).push c pl)]
    else [])

theorem vars_complete {D H : Nat} {p : Pos} (hw : p.WF H) (c : Fin 5) (pl : Player)
    (hl : p.ht c.val < H) {h₁ : Nat} {A₁ : Board 5} (hv : Variant D H p.toBoard c pl h₁ A₁) :
    ∃ v ∈ varsF D H p c.val pl, h₁ = v.1 ∧ A₁ = v.2.toBoard ∧ v.2.WF v.1 := by
  unfold varsF
  rw [force_eq]
  rcases hv with ⟨hh, hA⟩ | ⟨c1, c2, hh, hA⟩
  · exact ⟨(H, p.push c.val pl), by simp, hh, hA.trans (Pos.toBoard_push hw c pl).symm,
      Pos.WF_push hw c pl hl⟩
  · rw [Pos.height] at c1 c2
    have e1 := (clearM_iff D H p _).mpr c1
    have e2 : clearM D H (p.LM H) (p.ht c.val + D + 2) = false := by
      cases hh2 : clearM D H (p.LM H) (p.ht c.val + D + 2)
      · rfl
      · exact absurd ((clearM_iff D H p _).mp hh2) c2
    rw [e1, e2]
    have hws := stretchPos_WF hw (p.ht c.val + D + 1) (by omega)
    have hlow := stretchPos_low p (p.ht c.val + D + 1) c (by omega)
    refine ⟨(H + 2, (stretchPos p (p.ht c.val + D + 1)).push c.val pl), by simp, hh, ?_, ?_⟩
    · rw [hA, Pos.toBoard_push hws, stretchPos_toBoard _ _ (by omega), Pos.height]
    · exact Pos.WF_push hws c pl (by rw [hlow]; omega)

def unstrCol (b h r : Nat) : Nat × Nat :=
  if r + 2 < h then ((b % 2 ^ r) ||| ((b >>> (r + 2)) <<< r), h - 2) else (b, h)

def unstretchPos (p : Pos) (r : Nat) : Pos :=
  ⟨(unstrCol p.b0 p.h0 r).1, (unstrCol p.b1 p.h1 r).1, (unstrCol p.b2 p.h2 r).1, (unstrCol p.b3 p.h3 r).1,
   (unstrCol p.b4 p.h4 r).1, (unstrCol p.b0 p.h0 r).2, (unstrCol p.b1 p.h1 r).2, (unstrCol p.b2 p.h2 r).2,
   (unstrCol p.b3 p.h3 r).2, (unstrCol p.b4 p.h4 r).2⟩

/-- Try to contract two rows below the top of column `x`; the result is verified by stretching
back, so no property of `unstretchPos` is needed. -/
def normAt (D H : Nat) (p : Pos) (x : Nat) : Nat × Pos :=
  if D + 4 ≤ p.ht x ∧ 2 ≤ H then
    forceP (unstretchPos p (p.ht x - D - 3)) fun q =>
      if q.wfB (H - 2) && clearM D (H - 2) (q.LM (H - 2)) (p.ht x - D - 3) &&
          (stretchPos q (p.ht x - D - 3)).beq p then (H - 2, q) else (H, p)
  else (H, p)

theorem normAt_sound {D H : Nat} {p : Pos} (hw : p.WF H) (x : Nat) :
    (normAt D H p x).2.WF (normAt D H p x).1 ∧
      SEq D (normAt D H p x).1 (normAt D H p x).2.toBoard H p.toBoard := by
  unfold normAt
  by_cases h1 : D + 4 ≤ p.ht x ∧ 2 ≤ H
  · rw [if_pos h1, forceP_eq]
    by_cases h2 : ((unstretchPos p (p.ht x - D - 3)).wfB (H - 2) &&
        clearM D (H - 2) ((unstretchPos p (p.ht x - D - 3)).LM (H - 2)) (p.ht x - D - 3) &&
        (stretchPos (unstretchPos p (p.ht x - D - 3)) (p.ht x - D - 3)).beq p) = true
    · rw [if_pos h2]
      simp only [Bool.and_eq_true] at h2
      obtain ⟨⟨hwq, hcl⟩, hbeq⟩ := h2
      have heq := Pos.eq_of_beq hbeq
      refine ⟨Pos.wfB_sound hwq, ?_⟩
      have hc := (clearM_iff D (H - 2) _ _).mp hcl
      have hs := SEq.single hc
      rw [← stretchPos_toBoard _ _ (by omega), heq] at hs
      have e : H - 2 + 2 = H := by omega
      rw [e] at hs
      exact hs
    · rw [if_neg h2]; exact ⟨hw, SEq.refl _ _⟩
  · rw [if_neg h1]; exact ⟨hw, SEq.refl _ _⟩

/-- `normAt` in continuation-passing style, so that the kernel computes the contraction once. -/
def withNorm {α : Sort _} (D H : Nat) (p : Pos) (x : Nat) (k : Nat → Pos → α) : α :=
  if D + 4 ≤ p.ht x ∧ 2 ≤ H then
    forceP (unstretchPos p (p.ht x - D - 3)) fun q =>
      if q.wfB (H - 2) && clearM D (H - 2) (q.LM (H - 2)) (p.ht x - D - 3) &&
          (stretchPos q (p.ht x - D - 3)).beq p then k (H - 2) q else k H p
  else k H p

theorem withNorm_eq {α : Sort _} (D H : Nat) (p : Pos) (x : Nat) (k : Nat → Pos → α) :
    withNorm D H p x k = k (normAt D H p x).1 (normAt D H p x).2 := by
  unfold withNorm normAt
  by_cases h1 : D + 4 ≤ p.ht x ∧ 2 ≤ H
  · rw [if_pos h1, if_pos h1, forceP_eq, forceP_eq]
    by_cases h2 : ((unstretchPos p (p.ht x - D - 3)).wfB (H - 2) &&
        clearM D (H - 2) ((unstretchPos p (p.ht x - D - 3)).LM (H - 2)) (p.ht x - D - 3) &&
        (stretchPos (unstretchPos p (p.ht x - D - 3)) (p.ht x - D - 3)).beq p) = true
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h1, if_neg h1]

/-- The leaf set: abstract positions satisfying the claim criterion. -/
def CL (h : Nat) (A : Board 5) : Prop := ∃ q, ClaimHyp h A q

/-- Black's reply `e` from the (normalised) position after White's move.  The resulting position must
be a Black four, a member of the certificate, or a leaf (claim criterion). -/
def blackOK (D : Nat) (memf : Nat → Pos → Bool) (H₁ : Nat) (p₁ : Pos) (e : Nat) : Bool :=
  Nat.blt (p₁.ht e) H₁ &&
  (varsF D H₁ p₁ e .black).all fun v =>
    forceP v.2 fun p₂ => p₂.hasFourQ .black ||
      (withNorm D v.1 p₂ e fun H₃ p₃ => memf H₃ p₃ || claimB H₃ p₃)

/-- One variant of White's move in column `c`, with Black's recorded reply `e`. -/
def checkV (D : Nat) (memf : Nat → Pos → Bool) (c e : Nat) (v : Nat × Pos) : Bool :=
  forceP v.2 fun p₁ =>
    !p₁.hasFourQ .white &&
    (withNorm D v.1 p₁ c fun H₁ n₁ => n₁.fullF H₁ || blackOK D memf H₁ n₁ e)

def whiteOK (D : Nat) (memf : Nat → Pos → Bool) (H : Nat) (p : Pos) (rep c : Nat) : Bool :=
  if H ≤ p.ht c then true else
    force (p.LM H) fun lm =>
    checkV D memf c (replyOf rep (2 * c)) (H, p.push c .white) &&
    (if clearM D H lm (p.ht c + D + 1) && !clearM D H lm (p.ht c + D + 2) then
      checkV D memf c (replyOf rep (2 * c + 1)) (H + 2, (stretchPos p (p.ht c + D + 1)).push c .white)
    else true)

def stepOKS (D : Nat) (memf : Nat → Pos → Bool) (H : Nat) (p : Pos) (rep : Nat) : Bool :=
  p.wfB H && whiteOK D memf H p rep 0 && whiteOK D memf H p rep 1 && whiteOK D memf H p rep 2 &&
  whiteOK D memf H p rep 3 && whiteOK D memf H p rep 4

/-! ## Soundness -/

theorem variant_lift {D h' h : Nat} {A' A : Board 5} (s : SEq D h' A' h A) {e : Fin 5} {pl : Player}
    {h₂ : Nat} {A₂ : Board 5} (hv : Variant D h A e pl h₂ A₂) :
    ∃ h₂' B₂, Variant D h' A' e pl h₂' B₂ ∧ SEq D h₂' B₂ h₂ A₂ := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨c1, -, rfl, rfl⟩
  · exact exists_variant s e pl
  · exact exists_variant (s.trans (SEq.single c1)) e pl

section
variable {D : Nat} {I : Nat → Board 5 → Prop} {memf : Nat → Pos → Bool}

theorem blackOK_sound (hm : ∀ h q, memf h q = true → I h q.toBoard) {H₁ : Nat} {p₁ : Pos}
    (hw : p₁.WF H₁) (e : Fin 5) (hb : blackOK D memf H₁ p₁ e.val = true) :
    Legal H₁ p₁.toBoard e ∧ ∀ h₂ A₂, Variant D H₁ p₁.toBoard e .black h₂ A₂ →
      HasFour h₂ A₂ .black ∨ ∃ h₃ A₃, (I h₃ A₃ ∨ CL h₃ A₃) ∧ SEq D h₃ A₃ h₂ A₂ := by
  unfold blackOK at hb
  simp only [Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, forceP_eq, withNorm_eq, Bool.or_eq_true] at hb
  obtain ⟨hlt, hall⟩ := hb
  refine ⟨by show (p₁.toBoard e).length < H₁; rw [Pos.height]; exact hlt, ?_⟩
  intro h₂ A₂ hv
  obtain ⟨v, hmem, rfl, rfl, hwv⟩ := vars_complete hw e .black hlt hv
  rcases hall v hmem with hwin | hin
  · left
    rw [Pos.hasFourQ_eq] at hwin
    exact (hasFourF_iff hwv _).mp hwin
  · right
    obtain ⟨-, hs⟩ := normAt_sound (D := D) hwv e.val
    rcases hin with hin | hin
    · exact ⟨_, _, Or.inl (hm _ _ hin), hs⟩
    · exact ⟨_, _, Or.inr (claimB_sound hin), hs⟩

theorem checkV_sound (hD : 2 ≤ D) (hm : ∀ h q, memf h q = true → I h q.toBoard) (c : Nat) (e : Fin 5)
    {v : Nat × Pos} (hwv : v.2.WF v.1) (hc : checkV D memf c e.val v = true) :
    ¬ HasFour v.1 v.2.toBoard .white ∧
    (BoardFull v.1 v.2.toBoard ∨ ∃ e', Legal v.1 v.2.toBoard e' ∧ ∀ h₂ A₂,
      Variant D v.1 v.2.toBoard e' .black h₂ A₂ →
        HasFour h₂ A₂ .black ∨ ∃ h₃ A₃, (I h₃ A₃ ∨ CL h₃ A₃) ∧ SEq D h₃ A₃ h₂ A₂) := by
  unfold checkV at hc
  simp only [forceP_eq, withNorm_eq, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Pos.hasFourQ_eq] at hc
  obtain ⟨hnf, hrest⟩ := hc
  obtain ⟨hwn, hs⟩ := normAt_sound (D := D) hwv c
  refine ⟨?_, ?_⟩
  · intro hf
    rw [← hasFourF_iff hwv, hnf] at hf; exact Bool.noConfusion hf
  · rcases hrest with hfull | hb
    · exact Or.inl (hs.full_iff.mp (Pos.fullF_sound hfull))
    · right
      obtain ⟨hleg, hvar⟩ := blackOK_sound hm hwn e hb
      refine ⟨e, (hs.legal_iff e).mp hleg, fun h₂ A₂ hv => ?_⟩
      obtain ⟨h₂', B₂, hv', s2⟩ := variant_lift hs hv
      rcases hvar h₂' B₂ hv' with hwin | ⟨h₃, A₃, hI, s3⟩
      · exact Or.inl ((s2.hasFour_iff hD _).mp hwin)
      · exact Or.inr ⟨h₃, A₃, hI, s3.trans s2⟩

theorem whiteOK_sound (hD : 2 ≤ D) (hm : ∀ h q, memf h q = true → I h q.toBoard) {H : Nat} {p : Pos}
    (hw : p.WF H) {rep : Nat} (c : Fin 5) (hok : whiteOK D memf H p rep c.val = true)
    (hl : Legal H p.toBoard c) {h₁ : Nat} {A₁ : Board 5} (hv : Variant D H p.toBoard c .white h₁ A₁) :
    ¬ HasFour h₁ A₁ .white ∧
    (BoardFull h₁ A₁ ∨ ∃ e, Legal h₁ A₁ e ∧ ∀ h₂ A₂, Variant D h₁ A₁ e .black h₂ A₂ →
      HasFour h₂ A₂ .black ∨ ∃ h₃ A₃, (I h₃ A₃ ∨ CL h₃ A₃) ∧ SEq D h₃ A₃ h₂ A₂) := by
  have hlt : p.ht c.val < H := by have : (p.toBoard c).length < H := hl; rwa [Pos.height] at this
  obtain ⟨v, hmem, rfl, rfl, hwv⟩ := vars_complete hw c .white hlt hv
  unfold whiteOK at hok
  rw [if_neg (by omega), force_eq, Bool.and_eq_true] at hok
  obtain ⟨hok0, hok1⟩ := hok
  unfold varsF at hmem
  rw [force_eq] at hmem
  have key : ∃ e : Fin 5, checkV D memf c.val e.val v = true := by
    by_cases hcrit : (clearM D H (p.LM H) (p.ht c.val + D + 1) &&
        !clearM D H (p.LM H) (p.ht c.val + D + 2)) = true
    · rw [if_pos hcrit] at hmem hok1
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨⟨replyOf rep (2 * c.val), Nat.mod_lt _ (by decide)⟩, hok0⟩
      · exact ⟨⟨replyOf rep (2 * c.val + 1), Nat.mod_lt _ (by decide)⟩, hok1⟩
    · rw [if_neg hcrit] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact ⟨⟨replyOf rep (2 * c.val), Nat.mod_lt _ (by decide)⟩, hok0⟩
  obtain ⟨e, he⟩ := key
  exact checkV_sound hD hm c.val e hwv he

end

end C4W5
