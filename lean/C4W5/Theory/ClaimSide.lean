import C4W5.Theory.Claim
import C4W5.Cert.Tree

/-!
# The side branches T(1,b)·Wq·B4 (b ≥ 3) by the claim criterion

The claimed column is the fourth one (height 1).  All exceptional and potentially exceptional cells lie
in rows `≤ 4`, so the hypotheses of `claim_safe` only concern the bottom 8 rows, where the board is one
of two concrete boards (`b = 3`, `b ≥ 4`); those are checked by `decide`.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-! ## Reduction of the dead-line hypothesis to the bottom `K` rows -/

theorem lineOK_of_trunc {K H : Nat} (hKH : K ≤ H) {R : Board 5} {q : Fin 5} {h0 : Nat} {c : Fin 5}
    {r : Nat} (hr : r + 4 ≤ K) {dy : Int} (hdy : dy ∈ ([0, 1, -1] : List Int)) (i : Fin 4)
    (h : LineOK K (trunc K R) q h0 ((c.val : Int) - (i : Int) * 1) ((r : Int) - (i : Int) * dy) dy) :
    LineOK H R q h0 ((c.val : Int) - (i : Int) * 1) ((r : Int) - (i : Int) * dy) dy := by
  obtain ⟨j, hj | hj | hj⟩ := h
  · refine ⟨j, Or.inl ?_⟩
    rw [← cell_trunc hKH R _ _ (cell_trunc_some hj)]; exact hj
  · exact ⟨j, Or.inr (Or.inl hj)⟩
  · refine ⟨j, Or.inr (Or.inr ?_)⟩
    intro hin
    apply hj
    have hi := i.isLt
    have hjj := j.isLt
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
    rcases hdy with rfl | rfl | rfl <;> simp only [mul_zero, mul_one, mul_neg] at hin ⊢ <;> omega

theorem dead_of_trunc {K H : Nat} (hKH : K ≤ H) {R : Board 5} {q : Fin 5} {h0 : Nat}
    (hE : DiscE K R) (hT : ∀ c, TCol K H R c)
    (hdK : ∀ (c : Fin 5) (r : Nat), r + 4 ≤ K →
      Exceptional (trunc K R) c r ∨ PotExc K (trunc K R) c r → LinesDead K (trunc K R) q h0 c r) :
    ∀ c r, Exceptional R c r ∨ PotExc H R c r → LinesDead H R q h0 c r := by
  intro c r hcell
  have hr : r + 4 ≤ K := by
    rcases hcell with h | ⟨rfl, hlt, htop⟩
    · exact hE c r h
    · exact hT c hlt htop
  have hcellK : Exceptional (trunc K R) c r ∨ PotExc K (trunc K R) c r := by
    rcases hcell with ⟨h1, h2⟩ | ⟨rfl, hlt, htop⟩
    · left
      refine ⟨by simp only [trunc]; rw [stone_take _ _ _ (by omega)]; exact h1, ?_⟩
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · right; simp only [trunc]; rw [stone_take _ _ _ (by omega)]; exact h2
    · right
      have hlen : (trunc K R c).length = (R c).length := by rw [trunc_length]; omega
      refine ⟨hlen.symm, by omega, ?_⟩
      rw [hlen]
      rcases htop with h | h
      · exact Or.inl h
      · right; simp only [trunc]; rw [stone_take _ _ _ (by omega)]; exact h
  intro dy hdy i
  exact lineOK_of_trunc hKH hr hdy i (hdK c r hr hcellK dy hdy i)

/-! ## Decidability of the finite part -/

instance (b : Board 5) (c : Fin 5) (r : Nat) : Decidable (Exceptional b c r) := by
  unfold Exceptional; infer_instance
instance (H : Nat) (b : Board 5) (c : Fin 5) (r : Nat) : Decidable (PotExc H b c r) := by
  unfold PotExc; infer_instance
instance (H : Nat) (R : Board 5) (q : Fin 5) (h0 : Nat) (x y dy : Int) :
    Decidable (LineOK H R q h0 x y dy) := by
  unfold LineOK; infer_instance
instance (H : Nat) (R : Board 5) (q : Fin 5) (h0 : Nat) (c : Fin 5) (r : Nat) :
    Decidable (LinesDead H R q h0 c r) := by
  unfold LinesDead; infer_instance

/-- The decidable form of the dead-line hypothesis on the bottom 8 rows. -/
def DeadK8 (R : Board 5) (q : Fin 5) (h0 : Nat) : Prop :=
  ∀ (c : Fin 5) (r : Fin 5), Exceptional R c r.val ∨ PotExc 8 R c r.val → LinesDead 8 R q h0 c r.val

instance (R : Board 5) (q : Fin 5) (h0 : Nat) : Decidable (DeadK8 R q h0) := by
  unfold DeadK8; infer_instance

/-! ## The wall -/

theorem stone_wb : ∀ (b r : Nat), stone (wb b) r =
    if r < 2 * b then some (if r % 2 = 0 then Player.white else Player.black) else none
  | 0, r => by simp [wb, stone]
  | b + 1, 0 => by rw [if_pos (by omega)]; rfl
  | b + 1, 1 => by rw [if_pos (by omega)]; rfl
  | b + 1, r + 2 => by
    simp only [wb, stone]
    rw [stone_wb b r]
    by_cases h : r < 2 * b
    · have h2 : r + 2 < 2 * (b + 1) := by omega
      rw [if_pos h, if_pos h2]
      have : (r + 2) % 2 = r % 2 := by omega
      rw [this]
    · have h2 : ¬ r + 2 < 2 * (b + 1) := by omega
      rw [if_neg h, if_neg h2]

theorem wb_white {b r : Nat} (h : stone (wb b) r = some .white) : r % 2 = 0 := by
  rw [stone_wb] at h
  by_cases h1 : r < 2 * b
  · rw [if_pos h1] at h
    by_contra h2
    rw [if_neg h2] at h; cases h
  · rw [if_neg h1] at h; cases h

theorem wb_black {b r : Nat} (h : stone (wb b) r = some .black) : r % 2 = 1 := by
  rw [stone_wb] at h
  by_cases h1 : r < 2 * b
  · rw [if_pos h1] at h
    by_contra h2
    have h3 : r % 2 = 0 := by omega
    rw [if_pos h3] at h; cases h
  · rw [if_neg h1] at h; cases h

theorem take8_wb : ∀ b : Nat, 4 ≤ b → (wb b).take 8 = wb 4
  | b + 4, _ => by simp [wb]

theorem take_short (l : List Player) (h : l.length ≤ 8) : l.take 8 = l := List.take_of_length_le h

end C4W5
