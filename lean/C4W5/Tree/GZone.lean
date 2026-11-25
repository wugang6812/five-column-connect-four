import C4W5.Tree.GFam
import C4W5.Cert.StretchZoneTree

/-!
# G(b), b ≥ 5, on heights H ≥ 2b+6: zone game with K = 2b+4, modulo stretching

One certificate (root G(5) with K = 14) covers every b ≥ 5 and every even H ≥ 2b+6.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- A four only uses occupied cells, so the board height does not matter above the columns. -/
theorem hasFour_lower {K H : Nat} {R : Board 5} {p : Player} (hlen : ∀ c, (R c).length ≤ K)
    (hf : HasFour H R p) : HasFour K R p := by
  obtain ⟨d, hd, x, y, hdir⟩ := exists_dir hf
  apply hasFour_of_dir d hd (x := x) (y := y)
  intro i
  obtain ⟨c, hx, hy0, -, hs⟩ := cellAtInt_some (hdir i)
  have := stone_bound _ _ _ hs
  have := hlen c
  rw [hx, cellAtInt_fin _ c _ hy0 (by omega)]
  exact hs

theorem trunc_short {K : Nat} {R : Board 5} (hlen : ∀ c, (R c).length ≤ K) : trunc K R = R := by
  funext c; simp only [trunc]; exact List.take_of_length_le (hlen c)

theorem G_discE (b K : Nat) (hK : 7 ≤ K) : DiscE K (G b) := by
  intro x r hx
  obtain rfl | rfl | rfl | rfl | rfl := fin5_cases x
  · have := stone_bound _ _ _ hx.1; simp [G] at this
  · obtain ⟨h1, h2⟩ := hx
    simp only [G, ofCols_1] at h1 h2
    have w1 : ∀ n, stone (wb b ++ [Player.black]) n = some .white → n < 2 * b ∧ n % 2 = 0 := by
      intro n hn
      rw [stone_app, wb_length] at hn
      by_cases hlt : n < 2 * b
      · rw [if_pos hlt] at hn; exact ⟨hlt, wb_white hn⟩
      · rw [if_neg hlt] at hn
        have hb := stone_bound _ _ _ hn
        simp at hb
        have e : n - 2 * b = 0 := by omega
        rw [e] at hn; simp [stone] at hn
    rcases h2 with rfl | h2
    · omega
    · have a1 := w1 r h1; have a2 := w1 (r - 1) h2; omega
  · have := stone_bound _ _ _ hx.1; simp [G, centre] at this; omega
  · have := stone_bound _ _ _ hx.1; simp [G] at this; omega
  · have := stone_bound _ _ _ hx.1; simp [G] at this

theorem G_tcol (b K H : Nat) (hb : 1 ≤ b) (hK : 7 ≤ K) (c : Fin 5) : TCol K H (G b) c := by
  intro _ htop
  obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c
  · simp [G]; omega
  · exfalso
    simp only [G, ofCols_1, List.length_append, wb_length, List.length_cons, List.length_nil] at htop
    rcases htop with h | h
    · omega
    · rw [stone_app, wb_length, if_neg (by omega)] at h
      have e : 2 * b + (0 + 1) - 1 - 2 * b = 0 := by omega
      rw [e] at h; simp [stone] at h
  · simp [G, centre]; omega
  · simp [G]; omega
  · simp [G]; omega

theorem g5_zone_of_tree (t : CTree) (ok : t.szallOK 2 t.szmemB = true)
    (root : t.szmemB 14 g5p ⟨0, 0, 0, 0, 0⟩ = true) (m b : Nat) (hb : 5 ≤ b) (hbm : b + 3 ≤ m) :
    Safe (2 * m) (G b) := by
  have hlen : ∀ c, (G b c).length ≤ 2 * b + 4 := fun c => by
    have := G_len b (by omega) c; omega
  have hq : g5p.toBoard = G 5 := by
    funext c; obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  have hs : SEq 2 14 g5p.toBoard (2 * b + 4) (trunc (2 * b + 4) (G b)) := by
    rw [trunc_short hlen, hq]; exact seq_G_wall 4 (by omega) b hb
  have hs' : SEq 2 14 (G 5) (2 * b + 4) (G b) := seq_G_wall 4 (by omega) b hb
  have nf : ∀ p, ¬ HasFour 14 (G 5) p := by
    intro p hf
    rw [← G5_play] at hf
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
      (show (Pos.run 14 Pos.empty .black [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1]).isSome = true by decide)
    obtain ⟨e, hw, hb', -⟩ := root_of_run' hq
    rw [← e] at hf
    cases p
    · exact hb' hf
    · exact hw hf
  have nfb : ∀ p, ¬ HasFour (2 * m) (G b) p := fun p hf =>
    nf p ((hs'.hasFour_iff (by omega) p).mpr (hasFour_lower hlen hf))
  have hlab : (⟨0, 0, 0, 0, 0⟩ : Lab5).fn = labs (2 * m) (2 * b + 4) (G b) := by
    funext c
    have := hlen c
    simp only [labs, labOf]
    rw [if_pos this]
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  exact sz_safe_of_tree (by omega) t ok (by omega) (by omega) (by omega) (toMove_G b)
    (nfb .white) (nfb .black) (G_discE b _ (by omega)) (G_tcol b _ _ (by omega) (by omega))
    (fun c => by have := hlen c; omega) root hlab hs

end C4W5
