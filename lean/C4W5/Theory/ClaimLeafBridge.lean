import C4W5.Theory.ZoneGen

/-!
# Truncation Lifting & Zone Leaf Bridge (`ClaimLeafBridge`)

Proves `deadSet_of_truncG` (lifting `LinesDeadSet` from bottom `K` rows `truncG K R`
to arbitrary height `H ≥ K` under `DiscEP` and `TColP`) and instantiates `ZoneLeafSound` for:
1. `claimOdd_zoneLeafSound`  — Odd-Empty Regime (`ClaimOddHyp`: Odd-H White, Even-H Black)
2. `claimEven_zoneLeafSound` — Even-Empty Regime (`ClaimEvenHyp`: Odd-H Black, Even-H White)

Zero `sorry`, zero custom axioms.
-/

namespace C4W5Gen
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5

set_option linter.deprecated false

/-- Lifting a single dead non-vertical line from `truncG K R` to `R` when its anchor row
    satisfies `r + 4 ≤ K` (so every cell of the 4-line has row `< K`) and claimed cells
    are monotonically preserved (`hQ`). -/
theorem lineOKSet_of_truncG {me : Player} {K H : Nat} (hKH : K ≤ H) {R : Board 5}
    {QK QH : Fin 5 → Bool} {hK hH : Fin 5 → Nat}
    (hQ : ∀ x y, ClaimedSet QK hK x y → ClaimedSet QH hH x y)
    {c : Fin 5} {r : Nat} (hr : r + 4 ≤ K) {dy : Int} (hdy : dy ∈ ([0, 1, -1] : List Int))
    (i : Fin 4)
    (hok : LineOKSet me K (truncG K R) QK hK ((c.val : Int) - (i : Int) * 1) ((r : Int) - (i : Int) * dy) dy) :
    LineOKSet me H R QH hH ((c.val : Int) - (i : Int) * 1) ((r : Int) - (i : Int) * dy) dy := by
  obtain ⟨j, hj | hj | hj⟩ := hok
  · refine ⟨j, Or.inl ?_⟩
    obtain ⟨_, _, _, hyK, _⟩ := cellAtInt_some hj
    rw [← cell_truncG hKH R _ _ hyK]; exact hj
  · exact ⟨j, Or.inr (Or.inl (hQ _ _ hj))⟩
  · refine ⟨j, Or.inr (Or.inr ?_)⟩
    intro hin
    apply hj
    have hi := i.isLt
    have hjj := j.isLt
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
    rcases hdy with rfl | rfl | rfl <;> simp only [mul_zero, mul_one, mul_neg] at hin ⊢ <;> omega

/-- Lifting `LinesDeadSet` over all `ExceptionalP ∨ PotExcP` cells from `truncG K R` to `R`. -/
theorem deadSet_of_truncG {me : Player} {K H : Nat} (hKH : K ≤ H) {R : Board 5}
    {QK QH : Fin 5 → Bool} {hK hH : Fin 5 → Nat}
    (hQ : ∀ x y, ClaimedSet QK hK x y → ClaimedSet QH hH x y)
    (hE : DiscEP (opponent me) K R) (hT : ∀ c, TColP (opponent me) K H R c)
    (hdead : ∀ c r, ExceptionalP (opponent me) (truncG K R) c r ∨
        PotExcP (opponent me) K (truncG K R) c r →
        LinesDeadSet me K (truncG K R) QK hK c r) :
    ∀ c r, ExceptionalP (opponent me) R c r ∨ PotExcP (opponent me) H R c r →
      LinesDeadSet me H R QH hH c r := by
  intro c r hcell
  have hr : r + 4 ≤ K := by
    rcases hcell with he | ⟨rfl, hlt, htop⟩
    · exact hE c r he
    · exact hT c hlt htop
  have hcellK : ExceptionalP (opponent me) (truncG K R) c r ∨
      PotExcP (opponent me) K (truncG K R) c r := by
    rcases hcell with ⟨hs, hbot⟩ | ⟨rfl, hlt, htop⟩
    · left
      refine ⟨by simp only [truncG]; rw [stone_take _ _ _ (by omega)]; exact hs, ?_⟩
      rcases hbot with hz | hp
      · exact Or.inl hz
      · right; simp only [truncG]; rw [stone_take _ _ _ (by omega)]; exact hp
    · right
      have hlen : (truncG K R c).length = (R c).length := by rw [truncG_length]; omega
      refine ⟨hlen.symm, by omega, ?_⟩
      rw [hlen]
      rcases htop with hz | hs
      · exact Or.inl hz
      · right; simp only [truncG]; rw [stone_take _ _ _ (by omega)]; exact hs
  intro dy hdy i
  exact lineOKSet_of_truncG hKH hQ hr hdy i (hdead c r hcellK dy hdy i)

/-- Helper: `TopThreeP` lifts from `truncG K R` to `R` under `DiscEP`. -/
theorem ntr_of_truncG {me : Player} {K H : Nat} {R : Board 5}
    (hE : DiscEP (opponent me) K R)
    (hntr : ∀ c, (truncG K R c).length < K → ¬ TopThreeP (opponent me) (truncG K R) c) :
    ∀ c, (R c).length < H → ¬ TopThreeP (opponent me) R c := by
  intro c _ ht
  have he : ExceptionalP (opponent me) R c ((R c).length - 1) := by
    obtain ⟨h3, t1, t2, -⟩ := ht
    refine ⟨t1, Or.inr ?_⟩
    have e : (R c).length - 1 - 1 = (R c).length - 2 := by omega
    rw [e]; exact t2
  have hlow := hE c _ he
  have h3 := ht.1
  have etr : truncG K R c = R c := by
    simp only [truncG]; exact List.take_of_length_le (by omega)
  apply hntr c (by rw [etr]; omega)
  unfold TopThreeP
  rw [etr]; exact ht

/-- **Bridge 1: `ClaimOddHyp` is a sound zone leaf (Odd-H White & Even-H Black).** -/
theorem claimOdd_zoneLeafSound (me : Player) :
    ZoneLeafSound me (fun K L => ∃ q : Fin 5, ClaimOddHyp me K L q) := by
  unfold ZoneLeafSound
  intro K H R hpar hKH htm hnopp hnme hv hE hT hleaf
  obtain ⟨q, hy⟩ := hleaf
  have hodd := hy.odd
  rw [truncG_length] at hodd
  have hq : (R q).length < K := by
    by_contra hcon
    rw [Nat.min_eq_left (by omega)] at hodd; omega
  rw [Nat.min_eq_right (by omega)] at hodd
  have htq : (truncG K R q).length = (R q).length := by rw [truncG_length]; omega
  have hregH : emptyParity H (opponent me) = 1 := by
    have hregK := hy.regime
    unfold emptyParity at hregK ⊢
    omega
  have hoddH : (H - (R q).length) % 2 = 1 := by omega
  have hQ : ∀ x y,
      ClaimedSet (fun d => decide (d = q)) (fun d => (truncG K R d).length) x y →
      ClaimedSet (fun d => decide (d = q)) (fun d => (R d).length) x y := by
    intro x y ⟨q', hq', hx, hgt, hp⟩
    dsimp only at hq' hx hgt hp
    simp only [decide_eq_true_eq] at hq'
    rw [hq'] at hx hgt hp
    rw [htq] at hgt hp
    exact ⟨q, by simp, hx, hgt, hp⟩
  exact claim_odd_safe
    ⟨hregH, hv, hoddH, ntr_of_truncG hE hy.ntr, deadSet_of_truncG hKH hQ hE hT hy.dead⟩
    htm hnopp hnme

/-- **Bridge 2: `ClaimEvenHyp` is a sound zone leaf (Odd-H Black & Even-H White).** -/
theorem claimEven_zoneLeafSound (me : Player) :
    ZoneLeafSound me (ClaimEvenHyp me) := by
  unfold ZoneLeafSound
  intro K H R hpar hKH htm hnopp hnme hv hE hT hy
  have hregH : emptyParity H (opponent me) = 0 := by
    have hregK := hy.regime
    unfold emptyParity at hregK ⊢
    omega
  have hQ : ∀ x y,
      ClaimedSet (evenCols K (truncG K R)) (fun d => (truncG K R d).length) x y →
      ClaimedSet (evenCols H R) (fun d => (R d).length) x y := by
    intro x y ⟨q, hq, hx, hgt, hp⟩
    dsimp only at hq hx hgt hp
    simp only [evenCols, decide_eq_true_eq] at hq
    obtain ⟨hltK, hevK⟩ := hq
    rw [truncG_length] at hltK
    have hltR : (R q).length < K := by omega
    have htq : (truncG K R q).length = (R q).length := by rw [truncG_length]; omega
    rw [htq] at hevK hgt hp
    refine ⟨q, ?_, hx, hgt, hp⟩
    simp only [evenCols, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩
  exact claim_even_safe
    ⟨hregH, hv, ntr_of_truncG hE hy.ntr, deadSet_of_truncG hKH hQ hE hT hy.dead⟩
    htm hnopp hnme

#print axioms claimOdd_zoneLeafSound
#print axioms claimEven_zoneLeafSound

end C4W5Gen
