import LongThreatDefs

/-! Explicit target transport for the long odd-threat leaf. No game-value
    equivalence is used to identify the future winning square. -/
namespace C4W5.LongThreat
open Connect4 (Player opponent)
open Connect4.NarrowBoards
set_option linter.deprecated false

/-- The fixed target stays below the cut, otherwise rises by two. -/
def liftTarget (s rho : Nat) : Nat := if rho < s then rho else rho + 2

theorem threat_stretch {D H s rho : Nat} {A : Board 5} {t : Fin 5}
    (hD : 2 ≤ D) (hc : ClearCut D H A s) (ht : Threat H A t rho) :
    Threat (H + 2) (stretch A s) t (liftTarget s rho) := by
  obtain ⟨x, y, dy, i, hdy, hx, hy, hb⟩ := ht
  have hi := i.isLt
  have hdirs : dy = 0 ∨ dy = 1 ∨ dy = -1 := by simpa using hdy
  by_cases hs : rho < s
  · refine ⟨x, y, dy, i, hdy, hx, ?_, ?_⟩
    · simpa [liftTarget, hs] using hy
    · intro j hji
      have hj := j.isLt
      rw [cell_low (by omega) hc _ _ (by rcases hdirs with rfl | rfl | rfl <;> omega)]
      exact hb j hji
  · refine ⟨x, y + 2, dy, i, hdy, hx, ?_, ?_⟩
    · simp only [liftTarget, if_neg hs, Nat.cast_add, Nat.cast_ofNat]
      omega
    · intro j hji
      have hj := j.isLt
      rw [cell_high (by omega) hc _ _ (by rcases hdirs with rfl | rfl | rfl <;> omega)]
      have ee : y + 2 + (j : Int) * dy - 2 = y + (j : Int) * dy := by omega
      rw [ee]; exact hb j hji

/-- Low exceptional lines cannot lie above the old board top. At rho=s,
    the old cutoff cell is retained as a cover-Black cell, not a barrier. -/
theorem guard_stretch_low {D H s rho : Nat} {A : Board 5} {t : Fin 5}
    {Q : Fin 5 → Prop} (hD : 2 ≤ D) (hc : ClearCut D H A s)
    (hgt : (A t).length < rho) (hodd : (rho - (A t).length) % 2 = 1)
    {x y : Int} (hy : y ≤ (s : Int))
    (hg : Guard t rho Q (fun q => (A q).length) x y) :
    Guard t (liftTarget s rho) Q (fun q => (stretch A s q).length) x y := by
  rcases hg with ⟨q, hq, hx, hlt, hpar⟩ | ⟨hx, hbar⟩
  · left
    dsimp only at hlt hpar
    have he : (stretch A s q).length = (A q).length := by
      rw [stretch_length hc, if_neg (by omega)]
    exact ⟨q, hq, by simpa [Claimed, he] using (show Claimed q (A q).length x y from ⟨hx, hlt, hpar⟩)⟩
  · by_cases hs : rho < s
    · right; exact ⟨hx, by simpa [liftTarget, hs] using hbar⟩
    · have er : y = (rho : Int) := by omega
      have he : (stretch A s t).length = (A t).length := by
        rw [stretch_length hc, if_neg (by omega)]
      left
      refine ⟨t, Or.inl rfl, hx, ?_, ?_⟩
      · dsimp only; rw [he, er]; omega
      · dsimp only; rw [he, er]; omega

theorem guard_stretch_high {D H s rho : Nat} {A : Board 5} {t : Fin 5}
    {Q : Fin 5 → Prop} (hc : ClearCut D H A s) {x y : Int}
    (hg : Guard t rho Q (fun q => (A q).length) x y) :
    Guard t (liftTarget s rho) Q (fun q => (stretch A s q).length) x (y + 2) := by
  rcases hg with ⟨q, hq, hx, hlt, hpar⟩ | ⟨hx, hbar⟩
  · dsimp only at hlt hpar
    left; refine ⟨q, hq, hx, ?_, ?_⟩ <;> dsimp only <;> rw [stretch_length hc] <;> split_ifs <;> push_cast <;> omega
  · right; refine ⟨hx, ?_⟩
    unfold liftTarget; split_ifs <;> push_cast <;> omega

theorem dead_stretch_low {D H s rho : Nat} {A : Board 5} {t c : Fin 5}
    {Q : Fin 5 → Prop} {r0 : Nat} (hD : 2 ≤ D) (hc : ClearCut D H A s)
    (hgt : (A t).length < rho) (hodd : (rho - (A t).length) % 2 = 1)
    (hr : r0 + D < s) (hd : Dead H A t rho Q (fun q => (A q).length) c r0) :
    Dead (H + 2) (stretch A s) t (liftTarget s rho) Q
      (fun q => (stretch A s q).length) c r0 := by
  have hb := clearCut_bounds hc
  intro dy hdy i
  obtain ⟨j, hj⟩ := hd dy hdy i
  have hi := i.isLt
  have hjj := j.isLt
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
  dsimp only at hj ⊢
  refine ⟨j, ?_⟩
  rcases hj with hj | hj | hj
  · left
    rw [cell_low (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> omega)]
    exact hj
  · right; left
    exact guard_stretch_low hD hc hgt hodd
      (by rcases hdy with rfl | rfl | rfl <;> omega) hj
  · right; right
    rintro ⟨a1, a2, a3, a4⟩
    apply hj
    refine ⟨a1, a2, a3, ?_⟩
    rcases hdy with rfl | rfl | rfl <;> omega

theorem dead_stretch_high {D H s rho : Nat} {A : Board 5} {t c : Fin 5}
    {Q : Fin 5 → Prop} {r0 : Nat} (hD : 2 ≤ D) (hc : ClearCut D H A s)
    (hr : s + D < r0) (hd : Dead H A t rho Q (fun q => (A q).length) c r0) :
    Dead (H + 2) (stretch A s) t (liftTarget s rho) Q
      (fun q => (stretch A s q).length) c (r0 + 2) := by
  have hb := clearCut_bounds hc
  intro dy hdy i
  obtain ⟨j, hj⟩ := hd dy hdy i
  have hi := i.isLt
  have hjj := j.isLt
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
  dsimp only at hj ⊢
  have e : (((r0 + 2 : Nat) : Int) - (i : Int) * dy + (j : Int) * dy) =
      ((r0 : Int) - (i : Int) * dy + (j : Int) * dy) + 2 := by push_cast; omega
  refine ⟨j, ?_⟩
  rcases hj with hj | hj | hj
  · left
    rw [cell_high (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> push_cast <;> omega), e]
    simpa using hj
  · right; left
    rw [e]; exact guard_stretch_high hc hj
  · right; right
    rintro ⟨a1, a2, a3, a4⟩
    apply hj
    refine ⟨a1, a2, ?_, ?_⟩ <;> rcases hdy with rfl | rfl | rfl <;> push_cast at a3 a4 ⊢ <;> omega

/-- The explicit witness and all local hypotheses survive one clean cut. -/
theorem hyp_stretch {D H s rho : Nat} {A : Board 5} {t : Fin 5} {Q : Fin 5 → Prop}
    (hD : 2 ≤ D) (hc : ClearCut D H A s) (hy : Hyp H A t rho Q) :
    Hyp (H + 2) (stretch A s) t (liftTarget s rho) Q := by
  have hb := clearCut_bounds hc
  have hlen : ∀ c, (stretch A s c).length =
      if s < (A c).length then (A c).length + 2 else (A c).length := stretch_length hc
  have ht := hy.target_gt
  have htl := hy.target_lt
  have hto := hy.target_odd
  refine ⟨by have := hy.even; omega, ?_, hy.not_mem, ?_, ?_, ?_, ?_, ?_, ?_,
    threat_stretch hD hc hy.threat, ?_⟩
  · intro c; have := hy.valid c; rw [hlen]; split_ifs <;> omega
  · have := hy.valid t; have := hy.odd; rw [hlen]; split_ifs <;> omega
  · intro q hq; have := hy.valid q; have := hy.qpar q hq; rw [hlen]; split_ifs <;> omega
  · rw [hlen]; unfold liftTarget; split_ifs <;> omega
  · unfold liftTarget; split_ifs <;> omega
  · rw [hlen]; unfold liftTarget; split_ifs <;> omega
  · intro c hlt htop
    rcases top_of_clear hc c with hlow | hthr
    · have e : stretch A s c = A c := by
        simp only [stretch, colStretch]; rw [if_neg (by omega)]
      unfold TopThree at htop
      rw [e] at htop
      apply hy.ntr c (by show (A c).length < H; omega) htop
    · have hst : ∀ n, stone (stretch A s c) n = stone (A c) (phi s n) :=
        fun n => stone_phi (A c) s n (by omega) (by omega)
      have hl : (stretch A s c).length = (A c).length + 2 := by rw [hlen, if_pos (by omega)]
      obtain ⟨_, t1, t2, t3⟩ := htop
      rw [hl, hst, phi_gt (by omega)] at t1 t2 t3
      change (stretch A s c).length < H + 2 at hlt
      rw [hl] at hlt
      apply hy.ntr c (by show (A c).length < H; omega)
      refine ⟨by omega, ?_, ?_, ?_⟩
      · have e : (A c).length + 2 - 1 - 2 = (A c).length - 1 := by omega
        rw [e] at t1; exact t1
      · have e : (A c).length + 2 - 2 - 2 = (A c).length - 2 := by omega
        rw [e] at t2; exact t2
      · have e : (A c).length + 2 - 3 - 2 = (A c).length - 3 := by omega
        rw [e] at t3; exact t3
  · intro c r' hcell
    obtain ⟨r0, hcell0, ⟨rfl, hlo⟩ | ⟨rfl, hhi⟩⟩ := exc_stretch hD hc hcell
    · exact dead_stretch_low hD hc hy.target_gt hy.target_odd hlo (hy.dead c r0 hcell0)
    · exact dead_stretch_high hD hc hhi (hy.dead c r0 hcell0)

/-- Every SEq realization has a transported target witness. -/
theorem hyp_seq {D H H' rho : Nat} {A R : Board 5} {t : Fin 5} {Q : Fin 5 → Prop}
    (hD : 2 ≤ D) (hs : SEq D H A H' R) (hy : Hyp H A t rho Q) :
    ∃ rho', Hyp H' R t rho' Q := by
  induction hs generalizing rho with
  | refl => exact ⟨rho, hy⟩
  | step s hc _ ih => exact ih (hyp_stretch hD hc hy)

#print axioms hyp_stretch
#print axioms hyp_seq
end C4W5.LongThreat
