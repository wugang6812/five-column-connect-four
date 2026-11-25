import C4W5.Theory.Claim
import C4W5.Theory.StretchGame

/-!
# The claim criterion is invariant under stretching

`ClaimHyp h A q`: the hypotheses of `claim_safe` that do not follow from the course of the game.
If they hold for an abstract position, they hold for every stretch of it (`D ≥ 2`), so positions
satisfying the criterion can be used as leaves of stretch-game certificates.
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

structure ClaimHyp (h : Nat) (A : Board 5) (q : Fin 5) : Prop where
  even : h % 2 = 0
  valid : Valid h A
  odd : (h - (A q).length) % 2 = 1
  ntr : ∀ c, (A c).length < h → ¬ TopThree A c
  dead : ∀ c r, Exceptional A c r ∨ PotExc h A c r → LinesDead h A q (A q).length c r

theorem claimHyp_safe {H : Nat} {R : Board 5} {q : Fin 5} (hy : ClaimHyp H R q)
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black) :
    Safe H R :=
  claim_safe hy.even q htm hnw hnb hy.valid hy.odd hy.ntr hy.dead

/-- Every (potentially) exceptional cell of the stretched board comes from one of the original
board, either below the cut (same row) or above it (two rows lower). -/
theorem exc_stretch {D h r : Nat} {A : Board 5} (hD : 2 ≤ D) (hc : ClearCut D h A r) {c : Fin 5}
    {r' : Nat} (hcell : Exceptional (stretch A r) c r' ∨ PotExc (h + 2) (stretch A r) c r') :
    ∃ r0, (Exceptional A c r0 ∨ PotExc h A c r0) ∧
      ((r0 = r' ∧ r0 + D < r) ∨ (r' = r0 + 2 ∧ r + D < r0)) := by
  have hb := clearCut_bounds hc
  rcases top_of_clear hc c with hlow | hthr
  · -- the column does not reach the cut: unchanged
    have e : stretch A r c = A c := by
      simp only [stretch, colStretch]; rw [if_neg (by omega)]
    rcases hcell with hE | hP
    · rw [Exceptional, e] at hE
      have := stone_bound _ _ _ hE.1
      exact ⟨r', Or.inl hE, Or.inl ⟨rfl, by omega⟩⟩
    · rw [PotExc, e] at hP
      obtain ⟨h1, h2, h3⟩ := hP
      exact ⟨r', Or.inr ⟨h1, by omega, h3⟩, Or.inl ⟨rfl, by omega⟩⟩
  · have hst : ∀ n, stone (stretch A r c) n = stone (A c) (phi r n) :=
      fun n => stone_phi (A c) r n (by omega) (by omega)
    have hnd := not_defect_of_clear hc c
    have hlen : (stretch A r c).length = (A c).length + 2 := by
      rw [stretch_length hc, if_pos (by omega)]
    rcases hcell with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [hst] at h1
      rcases h2 with rfl | h2
      · rw [phi_lt (by omega)] at h1
        exact ⟨0, Or.inl ⟨h1, Or.inl rfl⟩, Or.inl ⟨rfl, by omega⟩⟩
      · rw [hst] at h2
        by_cases hr0 : r' = 0
        · subst hr0
          rw [phi_lt (by omega)] at h1
          exact ⟨0, Or.inl ⟨h1, Or.inl rfl⟩, Or.inl ⟨rfl, by omega⟩⟩
        have hcase : r' < r ∨ r' = r ∨ r' = r + 1 ∨ r' = r + 2 ∨ r + 3 ≤ r' := by omega
        rcases hcase with hlt | rfl | rfl | rfl | hge
        · rw [phi_lt hlt] at h1
          rw [phi_lt (by omega)] at h2
          have hdef : IsDefect (A c) r' := ⟨by omega, stone_bound _ _ _ h1, by rw [h1, h2]⟩
          have := hc.2 r' (Or.inr (Or.inr (Or.inr ⟨c, hdef⟩)))
          exact ⟨r', Or.inl ⟨h1, Or.inr h2⟩, Or.inl ⟨rfl, by omega⟩⟩
        · rw [phi_self] at h1
          rw [phi_lt (by omega)] at h2
          exact absurd ⟨by omega, by omega, by rw [h1, h2]⟩ hnd
        · rw [phi_succ] at h1
          have e : r + 1 - 1 = r := by omega
          rw [e, phi_self] at h2
          exact absurd ⟨by omega, by omega, by rw [h1, h2]⟩ hnd
        · rw [phi_gt (by omega)] at h1
          have e : r + 2 - 1 = r + 1 := by omega
          have e2 : r + 2 - 2 = r := by omega
          rw [e, phi_succ] at h2
          rw [e2] at h1
          exact absurd ⟨by omega, by omega, by rw [h1, h2]⟩ hnd
        · rw [phi_gt (by omega)] at h1 h2
          have e : r' - 1 - 2 = r' - 2 - 1 := by omega
          rw [e] at h2
          have hdef : IsDefect (A c) (r' - 2) := ⟨by omega, stone_bound _ _ _ h1, by rw [h1, h2]⟩
          have := hc.2 (r' - 2) (Or.inr (Or.inr (Or.inr ⟨c, hdef⟩)))
          exact ⟨r' - 2, Or.inl ⟨h1, Or.inr h2⟩, Or.inr ⟨by omega, by omega⟩⟩
    · rw [hlen] at h1 h2 h3
      refine ⟨(A c).length, Or.inr ⟨rfl, by omega, ?_⟩, Or.inr ⟨h1, hthr⟩⟩
      rcases h3 with h3 | h3
      · omega
      · right
        rw [hst, phi_gt (by omega)] at h3
        have e : (A c).length + 2 - 1 - 2 = (A c).length - 1 := by omega
        rw [e] at h3; exact h3

theorem linesDead_stretch_low {D h r : Nat} {A : Board 5} (hD : 2 ≤ D) (hc : ClearCut D h A r)
    {q c : Fin 5} {r0 : Nat} (hr : r0 + D < r)
    (hd : LinesDead h A q (A q).length c r0) :
    LinesDead (h + 2) (stretch A r) q (stretch A r q).length c r0 := by
  have hb := clearCut_bounds hc
  intro dy hdy i
  obtain ⟨j, hj⟩ := hd dy hdy i
  have hi := i.isLt
  have hjj := j.isLt
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
  refine ⟨j, ?_⟩
  rcases hj with hj | hj | hj
  · left
    rw [cell_low (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> omega)]; exact hj
  · right; left
    obtain ⟨h1, h2, h3⟩ := hj
    have hq : (stretch A r q).length = (A q).length := by
      rw [stretch_length hc]
      rcases top_of_clear hc q with hl | hl
      · rw [if_neg (by omega)]
      · exfalso; rcases hdy with rfl | rfl | rfl <;> omega
    rw [hq]; exact ⟨h1, h2, h3⟩
  · right; right
    rintro ⟨a1, a2, a3, a4⟩
    apply hj
    refine ⟨a1, a2, a3, ?_⟩
    rcases hdy with rfl | rfl | rfl <;> omega

theorem linesDead_stretch_high {D h r : Nat} {A : Board 5} (hD : 2 ≤ D) (hc : ClearCut D h A r)
    {q c : Fin 5} {r0 : Nat} (hr : r + D < r0)
    (hd : LinesDead h A q (A q).length c r0) :
    LinesDead (h + 2) (stretch A r) q (stretch A r q).length c (r0 + 2) := by
  have hb := clearCut_bounds hc
  intro dy hdy i
  obtain ⟨j, hj⟩ := hd dy hdy i
  have hi := i.isLt
  have hjj := j.isLt
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
  have e : (((r0 + 2 : Nat) : Int) - (i : Int) * dy + (j : Int) * dy) - 2 =
      (r0 : Int) - (i : Int) * dy + (j : Int) * dy := by
    push_cast; omega
  have hq : (stretch A r q).length = (A q).length ∨ (stretch A r q).length = (A q).length + 2 := by
    rw [stretch_length hc]
    by_cases hl : r < (A q).length
    · rw [if_pos hl]; exact Or.inr rfl
    · rw [if_neg hl]; exact Or.inl rfl
  refine ⟨j, ?_⟩
  rcases hj with hj | hj | hj
  · left
    rw [cell_high (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> push_cast <;> omega), e]
    exact hj
  · right; left
    obtain ⟨h1, h2, h3⟩ := hj
    refine ⟨h1, ?_, ?_⟩ <;> rcases hq with hq | hq <;> rw [hq] <;> push_cast <;> omega
  · right; right
    rintro ⟨a1, a2, a3, a4⟩
    apply hj
    refine ⟨a1, a2, ?_, ?_⟩ <;> rcases hdy with rfl | rfl | rfl <;> push_cast at a3 a4 ⊢ <;> omega

/-- **The claim criterion survives a stretch.** -/
theorem claimHyp_stretch {D h r : Nat} {A : Board 5} {q : Fin 5} (hD : 2 ≤ D)
    (hc : ClearCut D h A r) (hy : ClaimHyp h A q) : ClaimHyp (h + 2) (stretch A r) q := by
  have hb := clearCut_bounds hc
  have hlen : ∀ c, (stretch A r c).length =
      if r < (A c).length then (A c).length + 2 else (A c).length := stretch_length hc
  refine ⟨by have := hy.even; omega, ?_, ?_, ?_, ?_⟩
  · intro c
    have := hy.valid c
    rw [hlen]; split_ifs <;> omega
  · have := hy.valid q
    have := hy.odd
    rw [hlen]; split_ifs <;> omega
  · intro c hlt ht
    rcases top_of_clear hc c with hlow | hthr
    · have e : stretch A r c = A c := by
        simp only [stretch, colStretch]; rw [if_neg (by omega)]
      unfold TopThree at ht
      rw [e] at ht
      exact hy.ntr c (by omega) ht
    · have hst : ∀ n, stone (stretch A r c) n = stone (A c) (phi r n) :=
        fun n => stone_phi (A c) r n (by omega) (by omega)
      have hl : (stretch A r c).length = (A c).length + 2 := by rw [hlen, if_pos (by omega)]
      obtain ⟨-, t1, t2, t3⟩ := ht
      rw [hl, hst, phi_gt (by omega)] at t1 t2 t3
      rw [hl] at hlt
      apply hy.ntr c (by omega)
      refine ⟨by omega, ?_, ?_, ?_⟩
      · have e : (A c).length + 2 - 1 - 2 = (A c).length - 1 := by omega
        rw [e] at t1; exact t1
      · have e : (A c).length + 2 - 2 - 2 = (A c).length - 2 := by omega
        rw [e] at t2; exact t2
      · have e : (A c).length + 2 - 3 - 2 = (A c).length - 3 := by omega
        rw [e] at t3; exact t3
  · intro c r' hcell
    obtain ⟨r0, hcell0, ⟨rfl, hlo⟩ | ⟨rfl, hhi⟩⟩ := exc_stretch hD hc hcell
    · exact linesDead_stretch_low hD hc hlo (hy.dead c r0 hcell0)
    · exact linesDead_stretch_high hD hc hhi (hy.dead c r0 hcell0)

theorem claimHyp_seq {D : Nat} (hD : 2 ≤ D) {h H : Nat} {A R : Board 5} {q : Fin 5}
    (hs : SEq D h A H R) (hy : ClaimHyp h A q) : ClaimHyp H R q := by
  induction hs with
  | refl => exact hy
  | step r hc _ ih => exact ih (claimHyp_stretch hD hc hy)

/-- The leaf set of the claim criterion is sound for stretch-game certificates. -/
theorem claim_leafSound {D : Nat} (hD : 2 ≤ D) :
    LeafSound D (fun h A => ∃ q, ClaimHyp h A q) := by
  rintro h A H R ⟨q, hy⟩ hs htm hnw hnb
  exact claimHyp_safe (claimHyp_seq hD hs hy) htm hnw hnb

#print axioms claim_leafSound

end C4W5
