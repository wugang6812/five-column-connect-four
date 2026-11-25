import LongThreatLeaf
import C4W5.Theory.ZoneL

namespace C4W5.LongThreat
open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-- In the zone form, every optional protected column must genuinely lie below the
    cut, so its even-capacity phase is known on the real board. -/
def ZHyp (K : Nat) (L : Board 5) : Prop :=
  ∃ t rho Q, Hyp K L t rho Q ∧ ∀ q, Q q → (L q).length < K

theorem zhyp_seq {D k K : Nat} (hD : 2 ≤ D) {A L : Board 5}
    (hs : SEq D k A K L) (hy : ZHyp k A) : ZHyp K L := by
  obtain ⟨t, rho, Q, h0, hq⟩ := hy
  obtain ⟨rho', h1⟩ := hyp_seq hD hs h0
  exact ⟨t, rho', Q, h1, fun q h => (hs.legal_iff q).mp (hq q h)⟩

theorem zone_hyp {K H : Nat} {R : Board 5} {t : Fin 5} {rho : Nat} {Q : Fin 5 → Prop}
    (hKH : K ≤ H) (hH : H % 2 = 0) (hv : Valid H R) (hE : DiscE K R)
    (hT : ∀ c, TCol K H R c) (hy : Hyp K (trunc K R) t rho Q)
    (hq : ∀ q, Q q → (trunc K R q).length < K) : Hyp H R t rho Q := by
  have tr_eq (c : Fin 5) (h : (trunc K R c).length < K) : trunc K R c = R c := by
    have hr : (R c).length ≤ K := by rw [trunc_length] at h; omega
    simp only [trunc]
    exact List.take_of_length_le hr
  have ht : trunc K R t = R t := tr_eq t (lt_trans hy.target_gt hy.target_lt)
  have gteq : ∀ c, (c = t ∨ Q c) → (trunc K R c).length = (R c).length := by
    intro c hc
    rcases hc with rfl | h
    · rw [ht]
    · rw [tr_eq c (hq c h)]
  refine ⟨hH, hv, hy.not_mem, ?_, ?_, ?_, lt_of_lt_of_le hy.target_lt hKH, ?_, ?_, ?_, ?_⟩
  · have h := hy.odd
    have hl := hy.target_gt
    have hk := hy.even
    rw [ht] at h hl
    have hr := hy.target_lt
    omega
  · intro q hq'
    have hlen := hq q hq'
    have h0 := hy.qpar q hq'
    rw [tr_eq q hlen] at h0 hlen
    have hk := hy.even
    omega
  · rw [← ht]
    exact hy.target_gt
  · rw [← ht]
    exact hy.target_odd
  · intro c hlt ht3
    have he : Exceptional R c ((R c).length - 1) := by
      obtain ⟨h3, t1, t2, -⟩ := ht3
      refine ⟨t1, Or.inr ?_⟩
      have e : (R c).length - 1 - 1 = (R c).length - 2 := by omega
      rw [e]; exact t2
    have hlow := hE c _ he
    have hl3 := ht3.1
    have etr : trunc K R c = R c := by
      simp only [trunc]; exact List.take_of_length_le (by omega)
    apply hy.ntr c (by unfold Legal; rw [etr]; omega)
    unfold TopThree
    rw [etr]; exact ht3
  · obtain ⟨x,y,dy,i,hdy,hx,hy',hall⟩ := hy.threat
    refine ⟨x,y,dy,i,hdy,hx,hy',?_⟩
    intro j hj
    have hblack := hall j hj
    rw [← cell_trunc hKH R _ _ (cell_trunc_some hblack)]
    exact hblack
  · intro c r hcell
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
    obtain ⟨j, hj | hj | hj⟩ := hy.dead c r hcellK dy hdy i
    · refine ⟨j, Or.inl ?_⟩
      rw [← cell_trunc hKH R _ _ (cell_trunc_some hj)]
      exact hj
    · refine ⟨j, Or.inr (Or.inl ?_)⟩
      rcases hj with ⟨q, hq', hc⟩ | hb
      · refine Or.inl ⟨q, hq', ?_⟩; simpa only [gteq q hq'] using hc
      · exact Or.inr hb
    · refine ⟨j, Or.inr (Or.inr ?_)⟩
      intro hin
      apply hj
      have hi := i.isLt
      have hjj := j.isLt
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
      rcases hdy with rfl | rfl | rfl <;> simp only [mul_zero, mul_one, mul_neg] at hin ⊢ <;> omega

theorem zone_leaf {K H : Nat} (hKH : K ≤ H) (hH : H % 2 = 0)
    {R : Board 5} (htm : toMove R = .white) (hnw : ¬ HasFour H R .white)
    (hnb : ¬ HasFour H R .black) (hv : Valid H R) (hE : DiscE K R)
    (hT : ∀ c, TCol K H R c) (hy : ZHyp K (trunc K R)) : Safe H R := by
  obtain ⟨t, rho, Q, h0, hq⟩ := hy
  exact hyp_safe (zone_hyp hKH hH hv hE hT h0 hq) htm hnw hnb

#print axioms C4W5.LongThreat.zone_hyp
#print axioms C4W5.LongThreat.zhyp_seq
#print axioms C4W5.LongThreat.zone_leaf
end C4W5.LongThreat
