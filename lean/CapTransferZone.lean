import CapTransferStretch
import LongThreatZone

/-!
Source-only candidate; not compiled in this review.
A canonical CapTransfer.L certificate is sound as a terminal predicate for a
real Zone position. The transfer trigger is the cap at H, never the cutoff K.
-/
namespace C4W5.CapTransfer

open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-- Remove optional protected columns whose actual height is hidden. -/
def belowCut (K : Nat) (R : Board 5) (Q : Fin 5 → Prop) : Fin 5 → Prop :=
  fun q => Q q ∧ (trunc K R q).length < K

/-- All real exceptional and potential exceptional White cells are far enough
below the Zone cutoff, and are also exceptional in the truncated state. -/
theorem exception_to_trunc {K H : Nat} {R : Board 5} (hE : DiscE K R)
    (hT : ∀ c, TCol K H R c) {c : Fin 5} {r : Nat}
    (hcell : Exceptional R c r ∨ PotExc H R c r) :
    r + 4 ≤ K ∧ (Exceptional (trunc K R) c r ∨ PotExc K (trunc K R) c r) := by
  have hr : r + 4 ≤ K := by
    rcases hcell with h | ⟨rfl, hlt, htop⟩
    · exact hE c r h
    · exact hT c hlt htop
  refine ⟨hr, ?_⟩
  rcases hcell with ⟨h1, h2⟩ | ⟨rfl, hlt, htop⟩
  · left
    refine ⟨by simp only [trunc]; rw [stone_take _ _ _ (by omega)]; exact h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · right
      simp only [trunc]
      rw [stone_take _ _ _ (by omega)]
      exact h2
  · right
    have hlen : (trunc K R c).length = (R c).length := by rw [trunc_length]; omega
    refine ⟨hlen.symm, by omega, ?_⟩
    rw [hlen]
    rcases htop with h | h
    · exact Or.inl h
    · right
      simp only [trunc]
      rw [stone_take _ _ _ (by omega)]
      exact h

theorem line_y_below {K r : Nat} (hr : r + 4 ≤ K) {dy : Int}
    (hdy : dy ∈ ([0, 1, -1] : List Int)) (i j : Fin 4) :
    (r : Int) - (i : Int) * dy + (j : Int) * dy < (K : Int) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hdy
  rcases hdy with rfl | rfl | rfl <;> simp only [mul_zero, mul_one, mul_neg] <;> omega

theorem cap_zone_hyp {K H : Nat} {R : Board 5} {t s : Fin 5} {a b : Nat} {Q : Fin 5 → Prop}
    (hKH : K ≤ H) (hH : H % 2 = 0) (hv : Valid H R) (hE : DiscE K R)
    (hT : ∀ c, TCol K H R c) (hy : Hyp K (trunc K R) t s a b Q) :
    Hyp H R t s a b (belowCut K R Q) := by
  have tr_eq (c : Fin 5) (h : (trunc K R c).length < K) : trunc K R c = R c := by
    have hr : (R c).length ≤ K := by rw [trunc_length] at h; omega
    simp only [trunc]
    exact List.take_of_length_le hr
  have tlt : (trunc K R t).length < K := by
    have ht : (trunc K R t).length ≤ K := hy.valid t
    have ho := hy.oddT
    have he := hy.even
    omega
  have slt : (trunc K R s).length < K := lt_trans hy.above (lt_trans hy.order hy.below)
  have trT := tr_eq t tlt
  have trS := tr_eq s slt
  have liftB {x y : Int} (hx : cellAtInt K (trunc K R) x y = some .black) :
      cellAtInt H R x y = some .black := by
    rw [← cell_trunc hKH R _ _ (cell_trunc_some hx)]
    exact hx
  have liftThreat {rho : Nat} (ht : LongThreat.Threat K (trunc K R) s rho) :
      LongThreat.Threat H R s rho := by
    obtain ⟨x,y,dy,i,hdy,hx,hy',hall⟩ := ht
    exact ⟨x,y,dy,i,hdy,hx,hy',fun j hj => liftB (hall j hj)⟩
  have liftClaim {q : Fin 5} {x y : Int} (hyK : y < (K : Int))
      (hh : Claimed q (trunc K R q).length x y) :
      (trunc K R q).length < K ∧ Claimed q (R q).length x y := by
    have hh' : ((trunc K R q).length : Int) < y := hh.2.1
    have qK : (trunc K R q).length < K := by omega
    refine ⟨qK, ?_⟩
    rw [← tr_eq q qK]
    exact hh
  have carry {x y : Int} {P P' : Prop} (hyK : y < (K : Int))
      (hg : P → P')
      (h : cellAtInt K (trunc K R) x y = some .black ∨ P ∨
        ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (K : Int))) :
      cellAtInt H R x y = some .black ∨ P' ∨
        ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int)) := by
    rcases h with hb | hp | hn
    · exact Or.inl (liftB hb)
    · exact Or.inr (Or.inl (hg hp))
    · exact Or.inr (Or.inr (fun hh => hn ⟨hh.1, hh.2.1, hh.2.2.1, hyK⟩))
  have liftA (x y : Int) (hyK : y < (K : Int))
      (h : LongThreat.Guard s a (protect t Q) (fun q => (trunc K R q).length) x y) :
      LongThreat.Guard s a (protect t (belowCut K R Q)) (fun q => (R q).length) x y := by
    rcases h with ⟨q,hq,hc⟩ | hs
    · obtain ⟨hqK,hc'⟩ := liftClaim hyK hc
      refine Or.inl ⟨q, ?_, hc'⟩
      change q = s ∨ (q = t ∨ belowCut K R Q q)
      change q = s ∨ (q = t ∨ Q q) at hq
      rcases hq with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ⟨hh,hqK⟩)
    · exact Or.inr hs
  have liftPost (x y : Int) (hyK : y < (K : Int))
      (h : PostGuard t s a b Q (fun q => (trunc K R q).length) x y) :
      PostGuard t s a b (belowCut K R Q) (fun q => (R q).length) x y := by
    rcases h with ⟨q,hq,hc⟩ | hs
    · obtain ⟨hqK,hc'⟩ := liftClaim hyK hc
      refine Or.inl ⟨q, ?_, hc'⟩
      change q = t ∨ belowCut K R Q q
      change q = t ∨ Q q at hq
      exact hq.elim Or.inl (fun hh => Or.inr ⟨hh,hqK⟩)
    · exact Or.inr (by simpa only [trS] using hs)
  refine ⟨hH,hv,hy.distinct,fun h => hy.noT h.1,fun h => hy.noS h.1,
    ?_,?_,?_,?_,hy.order,lt_of_lt_of_le hy.below hKH,?_,?_,?_,
    liftThreat hy.threatA,liftThreat hy.threatB,?_,?_⟩
  · simpa only [trT] using hy.oddT
  · simpa only [trS] using hy.evenS
  · intro q hq
    simpa only [tr_eq q hq.2] using hy.evenQ q hq.1
  · simpa only [trS] using hy.above
  · simpa only [trS] using hy.oddA
  · simpa only [trS] using hy.evenB
  · intro c hl ht
    have he : Exceptional R c ((R c).length - 1) := by
      obtain ⟨h3, t1, t2, -⟩ := ht
      refine ⟨t1, Or.inr ?_⟩
      have ee : (R c).length - 1 - 1 = (R c).length - 2 := by omega
      rw [ee]
      exact t2
    have hlow := hE c _ he
    have hl3 := ht.1
    have eq : trunc K R c = R c := tr_eq c (by rw [trunc_length]; omega)
    apply hy.noTriple c (by show (trunc K R c).length < K; rw [eq]; omega)
    simpa only [TopThree, eq] using ht
  · intro c r hcell dy hdy i
    obtain ⟨hr, hk⟩ := exception_to_trunc hE hT hcell
    obtain ⟨j,hj⟩ := hy.deadA c r hk dy hdy i
    refine ⟨j, ?_⟩
    dsimp only at hj ⊢
    have hyK := line_y_below hr hdy i j
    simp only [mul_one] at hj ⊢
    exact carry hyK (liftA _ _ hyK) hj
  · intro c r hcell dy hdy i
    obtain ⟨hr, hk⟩ := exception_to_trunc hE hT hcell
    obtain ⟨j,hj⟩ := hy.deadB c r hk dy hdy i
    refine ⟨j, ?_⟩
    dsimp only at hj ⊢
    have hyK := line_y_below hr hdy i j
    simp only [mul_one] at hj ⊢
    exact carry hyK (liftPost _ _ hyK) hj

theorem cap_zone_leaf {K H : Nat} {R : Board 5} (hKH : K ≤ H) (hH : H % 2 = 0)
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black)
    (hv : Valid H R) (hE : DiscE K R) (hT : ∀ c, TCol K H R c)
    (hy : L K (trunc K R)) : Safe H R := by
  obtain ⟨t,s,a,b,Q,hh⟩ := hy
  exact hyp_safe (cap_zone_hyp hKH hH hv hE hT hh) htm hnw hnb

theorem cap_zone_seq {D k K : Nat} {A B : Board 5} (hD : 2 ≤ D)
    (hs : SEq D k A K B) (hy : L k A) : L K B := by
  obtain ⟨t,s,a,b,Q,hh⟩ := hy
  obtain ⟨a',b',hh'⟩ := hyp_seq hD hs hh
  exact ⟨t,s,a',b',Q,hh'⟩

end C4W5.CapTransfer
