import C4W5.Theory.Zone
import C4W5.Theory.ClaimSide
import C4W5.Theory.ClaimStretch

/-!
# The zone theorem with leaves

`ZoneCert2 K I J`: from a state in `I`, the zone game leads to states in `J`.  With
`J = I ∪ {claim-criterion leaves}` Black is safe (`zone_safeL`).  `Theory/Zone.lean` is left untouched
(the proof of `zone_step2` is that of `zone_step` with the target set generalised).
-/

namespace C4W5
open Connect4 (Player opponent)
open Connect4.NarrowBoards

set_option linter.deprecated false

/-- Two-ply invariant principle where Black's reply may also lead to a position known to be safe. -/
theorem safe_of_inv2L {H : Nat} (Inv : Board 5 → Prop)
    (h0 : ∀ R, Inv R → toMove R = .white ∧ ¬ HasFour H R .white)
    (hstep : ∀ R, Inv R → ∀ c, Legal H R c →
      ¬ HasFour H (play R c .white) .white ∧
      (BoardFull H (play R c .white) ∨ ∃ e, Legal H (play R c .white) e ∧
        (HasFour H (play (play R c .white) e .black) .black ∨ Inv (play (play R c .white) e .black) ∨
          Safe H (play (play R c .white) e .black)))) :
    ∀ R, Inv R → Safe H R := by
  have key : ∀ k R, Inv R → SafeFor H .black k R := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro R hR
      obtain ⟨htm, hnw⟩ := h0 R hR
      cases k with
      | zero => exact hnw
      | succ k =>
        refine ⟨hnw, Or.inr (Or.inr ?_)⟩
        have hne : ¬ toMove R = .black := by rw [htm]; decide
        rw [if_neg hne, htm]
        intro c hc
        obtain ⟨hnw1, hrest⟩ := hstep R hR c hc
        cases k with
        | zero => exact hnw1
        | succ k =>
          refine ⟨hnw1, ?_⟩
          rcases hrest with hfull | ⟨e, he, hout⟩
          · exact Or.inr (Or.inl hfull)
          · refine Or.inr (Or.inr ?_)
            have htb : toMove (play R c .white) = .black := toMove_play_white htm c
            rw [if_pos htb, htb]
            refine ⟨e, he, ?_⟩
            have hnw2 : ¬ HasFour H (play (play R c .white) e .black) .white :=
              fun hf => hnw1 (hasFour_play_other (by decide) hf)
            rcases hout with hwin | hinv | hsafe
            · exact safeFor_of_blackFour hnw2 hwin k
            · exact ih k (by omega) _ hinv
            · exact hsafe k
  exact fun R hR k => key k R hR

/-- Closure condition of the zone game from `I` into `J`. -/
def ZoneCert2 (K : Nat) (I J : Board 5 → (Fin 5 → Lab) → Prop) : Prop :=
  ∀ L ℓ, I L ℓ → ∀ c : Fin 5,
    (ℓ c = .low → (L c).length < K →
      ¬ HasFour K (play L c .white) .white ∧
      (BlackWin K (play L c .white) ℓ ∨
        ∃ e, (e = c ∨ (L c).length + 5 ≤ K) ∧ BlackOut K J (play L c .white) ℓ e)) ∧
    (ℓ c = .low → (L c).length = K → J L (Function.update ℓ c .dead)) ∧
    (ℓ c = .odd → (∀ d, Function.update ℓ c .dead d = .dead) ∨ BlackWin K L (Function.update ℓ c .dead) ∨
      ∃ e, BlackOut K J L (Function.update ℓ c .dead) e)

/-- One round of the real game: from the invariant for `I` to the invariant for `J`. -/
theorem zone_step2 {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    {I J : Board 5 → (Fin 5 → Lab) → Prop} (hIJ : ∀ L ℓ, I L ℓ → J L ℓ) (hI : ZoneCert2 K I J)
    {R : Board 5} (inv : ZInv K H I R) (c : Fin 5) (hc : Legal H R c) :
    ¬ HasFour H (play R c .white) .white ∧
    (BoardFull H (play R c .white) ∨ ∃ e, Legal H (play R c .white) e ∧
      (HasFour H (play (play R c .white) e .black) .black ∨
        ZInv K H J (play (play R c .white) e .black))) := by
  have hcl : (R c).length < H := hc
  have hE1 : DiscE K (play R c .white) := discE_play_white inv.dE c (inv.dT c) hc
  have hnb1 : ¬ HasFour H (play R c .white) .black := fun hf => inv.nb (hasFour_play_other (by decide) hf)
  have hv1 : Valid H (play R c .white) := play_valid inv.valid hc
  have nwOf : ¬ HasFour K (trunc K (play R c .white)) .white → ¬ HasFour H (play R c .white) .white :=
    fun hnt hf => hnt (whiteFour_low (by omega) hE1 hnb1 hf)
  have hTne : ∀ d, d ≠ c → TCol K H (play R c .white) d := fun d hd => (tcol_play_ne .white hd).mpr (inv.dT d)
  have mk : ∀ e, ¬ HasFour H (play R c .white) .white → Legal H (play R c .white) e →
      (∀ d, d ≠ e → TCol K H (play R c .white) d) →
      (J (trunc K (play (play R c .white) e .black)) (labs H K (play (play R c .white) e .black)) ∨
        ∀ d : Fin 5, K < (play (play R c .white) e .black d).length) →
      HasFour H (play (play R c .white) e .black) .black ∨ ZInv K H J (play (play R c .white) e .black) := by
    intro e hnw1 he hT habs
    by_cases hb : HasFour H (play (play R c .white) e .black) .black
    · exact Or.inl hb
    · right
      exact
        { tm := toMove_play_black (toMove_play_white inv.tm c) e
          nw := fun hf => hnw1 (hasFour_play_other (by decide) hf)
          nb := hb
          dE := discE_play_black hE1 e
          dT := fun d => by
            by_cases hd : d = e
            · subst hd; exact tcol_play_self_black K H _ d
            · exact (tcol_play_ne .black hd).mpr (hT d hd)
          valid := play_valid hv1 he
          abs := habs }
  have tail : ¬ HasFour H (play R c .white) .white → (∀ d, TCol K H (play R c .white) d) →
      (∀ d : Fin 5, K < (play R c .white d).length) →
      BoardFull H (play R c .white) ∨ ∃ e, Legal H (play R c .white) e ∧
        (HasFour H (play (play R c .white) e .black) .black ∨
          ZInv K H J (play (play R c .white) e .black)) := by
    intro hnw1 hT hhigh
    by_cases hfull : BoardFull H (play R c .white)
    · exact Or.inl hfull
    · obtain ⟨d, hd⟩ := exists_legal hv1 hfull
      exact Or.inr ⟨d, hd, mk d hnw1 hd (fun d' _ => hT d') (Or.inr fun d' =>
        lt_of_lt_of_le (hhigh d') (play_len_ge _ _ _ _))⟩
  by_cases hlow : (R c).length < K
  · rcases inv.abs with hI0 | hhigh
    swap
    · have := hhigh c; omega
    have hlab : labs H K R c = .low := by simp only [labs, labOf]; rw [if_pos (by omega)]
    obtain ⟨hnf, hrest⟩ := (hI _ _ hI0 c).1 hlab (by rw [trunc_length]; omega)
    rw [← trunc_play_low _ hlow] at hnf hrest
    have hlabs1 : labs H K (play R c .white) = labs H K R := by
      rw [labs_play]
      have : labOf H K (R c ++ [.white]) = labs H K R c := by
        rw [hlab]; unfold labOf; rw [if_pos (by simp; omega)]
      rw [this, Function.update_eq_self]
    rw [← hlabs1] at hrest
    have hnw1 := nwOf hnf
    refine ⟨hnw1, Or.inr ?_⟩
    rcases hrest with hwin | ⟨e, hmust, hout⟩
    · obtain ⟨e, he, hf⟩ := blackWin_real hKH hwin
      exact ⟨e, he, Or.inl hf⟩
    · obtain ⟨he, hI2⟩ := blackOut_real hK hH hKH hout
      refine ⟨e, he, mk e hnw1 he (fun d hd => ?_) (Or.inl hI2)⟩
      by_cases hdc : d = c
      · subst hdc
        have : (R d).length + 5 ≤ K := by
          rcases hmust with h | h
          · exact absurd h.symm hd
          · rw [trunc_length] at h; omega
        intro _ _; rw [play_len_self]; omega
      · exact hTne d hdc
  · have hnt : ¬ HasFour K (trunc K (play R c .white)) .white := by
      rw [trunc_play_high _ (by omega)]
      exact fun hf => inv.nw (hasFour_of_trunc (by omega) hf)
    have hnw1 := nwOf hnt
    refine ⟨hnw1, ?_⟩
    have htr1 : trunc K (play R c .white) = trunc K R := trunc_play_high _ (by omega)
    by_cases hcap : (R c).length + 1 = H
    · have hT1 : ∀ d, TCol K H (play R c .white) d := fun d => by
        by_cases hd : d = c
        · subst hd; intro hlt; rw [play_len_self] at hlt; omega
        · exact hTne d hd
      rcases inv.abs with hI0 | hhigh
      · have hlab : labs H K R c = .odd := by
          simp only [labs, labOf]; rw [if_neg (by omega), if_pos (by omega)]
        have hlabs1 : labs H K (play R c .white) = Function.update (labs H K R) c .dead := by
          rw [labs_play]
          have : labOf H K (R c ++ [.white]) = .dead := by
            unfold labOf; rw [if_neg (by simp; omega), if_neg (by simp; omega)]
          rw [this]
        have hcert := (hI _ _ hI0 c).2.2 hlab
        rw [← hlabs1, ← htr1] at hcert
        rcases hcert with hall | hwin | ⟨e, hout⟩
        · exact tail hnw1 hT1 (fun d => labOf_dead (hall d))
        · obtain ⟨e, he, hf⟩ := blackWin_real hKH hwin
          exact Or.inr ⟨e, he, Or.inl hf⟩
        · obtain ⟨he, hI2⟩ := blackOut_real hK hH hKH hout
          exact Or.inr ⟨e, he, mk e hnw1 he (fun d _ => hT1 d) (Or.inl hI2)⟩
      · exact tail hnw1 hT1 (fun d => lt_of_lt_of_le (hhigh d) (play_len_ge _ _ _ _))
    · have he : Legal H (play R c .white) c := by unfold Legal; rw [play_len_self]; omega
      refine Or.inr ⟨c, he, mk c hnw1 he (fun d hd => hTne d hd) ?_⟩
      rcases inv.abs with hI0 | hhigh
      · left
        have htr2 : trunc K (play (play R c .white) c .black) = trunc K R := by
          rw [trunc_play_high _ (by rw [play_len_self]; omega), htr1]
        have hlabs2 : labs H K (play (play R c .white) c .black) =
            Function.update (labs H K R) c (labOf H K (play R c .white c ++ [.black])) := by
          rw [labs_play, labs_play, Function.update_idem]
        rw [htr2, hlabs2]
        have hlen2 : (play R c .white c ++ [Player.black]).length = (R c).length + 2 := by
          rw [play_eq]; simp
        by_cases hKc : (R c).length = K
        · have hlab : labs H K R c = .low := by simp only [labs, labOf]; rw [if_pos (by omega)]
          have : labOf H K (play R c .white c ++ [.black]) = .dead := by
            unfold labOf; rw [hlen2, if_neg (by omega), if_neg (by omega)]
          rw [this]
          exact (hI _ _ hI0 c).2.1 hlab (by rw [trunc_length]; omega)
        · have : labOf H K (play R c .white c ++ [.black]) = labs H K R c := by
            have hpar : (H - ((R c).length + 2)) % 2 = (H - (R c).length) % 2 := by omega
            simp only [labs, labOf]
            rw [hlen2, if_neg (show ¬ (R c).length + 2 ≤ K by omega),
              if_neg (show ¬ (R c).length ≤ K by omega), hpar]
          rw [this, Function.update_eq_self]; exact hIJ _ _ hI0
      · exact Or.inr fun d => lt_of_lt_of_le (lt_of_lt_of_le (hhigh d) (play_len_ge _ _ _ _)) (play_len_ge _ _ _ _)

/-- A real position whose bottom `K` rows satisfy the claim criterion (as a board of height `K`)
is safe, given the discipline of the zone invariant. -/
theorem zone_leaf_safe {K H : Nat} (hH : H % 2 = 0) (hKH : K ≤ H) {R : Board 5}
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black)
    (hv : Valid H R) (hE : DiscE K R) (hT : ∀ c, TCol K H R c) {q : Fin 5}
    (hy : ClaimHyp K (trunc K R) q) : Safe H R := by
  have hKe := hy.even
  have hodd := hy.odd
  rw [trunc_length] at hodd
  have hq : (R q).length < K := by
    by_contra hcon
    rw [Nat.min_eq_left (by omega)] at hodd; omega
  rw [Nat.min_eq_right (by omega)] at hodd
  have htq : (trunc K R q).length = (R q).length := by rw [trunc_length]; omega
  apply claim_safe hH q htm hnw hnb hv (by omega)
  · intro c hlt ht
    have he : Exceptional R c ((R c).length - 1) := by
      obtain ⟨h3, t1, t2, -⟩ := ht
      refine ⟨t1, Or.inr ?_⟩
      have e : (R c).length - 1 - 1 = (R c).length - 2 := by omega
      rw [e]; exact t2
    have hlow := hE c _ he
    have hl3 := ht.1
    have etr : trunc K R c = R c := by
      simp only [trunc]; exact List.take_of_length_le (by omega)
    apply hy.ntr c (by rw [etr]; omega)
    unfold TopThree
    rw [etr]; exact ht
  · have hd := dead_of_trunc (q := q) (h0 := (trunc K R q).length) hKH hE hT
      (fun c r _ hcell => hy.dead c r hcell)
    rw [htq] at hd
    exact hd

/-- **The zone theorem with claim-criterion leaves.** -/
theorem zone_safeL {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    {I : Board 5 → (Fin 5 → Lab) → Prop}
    (hI : ZoneCert2 K I (fun L ℓ => I L ℓ ∨ ∃ q, ClaimHyp K L q)) {R : Board 5}
    (inv : ZInv K H I R) : Safe H R := by
  refine safe_of_inv2L (ZInv K H I) (fun _ h => ⟨h.tm, h.nw⟩) ?_ R inv
  intro R inv c hc
  obtain ⟨hnw1, hrest⟩ := zone_step2 hK hH hKH (fun L ℓ h => Or.inl h) hI inv c hc
  refine ⟨hnw1, ?_⟩
  rcases hrest with hfull | ⟨e, he, hwin | inv2⟩
  · exact Or.inl hfull
  · exact Or.inr ⟨e, he, Or.inl hwin⟩
  · refine Or.inr ⟨e, he, Or.inr ?_⟩
    rcases inv2.abs with (hI2 | ⟨q, hy⟩) | hhigh
    · exact Or.inl ⟨inv2.tm, inv2.nw, inv2.nb, inv2.dE, inv2.dT, inv2.valid, Or.inl hI2⟩
    · exact Or.inr (zone_leaf_safe hH (by omega) inv2.tm inv2.nw inv2.nb inv2.valid inv2.dE inv2.dT hy)
    · exact Or.inl ⟨inv2.tm, inv2.nw, inv2.nb, inv2.dE, inv2.dT, inv2.valid, Or.inr hhigh⟩

#print axioms zone_safeL

end C4W5
