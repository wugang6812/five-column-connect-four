import CapTransferBoard

/-! Static draft for the parity-changing cap. Await independent Lean elaboration. -/
namespace C4W5.CapTransfer
open Connect4 (Player opponent)
open Connect4.NarrowBoards
set_option linter.deprecated false

theorem stripe_below_black {H : Nat} {R : Board 5} {t s q : Fin 5} {a b : Nat}
    {Q : Fin 5 → Prop} {h0 : Fin 5 → Nat} {x y : Int}
    (cur : BeforeCap H R t s a b Q h0) (hq : protect t Q q)
    (claim : Claimed q (h0 q) x y) (hy0 : 0 ≤ y) (hyH : y < (H : Int))
    (hl : y < ((R q).length : Int)) :
    cellAtInt H R x y = some .black := by
  obtain ⟨hx, hy, hpar⟩ := claim
  rw [hx, cellAtInt_fin _ q _ hy0 hyH]
  exact cur.inv.alt q (Or.inr hq) y.toNat (by omega) (by omega) (by omega)

theorem transfer_post {H : Nat} {A : Board 5} {t s : Fin 5} {a b : Nat}
    {Q : Fin 5 → Prop} (hy : Hyp H A t s a b Q) :
    TransferPost H t s a b Q (fun q => (A q).length) := by
  intro R cur hcap _
  let h0 := fun q => (A q).length
  let B := pair R t s
  have haH : a < H := Nat.lt_trans hy.order hy.below
  have ht : Legal H R t := by change (R t).length < H; omega
  have hs : Legal H (play R t .white) s := by
    change (play R t .white s).length < H
    rw [play_ne _ _ _ _ hy.distinct]
    exact Nat.lt_trans cur.inv.below haH
  have validB : Valid H B := play_valid (play_valid cur.inv.valid ht) hs
  have lenS : (B s).length = (R s).length + 1 := by
    simp [B,pair,play_len,hy.distinct]
  have lenT : (B t).length = H := by
    simpa [B,pair,play_len,Ne.symm hy.distinct] using hcap
  have eqOther (q : Fin 5) (hsq : q ≠ s) (htq : q ≠ t) :
      B q = R q := by
    dsimp [B,pair]
    rw [play_ne _ _ _ _ hsq,play_ne _ _ _ _ htq]
  have lenSle : (B s).length ≤ a := by
    rw [lenS]; have hh := cur.inv.below; omega
  have hSpar : (R s).length % 2 = h0 s % 2 := cur.inv.par s (Or.inl rfl)
  have hSpar' : (B s).length % 2 ≠ h0 s % 2 := by omega
  have oddS : (H - (B s).length) % 2 = 1 := by
    have hev := hy.even
    have hp := hy.evenS
    have hle := validB s
    change h0 s % 2 = 0 at hp
    omega
  have bgt : (B s).length < b := Nat.lt_of_le_of_lt lenSle hy.order
  have bp : b % 2 = h0 s % 2 := hy.evenB
  have bOdd : (b - (B s).length) % 2 = 1 := by omega
  have adv {x y : Int} (hx : cellAtInt H R x y = some .black) :
      cellAtInt H B x y = some .black :=
    cell_play_mono (cell_play_mono hx t .white) s .black
  have keep (q : Fin 5) (hq : Q q) : B q = R q :=
    eqOther q (fun h => hy.noS (h ▸ hq)) (fun h => hy.noT (h ▸ hq))
  have rb (q : Fin 5) (hq : Q q) : (H - (B q).length) % 2 = 0 := by
    rw [keep q hq]
    have h1 : (R q).length % 2 = h0 q % 2 := cur.inv.par q (Or.inr (Or.inr hq))
    have h2 := hy.evenQ q hq
    change h0 q % 2 = 0 at h2
    have h3 := hy.even
    have h4 : (R q).length ≤ H := cur.inv.valid q
    omega
  refine ⟨hy.even,validB,hy.noS,oddS,rb,bgt,hy.below,bOdd,?_,?_,?_⟩
  · intro d hd hh
    by_cases hds : d = s
    · subst d
      obtain ⟨-, top, -, -⟩ := hh
      dsimp [B,pair] at top
      rw [play_eq,stone_append] at top
      simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_sub_cancel,
        lt_irrefl,if_false,if_true] at top
      cases top
    · by_cases hdt : d = t
      · subst d
        change (B t).length < H at hd
        omega
      · change TopThree B d at hh
        rw [TopThree,eqOther d hds hdt] at hh
        change (B d).length < H at hd
        rw [eqOther d hds hdt] at hd
        exact cur.inv.ntr d hd hh
  · exact LongThreat.threat_play (LongThreat.threat_play cur.threatB t .white) s .black
  · intro d r hx dy hdy i
    obtain ⟨j,hj⟩ := cur.deadB d r (exceptions_pair ht (Or.inr hcap) hx) dy hdy i
    refine ⟨j, ?_⟩
    dsimp only at hj ⊢
    let x : Int := (d.val : Int) - (i : Int) * 1 + (j : Int) * 1
    let y : Int := (r : Int) - (i : Int) * dy + (j : Int) * dy
    change cellAtInt H R x y = some .black ∨ PostGuard t s a b Q h0 x y ∨
      ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int)) at hj
    change cellAtInt H B x y = some .black ∨
      LongThreat.Guard s b Q (fun q => (B q).length) x y ∨
      ¬ (0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int))
    rcases hj with hB | hG | ho
    · exact Or.inl (adv hB)
    · by_cases nh : 0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < (H : Int)
      · obtain ⟨-, -, y0, yH⟩ := nh
        rcases hG with ⟨q,hq,hc⟩ | ⟨hsx, hby | ⟨hay,hpy⟩⟩
        · rcases hq with heq | hq
          · subst q
            have hpar : (R t).length % 2 = h0 t % 2 := cur.inv.par t (Or.inr (Or.inl rfl))
            have hline : (y - (h0 t : Int)) % 2 = 1 := hc.2.2
            have hlt : y < ((R t).length : Int) := by omega
            exact Or.inl (adv (stripe_below_black cur (Or.inl rfl) hc y0 yH hlt))
          · by_cases hlq : y < ((R q).length : Int)
            · exact Or.inl (adv (stripe_below_black cur (Or.inr hq) hc y0 yH hlq))
            · have hpar : (R q).length % 2 = h0 q % 2 := cur.inv.par q (Or.inr (Or.inr hq))
              obtain ⟨hqx,hqy,hqp⟩ := hc
              have nr : Claimed q (B q).length x y := by
                rw [keep q hq]
                exact ⟨hqx,by omega,by omega⟩
              exact Or.inr (Or.inl (Or.inl ⟨q,Or.inr hq,nr⟩))
        · exact Or.inr (Or.inl (Or.inr ⟨hsx,hby⟩))
        · have nr : Claimed s (B s).length x y :=
            ⟨hsx,by omega,by omega⟩
          exact Or.inr (Or.inl (Or.inl ⟨s,Or.inl rfl,nr⟩))
      · exact Or.inr (Or.inr nh)
    · exact Or.inr (Or.inr ho)

theorem hyp_safe {H : Nat} {A : Board 5} {t s : Fin 5} {a b : Nat}
    {Q : Fin 5 → Prop} (hy : Hyp H A t s a b Q)
    (ht : toMove A = .white) (hnw : ¬ HasFour H A .white)
    (hnb : ¬ HasFour H A .black) : Safe H A :=
  hyp_safe_of_transfer hy (transfer_post hy) ht hnw hnb

#print axioms hyp_safe

end C4W5.CapTransfer
