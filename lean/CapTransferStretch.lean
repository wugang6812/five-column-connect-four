import CapTransferRebase
import CapTransferArithmetic

/-! Source-only full clean-cut transport draft; not yet elaborated. -/
namespace C4W5.CapTransfer
open Connect4 (Player opponent)
open Connect4.NarrowBoards
open C4W5.LongThreat (liftTarget)
set_option linter.deprecated false

theorem postGuard_low {D H u a b : Nat} {A : Board 5} {t s : Fin 5}
    {Q : Fin 5 → Prop} {x y : Int} (hc : ClearCut D H A u)
    (ha : (A s).length < a) (hab : a < b) (hao : (a - (A s).length) % 2 = 1)
    (hbo : (b - (A s).length) % 2 = 0) (hy : y ≤ (u : Int))
    (g : PostGuard t s a b Q (fun q => (A q).length) x y) :
    PostGuard t s (liftTarget u a) (liftTarget u b) Q (fun q => (stretch A u q).length) x y := by
  rcases g with ⟨q,hq,hx,hy0,hpar⟩ | ⟨hx,hbar⟩
  · left
    dsimp only at hy0 hpar
    have he : (stretch A u q).length = (A q).length := by
      rw [stretch_length hc, if_neg (by omega)]
    exact ⟨q,hq,by
      simpa [Claimed,he] using
        (show Claimed q (A q).length x y from ⟨hx,hy0,hpar⟩)⟩
  · right; refine ⟨hx, ?_⟩
    have hb : (b : Int) ≤ y ∨ ((a : Int) ≤ y ∧ (y - ((A s).length : Int)) % 2 = 0) := by
      rcases hbar with h | ⟨h,p⟩
      · exact Or.inl h
      · change y % 2 = ((A s).length : Int) % 2 at p
        exact Or.inr ⟨h, by omega⟩
    have hnew := phase2_guard_stretch_low ha hab hao hbo hy hb
    dsimp only at hnew
    rw [← stretch_length hc s] at hnew
    rcases hnew with h | ⟨h,p⟩
    · exact Or.inl h
    · exact Or.inr ⟨h,by
        change y % 2 = ((stretch A u s).length : Int) % 2
        omega⟩

theorem postGuard_high {D H u a b : Nat} {A : Board 5} {t s : Fin 5}
    {Q : Fin 5 → Prop} {x y : Int} (hc : ClearCut D H A u)
    (g : PostGuard t s a b Q (fun q => (A q).length) x y) :
    PostGuard t s (liftTarget u a) (liftTarget u b) Q (fun q => (stretch A u q).length) x (y+2) := by
  rcases g with ⟨q,hq,hx,hy0,hpar⟩ | ⟨hx,hbar⟩
  · left
    refine ⟨q,hq,hx,?_,?_⟩ <;> dsimp only at * <;> rw [stretch_length hc]
      <;> split_ifs <;> push_cast <;> omega
  · right; refine ⟨hx,?_⟩
    have hb : (b : Int) ≤ y ∨ ((a : Int) ≤ y ∧ (y - ((A s).length : Int)) % 2 = 0) := by
      rcases hbar with h | ⟨h,p⟩
      · exact Or.inl h
      · change y % 2 = ((A s).length : Int) % 2 at p
        exact Or.inr ⟨h,by omega⟩
    have hnew := phase2_guard_stretch_high (u := u) hb
    dsimp only at hnew
    rw [← stretch_length hc s] at hnew
    rcases hnew with h | ⟨h,p⟩
    · exact Or.inl h
    · exact Or.inr ⟨h,by
        change (y + 2) % 2 = ((stretch A u s).length : Int) % 2
        omega⟩

theorem postDead_low {D H u a b : Nat} {A : Board 5} {t s c : Fin 5}
    {Q : Fin 5 → Prop} {r : Nat} (hD : 2 ≤ D) (hc : ClearCut D H A u)
    (ha : (A s).length < a) (hab : a < b) (hao : (a - (A s).length) % 2 = 1)
    (hbo : (b - (A s).length) % 2 = 0) (hr : r + D < u)
    (hd : PostDead H A t s a b Q (fun q => (A q).length) c r) :
    PostDead (H+2) (stretch A u) t s (liftTarget u a) (liftTarget u b) Q
       (fun q => (stretch A u q).length) c r := by
  have hb := clearCut_bounds hc
  intro dy hdy i
  obtain ⟨j,hj⟩ := hd dy hdy i
  have hi := i.isLt
  have hjj := j.isLt
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hdy
  dsimp only at hj ⊢
  refine ⟨j,?_⟩
  rcases hj with hj | hj | hj
  · left
    rw [cell_low (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> omega)]
    exact hj
  · right; left
    exact postGuard_low hc ha hab hao hbo (by rcases hdy with rfl | rfl | rfl <;> omega) hj
  · right; right
    rintro ⟨a1,a2,a3,a4⟩
    apply hj
    refine ⟨a1,a2,a3,?_⟩
    rcases hdy with rfl | rfl | rfl <;> omega

theorem postDead_high {D H u a b : Nat} {A : Board 5} {t s c : Fin 5}
    {Q : Fin 5 → Prop} {r : Nat} (hD : 2 ≤ D) (hc : ClearCut D H A u)
    (hr : u + D < r)
    (hd : PostDead H A t s a b Q (fun q => (A q).length) c r) :
    PostDead (H+2) (stretch A u) t s (liftTarget u a) (liftTarget u b) Q
      (fun q => (stretch A u q).length) c (r+2) := by
  have hb := clearCut_bounds hc
  intro dy hdy i
  obtain ⟨j,hj⟩ := hd dy hdy i
  have hi := i.isLt
  have hjj := j.isLt
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hdy
  dsimp only at hj ⊢
  have e : (((r+2 : Nat) : Int) - (i : Int) * dy + (j : Int) * dy) =
      ((r : Int) - (i : Int) * dy + (j : Int) * dy)+2 := by push_cast; omega
  refine ⟨j,?_⟩
  rcases hj with hj | hj | hj
  · left
    rw [cell_high (by omega) hc _ _ (by rcases hdy with rfl | rfl | rfl <;> push_cast <;> omega), e]
    simpa using hj
  · right; left
    rw [e]; exact postGuard_high hc hj
  · right; right
    rintro ⟨a1,a2,a3,a4⟩
    apply hj
    refine ⟨a1,a2,?_,?_⟩ <;>
      rcases hdy with rfl | rfl | rfl <;> push_cast at a3 a4 ⊢ <;> omega

theorem hyp_stretch {D H u a b : Nat} {A : Board 5} {t s : Fin 5}
    {Q : Fin 5 → Prop} (hD : 2 ≤ D) (hc : ClearCut D H A u)
    (hy : Hyp H A t s a b Q) :
    Hyp (H+2) (stretch A u) t s (liftTarget u a) (liftTarget u b) Q := by
  have hb := clearCut_bounds hc
  have hlen : ∀ c, (stretch A u c).length =
    if u < (A c).length then (A c).length+2 else (A c).length := stretch_length hc
  have hbo : (b - (A s).length) % 2 = 0 := by
    have h1 := hy.evenB; have h2 := hy.above; have h3 := hy.order
    omega
  have hn := two_target_height_transport (u := u) hy.above hy.order hy.below hy.oddA hbo
  dsimp only at hn
  rw [← hlen s] at hn
  obtain ⟨ha,hab,hbH,hao,hbParity⟩ := hn
  have bEven : liftTarget u b % 2 = (stretch A u s).length % 2 := by omega
  refine ⟨by have := hy.even; omega,?_,hy.distinct,hy.noT,hy.noS,?_,?_,?_,
    ha,hab,hbH,hao,bEven,?_,LongThreat.threat_stretch hD hc hy.threatA,
        LongThreat.threat_stretch hD hc hy.threatB,?_,?_⟩
  · intro c
    have := hy.valid c
    rw [hlen]; split_ifs <;> omega
  · have := hy.oddT
    rw [hlen]; split_ifs <;> omega
  · have := hy.evenS
    rw [hlen]; split_ifs <;> omega
  · intro q hq
    have := hy.evenQ q hq
    rw [hlen]; split_ifs <;> omega
  · intro c hlt ht
    rcases top_of_clear hc c with hlow | hthr
    · have e : stretch A u c = A c := by
        simp only [stretch,colStretch]; rw [if_neg (by omega)]
      unfold TopThree at ht
      rw [e] at ht
      exact hy.noTriple c (by show (A c).length < H; omega) ht
    · have hst : ∀ n, stone (stretch A u c) n = stone (A c) (phi u n) :=
        fun n => stone_phi (A c) u n (by omega) (by omega)
      have hl : (stretch A u c).length = (A c).length+2 := by
        rw [hlen,if_pos (by omega)]
      obtain ⟨-,t1,t2,t3⟩ := ht
      rw [hl,hst,phi_gt (by omega)] at t1 t2 t3
      change (stretch A u c).length < H+2 at hlt
      rw [hl] at hlt
      apply hy.noTriple c (by show (A c).length < H; omega)
      refine ⟨by omega, ?_, ?_, ?_⟩
      · have e : (A c).length+2-1-2 = (A c).length-1 := by omega
        rw [e] at t1; exact t1
      · have e : (A c).length+2-2-2 = (A c).length-2 := by omega
        rw [e] at t2; exact t2
      · have e : (A c).length+2-3-2 = (A c).length-3 := by omega
        rw [e] at t3; exact t3
  · intro c r' hcell
    obtain ⟨r,hold,⟨rfl,hl⟩ | ⟨rfl,hh⟩⟩ := exc_stretch hD hc hcell
    · exact LongThreat.dead_stretch_low hD hc hy.above hy.oddA hl (hy.deadA c r hold)
    · exact LongThreat.dead_stretch_high hD hc hh (hy.deadA c r hold)
  · intro c r' hcell
    obtain ⟨r,hold,⟨rfl,hl⟩ | ⟨rfl,hh⟩⟩ := exc_stretch hD hc hcell
    · exact postDead_low hD hc hy.above hy.order hy.oddA hbo hl (hy.deadB c r hold)
    · exact postDead_high hD hc hh (hy.deadB c r hold)

theorem hyp_seq {D H H' a b : Nat} {A R : Board 5} {t s : Fin 5}
    {Q : Fin 5 → Prop} (hD : 2 ≤ D) (hs : SEq D H A H' R)
    (hy : Hyp H A t s a b Q) :
    ∃ a' b', Hyp H' R t s a' b' Q := by
  induction hs generalizing a b with
  | refl => exact ⟨a,b,hy⟩
  | step u hc _ ih => exact ih (hyp_stretch hD hc hy)

theorem leafSound {D : Nat} (hD : 2 ≤ D) : LeafSound D L := by
  rintro h A H R ⟨t,s,a,b,Q,hy⟩ hs htm hnw hnb
  obtain ⟨a',b',h'⟩ := hyp_seq hD hs hy
  exact hyp_safe h' htm hnw hnb

#print axioms leafSound

end C4W5.CapTransfer
