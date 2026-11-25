import C4W5.CompactZone.PackedBank
import C4W5.Cert.ClaimBits
import C4W5.Theory.ZoneL

/-! The original all-height Zone lift already supports ClaimHyp endpoints.
This bridge preserves its exact transition and discipline conditions and
uses a compact relation for all non-leaf states. -/
namespace C4W5.CompactZone.ClaimBank
open Connect4 (Player)
open Connect4.NarrowBoards C4W5.PackedBank

def zmemL (K : Nat) (F : ZFormat) (t : Bank) (p : Pos) (l : Lab5) : Bool :=
  zmem F t p l || ClaimBits.fast K p

theorem zmemL_sound {K : Nat} {F : ZFormat} {t : Bank} {p : Pos} {l : Lab5}
    (hm : zmemL K F t p l = true) :
    zrel F t p.toBoard l.fn ∨ ∃ q, ClaimHyp K p.toBoard q := by
  simp only [zmemL, Bool.or_eq_true] at hm
  exact hm.elim (fun h => Or.inl (zmem_sound h)) (fun h => Or.inr (claimB_sound (ClaimBits.fast_sound h)))

def zcheckRowL (K : Nat) (F : ZFormat) (t : Bank) (w : Nat) : Bool :=
  force w fun w => forceP (F.pos w) fun p =>
    stepOKZ K (zmemL K F t) p (F.labels w) (w % F.repBase)

theorem zoneCert2_of_bank {K : Nat} (F : ZFormat) (t : Bank)
    (hall : all F.radix (zcheckRowL K F t) t = true) :
    ZoneCert2 K (zrel F t) (fun A l => zrel F t A l ∨ ∃ q, ClaimHyp K A q) := by
  rintro A l ⟨w, hw, rfl, rfl⟩ c
  have hr := all_sound hall hw
  simp only [zcheckRowL, force_eq, forceP_eq] at hr
  exact stepOKZ_sound (I := fun A l => zrel F t A l ∨ ∃ q, ClaimHyp K A q)
    (fun _ _ h => zmemL_sound h) hr c

theorem zone_safe_of_claim_bank {K H : Nat} (hK : K % 2 = 0) (hH : H % 2 = 0) (hKH : K + 2 ≤ H)
    (F : ZFormat) (t : Bank) (ms : List (Fin 5)) (q : Pos) (hr : Pos.run K Pos.empty .black ms = some q)
    (hall : all F.radix (zcheckRowL K F t) t = true) (hodd : q.total % 2 = 1) (hd : q.discB K = true)
    (hm : zmem F t q ⟨0, 0, 0, 0, 0⟩ = true) : Safe H (playList (emptyBoard 5) .black ms) := by
  obtain ⟨e, hnw, hnb, hwf⟩ := root_of_run' hr
  rw [← e]
  have hwH := Pos.WF_mono hwf (show K ≤ H by omega)
  obtain ⟨hE, hT⟩ := Pos.discB_sound (H := H) hwf hd
  have htrunc : trunc K q.toBoard = q.toBoard := by
    funext c
    simp only [trunc]
    exact List.take_of_length_le (by rw [Pos.height]; exact (hwf c.val).2)
  have hfourK : ∀ pl, HasFour H q.toBoard pl → HasFour K q.toBoard pl := by
    intro pl hf
    rw [← hasFourF_iff hwH] at hf
    exact (hasFourF_iff hwf pl).mp hf
  apply zone_safeL hK hH hKH (zoneCert2_of_bank F t hall)
  refine ⟨?_, fun hf => hnw (hfourK _ hf), fun hf => hnb (hfourK _ hf), hE, hT, ?_, Or.inl ?_⟩
  · unfold toMove
    rw [Pos.totalStones_eq, if_neg (by omega)]
  · intro c
    rw [Pos.height]
    exact (hwH c.val).2
  · rw [htrunc]
    have heq : labs H K q.toBoard = (⟨0, 0, 0, 0, 0⟩ : Lab5).fn := by
      funext c
      simp only [labs, labOf, Lab5.fn]
      rw [if_pos (by rw [Pos.height]; exact (hwf c.val).2)]
      fin_cases c <;> rfl
    rw [heq]
    exact zmem_sound hm

#print axioms zone_safe_of_claim_bank

end C4W5.CompactZone.ClaimBank
