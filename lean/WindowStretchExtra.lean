import SG3CheckedRoot

/-! Optional terminal callback whose reflection and Stretch transport are hypotheses.
Omitting it (false) gives the original certificate semantics. All old Claim exits remain. -/
namespace C4W5.WindowBank
open Connect4 (Player opponent)
open Connect4.NarrowBoards

def sgate (F : SFormat) (t : Bank) (extra : Nat → Pos → Bool) (h : Nat) (p : Pos) : Bool :=
  smem F t h p || extra h p

def scheckExtraRow (D : Nat) (F : SFormat) (t : Bank) (extra : Nat → Pos → Bool) (w : Nat) : Bool :=
  force w fun w => forceP (F.pos w) fun p =>
    stepOKS D (sgate F t extra) (F.height w) p (w % F.repBase)

theorem stretchCert_of_extra_bank {D : Nat} (hD : 2 ≤ D) (F : SFormat) (t : Bank)
    {L : Nat → Board 5 → Prop} (extra : Nat → Pos → Bool)
    (extraSound : ∀ h p, extra h p = true → L h p.toBoard)
    (hall : all F.radix (scheckExtraRow D F t extra) t = true) :
    StretchCertL D (fun h A => CL h A ∨ L h A) (srel F t) := by
  have hm : ∀ h p, sgate F t extra h p = true → srel F t h p.toBoard ∨ L h p.toBoard := by
    intro h p hp
    simp only [sgate, Bool.or_eq_true] at hp
    rcases hp with hf | he
    · exact Or.inl (smem_sound hf)
    · exact Or.inr (extraSound _ _ he)
  rintro h A ⟨w, hw, rfl, rfl⟩ c hc h₁ A₁ hv
  have hrow := all_sound hall hw
  simp only [scheckExtraRow, force_eq, forceP_eq] at hrow
  obtain ⟨hno, hcases⟩ :=
    stepOKS_sound hD (I := fun h A => srel F t h A ∨ L h A) hm hrow c hc h₁ A₁ hv
  refine ⟨hno, ?_⟩
  rcases hcases with hfull | ⟨e, he, hv₂⟩
  · exact Or.inl hfull
  · refine Or.inr ⟨e, he, ?_⟩
    intro h₂ A₂ hvar
    rcases hv₂ h₂ A₂ hvar with hwin | ⟨h₃, A₃, ((hbank | hextra) | hold), hseq⟩
    · exact Or.inl hwin
    · exact Or.inr ⟨h₃, A₃, Or.inl hbank, hseq⟩
    · exact Or.inr ⟨h₃, A₃, Or.inr (Or.inr hextra), hseq⟩
    · exact Or.inr ⟨h₃, A₃, Or.inr (Or.inl hold), hseq⟩

theorem stretch_safe_of_extra_bank {D : Nat} (hD : 2 ≤ D) (F : SFormat) (t : Bank)
    {L : Nat → Board 5 → Prop} (extra : Nat → Pos → Bool)
    (extraSound : ∀ h p, extra h p = true → L h p.toBoard)
    (extraLift : LeafSound D L)
    (hall : all F.radix (scheckExtraRow D F t extra) t = true)
    {h : Nat} {q : Pos} (hq : smem F t h q = true) {H : Nat} {R : Board 5}
    (htm : toMove R = .white) (hnw : ¬ HasFour H R .white)
    (hs : SEq D h q.toBoard H R) : Safe H R := by
  have hleaf : LeafSound D (fun h A => CL h A ∨ L h A) := by
    intro h A H R ht hs htm hnw hnb
    rcases ht with old | fresh
    · exact claim_leafSound hD h A H R old hs htm hnw hnb
    · exact extraLift h A H R fresh hs htm hnw hnb
  exact stretch_safeL hD hleaf (stretchCert_of_extra_bank hD F t extra extraSound hall)
    htm hnw (smem_sound hq) hs

theorem g3_of_extra_window_bank (F : SFormat) (t : Bank)
    {L : Nat → Board 5 → Prop} (extra : Nat → Pos → Bool)
    (extraSound : ∀ h p, extra h p = true → L h p.toBoard)
    (extraLift : LeafSound 2 L)
    (ok : all F.radix (scheckExtraRow 2 F t extra) t = true)
    (root : smem F t 14 g3p = true) (m : Nat) (hm : 7 ≤ m) : Safe (2*m) (G 3) := by
  have hq : g3p.toBoard = G 3 := by
    funext c
    obtain rfl | rfl | rfl | rfl | rfl := fin5_cases c <;> rfl
  have e : 14 + 2 * (m-7) = 2*m := by omega
  have hs : SEq 2 14 g3p.toBoard (2*m) (G 3) := by
    rw [hq, ← e]
    exact seq_G3 (m-7)
  have hnw : ¬ HasFour (2*m) (G 3) .white := by
    intro hf
    have hn := (hs.hasFour_iff (by omega) .white).mpr hf
    rw [hq, ← G3_play] at hn
    exact no_four_of_run _ (by decide +kernel) hn
  exact stretch_safe_of_extra_bank (by omega) F t extra extraSound extraLift ok root (toMove_G 3) hnw hs

#print axioms stretchCert_of_extra_bank
#print axioms g3_of_extra_window_bank
end C4W5.WindowBank
