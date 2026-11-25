import ZoneEndStretch
import CapTransferCheck
import LongThreatZoneChecked
import C4W5.Cert.ZoneFast

namespace C4W5.ZoneEnds.SZ
open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-- Conditional membership gate: the original Long and the existing cap witnesses
are separately checked. The data decoder picks which predicate to invoke. -/
theorem checkCapExtra {k : Nat} {p : Pos} {t s : Fin 5} {a b mask : Nat}
    {dA dB : Fin 3} {iA iB : Fin 4}
    (h : CapTransfer.check k p t s a b mask dA dB iA iB = true) : Extra k p.toBoard :=
  Or.inr (CapTransfer.check_leaf h)

theorem checkLongExtra {k : Nat} {p : Pos} {t : Fin 5} {rho mask : Nat}
    {d : Fin 3} {i : Fin 4}
    (h : LongThreat.SZ.checkZone k p t rho mask d i = true) : Extra k p.toBoard :=
  Or.inl (LongThreat.SZ.checkZone_sound h)

def Join (J : Nat → Board 5 → (Fin 5 → Lab) → Prop) (k : Nat) (A : Board 5) (l : Fin 5 → Lab) : Prop :=
  J k A l ∨ Extra k A

theorem promoteJL {D k : Nat} {J : Nat → Board 5 → (Fin 5 → Lab) → Prop} {A : Board 5}
    {l : Fin 5 → Lab} (h : C4W5.JL D (Join J) k A l) : JL D J k A l := by
  rcases h with ⟨k', A', (hJ|hZ)|hOld, hS⟩
  · exact ⟨k', A', Or.inl hJ, hS⟩
  · exact ⟨k', A', Or.inr (Or.inr hZ), hS⟩
  · exact ⟨k', A', Or.inr (Or.inl hOld), hS⟩

theorem promoteOut {D k : Nat} {J : Nat → Board 5 → (Fin 5 → Lab) → Prop}
    {A : Board 5} {l : Fin 5 → Lab} {e : Fin 5}
    (h : C4W5.SBlackOut D (Join J) k A l e) : SBlackOut D J k A l e := by
  rcases h with ⟨hl, hlen, hall⟩ | ⟨hl, hlen, hJ⟩ | ⟨hl, hJ⟩
  · refine Or.inl ⟨hl, hlen, fun k' A' hv => ?_⟩
    rcases hall k' A' hv with hw | ho
    · exact Or.inl hw
    · exact Or.inr (promoteJL ho)
  · exact Or.inr (Or.inl ⟨hl, hlen, promoteJL hJ⟩)
  · exact Or.inr (Or.inr ⟨hl, promoteJL hJ⟩)

theorem fast_sound_extra {D : Nat} (hD : 2 ≤ D)
    {J : Nat → Board 5 → (Fin 5 → Lab) → Prop} {memf : Nat → Pos → Lab5 → Bool}
    (hm : ∀ k q l, memf k q l = true → Join J k q.toBoard l.fn) {k : Nat}
    {p : Pos} {l : Lab5} {rep : Nat} (hok : ZoneFast.step D memf k p l rep = true) :
    Valid k p.toBoard ∧ ∀ c : Fin 5,
    (l.fn c = .low → (p.toBoard c).length < k → ∀ k₁ A₁, Variant D k p.toBoard c .white k₁ A₁ →
      ¬ HasFour k₁ A₁ .white ∧
      (SBlackWin D k₁ A₁ l.fn ∨
        ∃ e, (e = c ∨ (p.toBoard c).length + 5 ≤ k) ∧ SBlackOut D J k₁ A₁ l.fn e)) ∧
    (l.fn c = .low → (p.toBoard c).length = k → JL D J k p.toBoard (Function.update l.fn c .dead)) ∧
    (l.fn c = .odd → (∀ d, Function.update l.fn c .dead d = .dead) ∨
      SBlackWin D k p.toBoard (Function.update l.fn c .dead) ∨
      ∃ e, SBlackOut D J k p.toBoard (Function.update l.fn c .dead) e) := by
  obtain ⟨hv, hall⟩ := stepOKSZ_sound hD hm (ZoneFast.step_sound hok)
  refine ⟨hv, fun c => ?_⟩
  obtain ⟨low, cap, odd⟩ := hall c
  refine ⟨?_, fun hl he => promoteJL (cap hl he), ?_⟩
  · intro hl hlen k₁ A₁ hs
    obtain ⟨hnw, hw | ⟨e, hcond, ho⟩⟩ := low hl hlen k₁ A₁ hs
    · exact ⟨hnw, Or.inl hw⟩
    · exact ⟨hnw, Or.inr ⟨e, hcond, promoteOut ho⟩⟩
  · intro hl
    rcases odd hl with hnone | hw | ⟨e, ho⟩
    · exact Or.inl hnone
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr ⟨e, promoteOut ho⟩)

#print axioms C4W5.ZoneEnds.SZ.checkCapExtra
#print axioms C4W5.ZoneEnds.SZ.fast_sound_extra
end C4W5.ZoneEnds.SZ
