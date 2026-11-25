import G5WindowRoot
import C4W5.Cert.ZoneFast

/-! Use the original optimized ZoneFast step with a compact window lookup. -/
namespace C4W5.WindowBank
open Connect4.NarrowBoards

theorem all_mono {a : Nat} {f g : Nat → Bool} (implies : ∀ w, f w = true → g w = true)
    {t : Bank} (hf : all a f t = true) : all a g t = true := by
  induction t with
  | block n no =>
      simp only [all, List.all_eq_true] at *
      exact fun i hi => implies _ (hf i hi)
  | window n base bias no =>
      simp only [all, List.all_eq_true] at *
      exact fun i hi => implies _ (hf i hi)
  | branch cut l r hl hr =>
      simp only [all, Bool.and_eq_true] at hf ⊢
      exact ⟨hl hf.1, hr hf.2⟩

def szcheckFast (D : Nat) (F : SZFormat) (t : Bank) (w : Nat) : Bool :=
  force w fun w => forceP (F.pos w) fun p =>
    ZoneFast.step D (szmem F t) (F.height w) p (F.labels w) (w % F.repBase)

theorem szcheckFast_sound {D : Nat} {F : SZFormat} {t : Bank} {w : Nat}
    (h : szcheckFast D F t w = true) : szcheckRow D F t w = true := by
  simp only [szcheckFast, szcheckRow, force_eq, forceP_eq] at *
  exact ZoneFast.step_sound h

theorem g5_zone_of_fast_window_bank (F : SZFormat) (t : Bank)
    (ok : all F.radix (szcheckFast 2 F t) t = true)
    (root : szmem F t 14 g5p ⟨0, 0, 0, 0, 0⟩ = true) (m b : Nat) (hb : 5 ≤ b) (hbm : b + 3 ≤ m) :
    Safe (2 * m) (G b) :=
  g5_zone_of_window_bank F t (all_mono (fun _ => szcheckFast_sound) ok) root m b hb hbm

#print axioms g5_zone_of_fast_window_bank
end C4W5.WindowBank
