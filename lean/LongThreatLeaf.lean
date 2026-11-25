import LongThreat
import LongThreatCheck

namespace C4W5.LongThreat
open Connect4 (Player opponent)
open Connect4.NarrowBoards

/-- Terminal real-tail interface. Q is an actual claimed set, not a zone label. -/
def L (H : Nat) (R : Board 5) : Prop := ∃ t rho Q, Hyp H R t rho Q

theorem leafSound {D : Nat} (hD : 2 ≤ D) : LeafSound D L := by
  rintro h A H R ⟨t, rho, Q, hy⟩ hs htm hnw hnb
  obtain ⟨rho', h'⟩ := hyp_seq hD hs hy
  exact hyp_safe h' htm hnw hnb

theorem check_leaf {H : Nat} {p : Pos} {t : Fin 5} {rho mask : Nat} {d : Fin 3} {i : Fin 4}
    (h : check H p t rho mask d i = true) : L H p.toBoard :=
  ⟨t, rho, selected mask, check_sound h⟩

theorem example_all_stretches {D H : Nat} {R : Board 5} (hD : 2 ≤ D)
    (hs : SEq D 10 examplePos.toBoard H R) (htm : toMove R = .white)
    (hnw : ¬ HasFour H R .white) (hnb : ¬ HasFour H R .black) : Safe H R :=
  leafSound hD 10 examplePos.toBoard H R (check_leaf exampleChecked) hs htm hnw hnb

#print axioms leafSound
#print axioms check_leaf
#print axioms example_all_stretches
end C4W5.LongThreat
