import WindowLongGate
import LongThreatBits

namespace C4W5.WindowBank

def fastGate : SFormat → Bank → Nat → Pos → Bool := witnessGate LongThreat.checkBits

theorem fastGate_sound (F : SFormat) (hints : Bank) (H : Nat) (p : Pos)
    (h : fastGate F hints H p = true) : LongThreat.L H p.toBoard :=
  witnessGate_sound LongThreat.checkBits
    (fun _ _ _ _ _ _ _ h => LongThreat.check_leaf (LongThreat.checkBits_reference h))
    F hints H p h

#print axioms fastGate_sound

end C4W5.WindowBank
