import FiveColumns.FrozenBridge
import C4W5.Even

namespace FiveColumns

theorem five_even_draw_by_stretch : FiveEvenDrawGoal :=
  frozen_goal_of_even_draw C4W5.five_columns_even_draw

#print axioms five_even_draw_by_stretch
end FiveColumns
