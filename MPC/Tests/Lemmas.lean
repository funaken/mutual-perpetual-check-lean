import MPC.Basic.Lemmas

/-! Dependency guards for the shared elementary facts. -/

/-- info: 'MPC.Player.opponent_opponent' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Player.opponent_opponent

/-- info: 'MPC.Player.opponent_ne_self' does not depend on any axioms -/
#guard_msgs in
#print axioms MPC.Player.opponent_ne_self

/-- info: 'MPC.Player.eq_or_eq_opponent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MPC.Player.eq_or_eq_opponent

/-- info: 'MPC.Pos.onBoard_toInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Pos.onBoard_toInt

/-- info: 'MPC.Pos.toPos_toInt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MPC.Pos.toPos_toInt

/-- info: 'MPC.PieceType.mem_king_stepDirs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPC.PieceType.mem_king_stepDirs_iff
