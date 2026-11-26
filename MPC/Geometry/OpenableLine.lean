import MPC.Basic.Lemmas
import MPC.Glare.NonGlaringCount
/-!
# MPC.Geometry.OpenableLine

The paper's Proposition 3.3 and Corollary 3.4 on independent traces, in a
linear-interval form. In a periodic mutual-check trace, a board move of a
non-glaring piece from a square `A` is a discovered check (Lemmas 2.4 and 2.8);
its unblocked checker `Q` stands on a square `B` whose line to the enemy king
runs through `A`. Every move whose destination glares afterwards is a direct
check by that destination piece (Lemmas 2.5–2.8). So no move can put a piece on
`B` while `A` is occupied, because `A` blocks that line; and moving `Q` away
would empty `B`. Hence, going back from the departure, `Q` stays on `B` for as
long as `A` stays occupied: while the openable piece sits on `A`, `Q` is
neither moved nor captured. Corollary 3.4's second half holds for every move:
when the mover's king is in check and does not move, the destination is the
checker's square or lies on its line.

The interval argument depends only on the direct-check property of glaring
destinations and on fixed kings, not on periodicity itself. Intervals that wrap
around the period, and the existence of a later departure, are left to a later
Part. -/

namespace MPC

private theorem toInt_toPos (q : ℤ × ℤ) (h : onBoard q) : (toPos q h).toInt = q := by
  obtain ⟨h1, _, h2, _⟩ := h
  ext
  · simp [toPos, Pos.toInt]; omega
  · simp [toPos, Pos.toInt]; omega

/-- An occupied square on the line from `B` to `K` blocks every slide from `B`
    to `K`, so only a step attack can remain. -/
theorem stepAttack_of_attacks_of_blocked (board : Board) (owner : Player) (pt : PieceType)
    (B K A : Pos) (h : attacksOriented board owner pt B K) (hA : A.toInt ∈ slidePath B K)
    (hocc : board.grid A ≠ none) :
    Pos.dirTo B K ∈ pt.stepDirs.map (Dir.forPlayer · owner) := by
  rcases h with hs | ⟨_, _, _, _, _, _, _, hc⟩
  · exact hs
  · have h := hc A.toInt hA (Pos.onBoard_toInt A) (Pos.onBoard_toInt A)
    rw [Pos.toPos_toInt] at h
    exact absurd h hocc

namespace MoveTrace

/-- Every move whose destination glares afterwards is a direct check by the
    destination piece. -/
def GlaringDestinationsCheck (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) : Prop :=
  ∀ i : Fin tr.len, tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination →
    hasDestinationCheckerOriented (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent)

/-- In a periodic trace satisfying 's premises, glaring destinations are
    direct checks: a board move to a glaring square moves a glaring piece
    (Lemma 2.8), which has no unblocked checker (Lemma 2.5); a drop never has one. -/
theorem glaringDestinationsCheck_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) : tr.GlaringDestinationsCheck kp := by
  intro i hg
  rcases (tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe kp ht hs hk hsafe
    h0).mp hc i with hdc | hu
  · exact hdc
  · exfalso
    rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
    · have hg' : tr.GlaresAtEnemyKing kp i.succ dst := by
        rw [hm] at hg
        exact hg
      have hsrc := tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr
        hp i src dst promote hm hg'
      exact tr.not_unblockedChecker_of_source_glares kp ht hs hk hsafe h0 i src dst promote hm
        hsrc hu
    · rw [hm] at hu
      exact hu

/-- In such a trace, moving a non-glaring piece is a discovered check: its
    destination does not glare (Lemma 2.8), so Lemma 2.4 gives an unblocked
    checker. -/
theorem unblockedChecker_of_not_glares_source_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) :
    hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) :=
  (tr.everyMoveChecksOpponent_glares_or_unblocked kp ht hs hk hsafe h0 hc i).resolve_left
    fun hg => hns (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr
      hp i src dst promote hm (by rw [hm] at hg; exact hg))

/-- One step back: if `B` holds a glaring `Q` after move `i` and `A` is occupied
    then, `B` held `Q` before the move. -/
private theorem grid_castSucc_of_succ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hd : tr.BoardMoveEndpointsDistinct)
    (hkp : ∀ k, kp k = kp 0) (hgd : tr.GlaringDestinationsCheck kp) (i : Fin tr.len)
    (B A : Pos) (Q : Piece) (hQ : (tr.states i.succ).board.grid B = some Q)
    (hgl : tr.GlaresAtEnemyKing kp i.succ B)
    (hA : A.toInt ∈ slidePath B (kp 0 Q.owner.opponent))
    (hstep : Pos.dirTo B (kp 0 Q.owner.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner))
    (hocc : (tr.states i.succ).board.grid A ≠ none) :
    (tr.states i.castSucc).board.grid B = some Q := by
  -- A move onto `B` would be a direct check through the occupied `A`.
  have harrive : (tr.moves i).destination ≠ B := by
    intro hdest
    obtain ⟨piece, hp, hown, ha⟩ := hgd i (hdest ▸ hgl)
    rw [hdest] at hp ha
    have hpq : piece = Q := Option.some.inj (hp.symm.trans hQ)
    subst hpq
    have ho : (tr.before i).turn.opponent = piece.owner.opponent := by
      rw [hown, Player.opponent_opponent]
    rw [hkp, ho] at ha
    exact hstep (stepAttack_of_attacks_of_blocked _ _ _ _ _ A ha hA hocc)
  rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · rw [hm] at harrive
    have hdB : B ≠ dst := fun h => harrive (h ▸ rfl)
    have hsB : B ≠ src := by
      rintro rfl
      have := tr.boardMove_grid_src ht i B dst promote hm (hd i B dst promote hm)
      change (tr.states i.succ).board.grid B = none at this
      rw [hQ] at this
      cases this
    have := tr.boardMove_grid_other ht i src dst promote B hm hsB hdB
    change (tr.states i.succ).board.grid B = (tr.states i.castSucc).board.grid B at this
    rw [← this]
    exact hQ
  · rw [hm] at harrive
    have hdB : B ≠ dst := fun h => harrive (h ▸ rfl)
    have := tr.dropMove_grid_other ht i pt dst B hm hdB
    change (tr.states i.succ).board.grid B = (tr.states i.castSucc).board.grid B at this
    rw [← this]
    exact hQ

/-- Proposition 3.3's core, without periodicity. Suppose glaring destinations
    are direct checks and the kings stay put. If `B` holds a glaring `Q` at state
    `b` whose line to the enemy king runs through `A`, `Q` attacks by sliding
    there, and `A` is occupied in every state of `(a, b]`, then `B` holds `Q` in
    every state of `[a, b]`: it was neither moved nor captured. -/
theorem grid_eq_of_glares_through_occupied (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hd : tr.BoardMoveEndpointsDistinct)
    (hkp : ∀ k, kp k = kp 0) (hgd : tr.GlaringDestinationsCheck kp)
    {a b : Fin (tr.len + 1)} (B A : Pos) (Q : Piece)
    (hQ : (tr.states b).board.grid B = some Q) (hgl : tr.GlaresAtEnemyKing kp b B)
    (hA : A.toInt ∈ slidePath B (kp 0 Q.owner.opponent))
    (hstep : Pos.dirTo B (kp 0 Q.owner.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner))
    (hocc : ∀ k : Fin (tr.len + 1), a < k → k ≤ b → (tr.states k).board.grid A ≠ none) :
    ∀ k : Fin (tr.len + 1), a ≤ k → k ≤ b → (tr.states k).board.grid B = some Q := by
  have key : ∀ n : ℕ, ∀ k : Fin (tr.len + 1), k.val + n = b.val → a ≤ k →
      (tr.states k).board.grid B = some Q := by
    intro n
    induction n with
    | zero =>
      intro k hk _
      rw [show k = b from Fin.ext (by omega)]
      exact hQ
    | succ n ih =>
      intro k hk hak
      have hkl : k.val < tr.len := by have := b.isLt; omega
      let i : Fin tr.len := ⟨k.val, hkl⟩
      have hki : k = i.castSucc := Fin.ext rfl
      have hab : a < i.succ := by
        rw [Fin.le_def] at hak
        rw [Fin.lt_def, Fin.val_succ]
        show a.val < k.val + 1
        omega
      have hib : i.succ ≤ b := by
        rw [Fin.le_def, Fin.val_succ]
        show k.val + 1 ≤ b.val
        omega
      have hs : (tr.states i.succ).board.grid B = some Q :=
        ih i.succ (by rw [Fin.val_succ]; show k.val + 1 + n = b.val; omega) (le_of_lt hab)
      have hgl' : tr.GlaresAtEnemyKing kp i.succ B :=
        (tr.glaresAtEnemyKing_congr kp ht (hs.trans hQ.symm) ((hkp _).trans (hkp _).symm)).mpr hgl
      rw [hki]
      exact grid_castSucc_of_succ tr kp ht hd hkp hgd i B A Q hs hgl' hA hstep
        (hocc i.succ hab hib)
  intro k hak hkb
  rw [Fin.le_def] at hkb
  exact key (b.val - k.val) k (by omega) hak

/-- Proposition 3.3 in a linear-interval form: in a periodic trace satisfying
    's premises, when a non-glaring piece leaves `A` by move `j`, some
    piece `Q` of the mover stands on a square `B` whose glaring line to the enemy
    king runs through `A`. Throughout any interval before `j` in which `A` stays
    occupied, `Q` stays on `B` and keeps glaring. -/
theorem openable_glaring_line_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (j : Fin tr.len) (A dst : Pos) (promote : Bool)
    (hm : tr.moves j = .boardMove A dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp j.castSucc A) {a : Fin (tr.len + 1)}
    (hocc : ∀ k : Fin (tr.len + 1), a < k → k ≤ j.castSucc →
      (tr.states k).board.grid A ≠ none) :
    ∃ (B : Pos) (Q : Piece), Q.owner = (tr.before j).turn ∧
      A.toInt ∈ slidePath B (kp 0 (tr.before j).turn.opponent) ∧
      ∀ k : Fin (tr.len + 1), a ≤ k → k ≤ j.castSucc →
        (tr.states k).board.grid B = some Q ∧ tr.GlaresAtEnemyKing kp k B := by
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hgd := tr.glaringDestinationsCheck_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hu := tr.unblockedChecker_of_not_glares_source_of_periodic kp ht hs hk hsafe h0 hc hr hp
    j A dst promote hm hns
  rw [hm] at hu
  obtain ⟨B, Q, _, _, hQ0, hQ1, hQo, hatk, hmem, _, _, _⟩ := hu
  have hown : Q.owner = (tr.before j).turn := by rw [hQo, Player.opponent_opponent]
  have hopp : (tr.before j).turn.opponent = Q.owner.opponent := by rw [hown]
  rw [hconst j.succ, hopp] at hatk hmem
  have hgl1 : tr.GlaresAtEnemyKing kp j.succ B :=
    tr.glaresAtEnemyKing_of_attacks kp j.succ B Q hQ1 (by rw [hconst j.succ]; exact hatk)
  have hgl0 : tr.GlaresAtEnemyKing kp j.castSucc B :=
    (tr.glaresAtEnemyKing_congr kp ht (hQ0.trans hQ1.symm)
      ((hconst _).trans (hconst _).symm)).mpr hgl1
  have hstep : Pos.dirTo B (kp 0 Q.owner.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
    intro hst
    apply tr.before_opponent_not_inCheck kp ht hsafe h0 j
    refine ⟨B, Q, hQ0, by rw [hown, Player.opponent_opponent], Or.inl ?_⟩
    rw [hconst j.castSucc, hopp]
    exact hst
  have hgrid := tr.grid_eq_of_glares_through_occupied kp ht hd hconst hgd (b := j.castSucc)
    B A Q hQ0 hgl0 hmem hstep hocc
  refine ⟨B, Q, hown, by rw [hopp]; exact hmem, fun k hak hkb => ⟨hgrid k hak hkb, ?_⟩⟩
  exact (tr.glaresAtEnemyKing_congr kp ht ((hgrid k hak hkb).trans hQ0.symm)
    ((hconst _).trans (hconst _).symm)).mpr hgl0

/-- Corollary 3.4's second half, without periodicity: if an enemy piece `X` on `C`
    attacks the mover's king and that king does not move, the move lands on `C`
    (capturing the checker) or on `X`'s sliding line to the king. Otherwise `X`
    keeps its attack and the mover's king stays in check. -/
theorem destination_on_checker_line (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (i : Fin tr.len)
    (hkm : kp i.succ (tr.before i).turn = kp i.castSucc (tr.before i).turn)
    (C : Pos) (X : Piece) (hX : (tr.before i).board.grid C = some X)
    (hXo : X.owner = (tr.before i).turn.opponent)
    (hatk : attacksOriented (tr.before i).board X.owner X.pieceType C
      (kp i.castSucc (tr.before i).turn)) :
    (tr.moves i).destination = C ∨
      ((tr.moves i).destination.toInt ∈ slidePath C (kp i.castSucc (tr.before i).turn) ∧
        Pos.dirTo C (kp i.castSucc (tr.before i).turn) ∉
          X.pieceType.stepDirs.map (Dir.forPlayer · X.owner)) := by
  by_contra hcon
  rw [not_or, not_and_or] at hcon
  obtain ⟨hdC, hrest⟩ := hcon
  -- Only the destination can become occupied.
  have hempty : ∀ q, q ≠ (tr.moves i).destination → (tr.before i).board.grid q = none →
      (tr.after i).board.grid q = none := by
    intro q hq hn
    rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
    · rw [hm] at hq
      by_cases hqs : q = src
      · rw [hqs]
        exact tr.boardMove_grid_src ht i src dst promote hm fun h => hq (hqs.trans h)
      · rw [tr.boardMove_grid_other ht i src dst promote q hm hqs hq]
        exact hn
    · rw [hm] at hq
      rw [tr.dropMove_grid_other ht i pt dst q hm hq]
      exact hn
  -- The checker stays on `C`.
  have hXa : (tr.after i).board.grid C = some X := by
    rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
    · rw [hm] at hdC
      have hCs : C ≠ src := by
        rintro rfl
        obtain ⟨piece, hp, ho⟩ := hs i C dst promote hm
        rw [hX] at hp
        cases hp
        exact Player.opponent_ne_self _ (hXo.symm.trans ho)
      rw [tr.boardMove_grid_other ht i src dst promote C hm hCs (Ne.symm hdC)]
      exact hX
    · rw [hm] at hdC
      rw [tr.dropMove_grid_other ht i pt dst C hm (Ne.symm hdC)]
      exact hX
  -- The attack survives.
  have hatk' : attacksOriented (tr.after i).board X.owner X.pieceType C
      (kp i.castSucc (tr.before i).turn) := by
    rcases hatk with hst | ⟨sd, hsd, hn, k, hk1, hx, hy, hpc⟩
    · exact Or.inl hst
    · rcases hrest with hnot | hstep
      · refine Or.inr ⟨sd, hsd, hn, k, hk1, hx, hy, ?_⟩
        intro q hq hob hproof
        have hne : toPos q hproof ≠ (tr.moves i).destination := by
          intro he
          apply hnot
          rw [← he, toInt_toPos]
          exact hq
        exact hempty _ hne (hpc q hq hob hproof)
      · exact Or.inl (not_not.mp hstep)
  apply hsafe i
  refine ⟨C, X, hXa, hXo, ?_⟩
  rw [hkm]
  exact hatk'

/-- Corollary 3.4 in a linear-interval form: in a periodic trace satisfying
    's premises, let move `i` put a piece on `A` and a later move `j` move a
    non-glaring piece off `A`, with `A` occupied in between. Then right after
    move `i`, `A` lies on the glaring line of a piece of the departing side; and
    if an enemy piece attacked the mover's king before move `i`, `A` is that
    checker's square or lies on its sliding line to the king. -/
theorem openable_destination_lines_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i j : Fin tr.len) (A : Pos) (hmi : (tr.moves i).destination = A)
    (dst : Pos) (promote : Bool) (hmj : tr.moves j = .boardMove A dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp j.castSucc A) (hij : i.succ ≤ j.castSucc)
    (hocc : ∀ k : Fin (tr.len + 1), i.succ < k → k ≤ j.castSucc →
      (tr.states k).board.grid A ≠ none)
    (C : Pos) (X : Piece) (hX : (tr.before i).board.grid C = some X)
    (hXo : X.owner = (tr.before i).turn.opponent)
    (hatk : attacksOriented (tr.before i).board X.owner X.pieceType C
      (kp i.castSucc (tr.before i).turn)) :
    (∃ (B : Pos) (Q : Piece), Q.owner = (tr.before j).turn ∧
      A.toInt ∈ slidePath B (kp 0 (tr.before j).turn.opponent) ∧
      (tr.states i.succ).board.grid B = some Q ∧ tr.GlaresAtEnemyKing kp i.succ B) ∧
    (A = C ∨ (A.toInt ∈ slidePath C (kp i.castSucc (tr.before i).turn) ∧
      Pos.dirTo C (kp i.castSucc (tr.before i).turn) ∉
        X.pieceType.stepDirs.map (Dir.forPlayer · X.owner))) := by
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨B, Q, hown, hmem, hall⟩ := tr.openable_glaring_line_of_periodic kp ht hs hk hsafe h0 hc
    hr hp j A dst promote hmj hns (a := i.succ) hocc
  refine ⟨⟨B, Q, hown, hmem, hall i.succ (le_refl _) hij⟩, ?_⟩
  have h := tr.destination_on_checker_line kp ht hs hsafe i
    (by rw [hconst i.succ, hconst i.castSucc]) C X hX hXo hatk
  rw [hmi] at h
  exact h

end MoveTrace
end MPC
