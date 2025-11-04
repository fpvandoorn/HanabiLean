import Mathlib.Data.Real.Basic

/-! # General games -/

/-- An incomplete-information asynchronous multiplayer game. -/
structure Game : Type _ where
  Player : Type
  /-- The state of a game.
  Should typically encode the full game history and any future randomness. -/
  State : Type
  /-- The information state a player can have. -/
  Information : Type
  /-- Possible actions. -/
  Action : Type
  /-- The possible set of starting states
  * currently assuming a uniform distribution on these, we could change that. -/
  startingStates : Set State
  /-- The information of a player at a turn. -/
  info : State → Player → Information
  /-- the player whose move it is.
  * We allow for the fact that not everyone knows whose turn it is.
  -/
  current : State → Player
  /-- The allowed actions on a turn.
  * The valid actions can only depend on what the current player knows.
  * We encode the end of the game by making this the empty set.
  * Currently we allow for situations where players might not know
    whether an action of another player is valid.
  -/
  valid : Information → Set Action
  /-- the state after an action. -/
  next : State → Action → State
  /-- the score of a player at a state.
  * need not be meaningful when the game is ongoing.
  * doesn't depend on the player-variable in fully cooperative games. -/
  score : State → Player → ℝ

variable {G : Game}

namespace Game

def State.info := Game.info G
def State.current := Game.current G
def Information.valid := Game.valid G
def State.next := Game.next G
def State.score := Game.score G

/-- The valid actions in state `S`. -/
def State.valid (S : G.State) : Set G.Action :=
  S.info S.current |>.valid

/-- The game has ended at state `S`. -/
def State.IsGameEnd (S : G.State) : Prop :=
  S.valid = ∅

/-- `P` is known to be true by a `p` at state `S` if it holds
for every state compatible with the current information of player `p`. -/
def State.IsKnownBy (P : G.State → Prop) (S : G.State) (p : G.Player) : Prop :=
  ∀ S' ∈ (G.info · p) ⁻¹' {G.info S p}, P S'

/-- `P` is known to be either true or false by a `p` at state `S`. -/
def State.IsDecidableBy (S : G.State) (P : G.State → Prop) (p : G.Player) : Prop :=
  S.IsKnownBy P p ∨ S.IsKnownBy (¬ P ·) p

/-!  Some nice properties to have in a game. -/

/-- Everyone knows whether the game has ended. -/
def KnowGameEnd : Prop := ∀ (S : G.State) (p : G.Player), S.IsDecidableBy State.IsGameEnd p
/-- Every player knows whether it's their turn. -/
def KnowCurrent : Prop := ∀ (S : G.State) (p : G.Player), S.IsDecidableBy (State.current · = p) p
/-- Every player remembers the previous game state and knows the last action. -/
def GoodKnowledge : Prop :=
  ∀ ⦃S S' : G.State⦄ ⦃A A' : G.Action⦄ (p : G.Player) (_h : A ∈ S.valid) (_h' : A' ∈ S'.valid)
  (_eq : (S.next A).info p = (S'.next A').info p), S.info p = S'.info p ∧ A = A'

/-- Exercise: given a game, define a new game where the last action taken is public information. -/
def withAction (G : Game) : Game where
  Player := G.Player
  State := G.State × Option G.Action
  Information := G.Information × Option G.Action
  Action := G.Action
  startingStates := sorry
  info := sorry
  current := sorry
  valid := sorry
  next := sorry
  score := sorry

/-- Exercise: given a game,
define a new game where every player remembers their previous information. -/
def withPrev (G : Game) : Game where
  Player := G.Player
  State := List G.State
  Information := List G.Information
  Action := G.Action
  startingStates := sorry
  info := sorry
  current := sorry
  valid := sorry
  next := sorry
  score := sorry

/- Exercise: given a game `G`, show that `G.withAction.withPrev` satisfies `GoodKnowledge`. -/


/-- A game convention -/
structure Convention (G : Game) : Type _ where
  /- Is `A` a conventional action with information `I`?
  True: conventional
  False: unconventional
  none: this convention doesn't apply for this action. -/
  IsConventional (I : G.Information) (A : G.Action) : Option Prop

namespace Convention

/-- Does a convention apply to the current action? -/
def Applies (C : G.Convention) (I : G.Information) (A : G.Action) : Prop :=
  C.IsConventional I A |>.isSome

/-- Combine multiple conventions, where the priority of a convention is given by the order on `ι`.
An action is conventional if the largest convention that applies says it is. -/
def combine {ι : Type} [CompleteLinearOrder ι] (C : ι → Convention G) : Convention G where
  IsConventional I A :=
    /- The relevant convention. Note that when the set over which we take the supremum is empty,
    `combine` still gives the right value `none`. -/
    let i := sSup {i : ι | C i |>.Applies I A }
    C i |>.IsConventional I A


end Convention

end Game
