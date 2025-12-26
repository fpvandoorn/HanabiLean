import Mathlib.Data.Real.Archimedean

set_option linter.unusedVariables false

/-! # General games -/

/-- An incomplete-information asynchronous multiplayer game. -/
structure Game : Type _ where
  Player : Type
  /-- The state of a game.
  Should typically encode the full game history and any future randomness. -/
  State : Type
  /-- The information state a player can have. -/
  Info : Type
  /-- Possible actions. -/
  Action : Type
  /-- The possible set of starting states
  * currently assuming a uniform distribution on these, we could change that. -/
  start : Set State
  /-- The information of a player at a turn. -/
  info : State → Player → Info
  /-- Every player knows who they are -/
  me : Info → Player
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
  valid : Info → Set Action
  /-- the state after an action. -/
  next : State → Action → State
  /-- the score of a player at a state.
  * need not be meaningful when the game is ongoing.
  * doesn't depend on the player-variable in fully cooperative games. -/
  score : State → Player → ℝ
  [inhabited_state : Inhabited State]
  [inhabited_action : Inhabited Action]

variable {G : Game}

namespace Game

attribute [instance] inhabited_state inhabited_action
instance : Inhabited G.Player := ⟨G.current default⟩
instance : Inhabited G.Info := ⟨G.info default default⟩

def State.info := Game.info G
def State.current := Game.current G
def Info.valid := Game.valid G
def Info.me := Game.me G
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
def KnowGameEnd (G : Game) : Prop :=
  ∀ (S : G.State) (p : G.Player), S.IsDecidableBy State.IsGameEnd p
/-- Every player knows whether it's their turn. -/
def KnowCurrent (G : Game) : Prop :=
  ∀ (S : G.State) (p : G.Player), S.IsDecidableBy (State.current · = p) p

/-- Every player remembers the previous game state and knows the last action. -/
class GoodKnowledge (G : Game) where
  /-- The information a player had last turn -/
  prev : G.Info → Option G.Info
  /-- Every player can deduce what player played the last action and which action they played. -/
  prevAction : G.Info → Option (G.Player × G.Action)

def Info.prev := @GoodKnowledge.prev
def Info.prevAction := @GoodKnowledge.prevAction

def Info.prev! [GoodKnowledge G] (I : G.Info) : G.Info := I.prev.get!
def Info.prevAction! [GoodKnowledge G] (I : G.Info) : G.Player × G.Action := I.prevAction.get!

noncomputable def maxScore (p : G.Player) : WithTop ℝ :=
  ⨆ s : G.State, s.score p

/-- Is state `t` a possible state after performing 1 move in state `s`? -/
noncomputable def State.IsNext (T S : G.State) : Prop :=
  T ∈ S.next '' S.valid

/-- Is state `t` reachable from state `s`? -/
noncomputable def State.Reachable (T S : G.State) : Prop :=
  Relation.ReflTransGen State.IsNext T S

/-- Maximal possible score for player `p`. -/
noncomputable def Player.maxScore (p : G.Player) : WithTop ℝ :=
  ⨆ (S : G.State) (_ : S.IsGameEnd), S.score p

/-- Maximal possible score for player `p` reachable from state `S`. -/
noncomputable def State.maxScore (S : G.State) (p : G.Player) : WithTop ℝ :=
  ⨆ (T : G.State) (_ : T.IsGameEnd) (_ : T.Reachable S) , T.score p


/-- Given a game, we define a new game where the last action taken (and who took it)
is public information. -/
def withAction (G : Game) : Game where
  Player := G.Player
  State := G.State × Option (G.Player × G.Action)
  Info := G.Info × Option (G.Player × G.Action)
  Action := G.Action
  start := (·, none) '' G.start
  info S p := (G.info S.1 p, S.2)
  me S := G.me S.1
  current S := G.current S.1
  valid S := G.valid S.1
  next S A := (G.next S.1 A, S.1.current, A)
  score S := G.score S.1

/-- Given a game, we define a new game where every player remembers their previous information.
We use `α × List α` to talk about nonempty lists on `α`. -/
def withPrev (G : Game) : Game where
  Player := G.Player
  State := G.State × List G.State
  Info := G.Info × List G.Info
  Action := G.Action
  start := (·, []) '' G.start
  info S p := (G.info S.1 p, S.2.map (G.info · p))
  me S := G.me S.1
  current S := G.current S.1
  valid S := G.valid S.1
  next S A := (G.next S.1 A, S.1 :: S.2)
  score S := G.score S.1

/- Given a game `G`, show that `G.withAction.withPrev` satisfies `GoodKnowledge`. -/
instance (G : Game) : GoodKnowledge G.withAction.withPrev where
  prev I := match I.2 with
    | []    => none
    | i::is => some (i, is)
  prevAction I := I.1.2

def Info.orig (S : G.withAction.withPrev.Info) : G.Info := S.1.1
def State.orig (S : G.withAction.withPrev.State) : G.State := S.1.1

/-!
# Conventions

A *hanabi*-convention is an agreement between players.

We want to formalize the notion of conventions with three criteria:
* We should be able to write a convention system with modular conventions
* We should be able to define some simple conventions without too much effort,
  and potentially prove things about them.

To make conventions convenient, the players need some additional state
(e.g. playable cards, chop moved cards).
Note that this information must be shared between conventions:
a new convention might add a way to chop move cards,
and any already existing convention should use the same notion of chop moved cards.

We therefore make the additional state type an argument to conventions:
then we can easily talk about conventions with the same state.
-/

/-- A game convention -/
structure Convention (G : Game) (Info : Type) : Type _ where
  /-- Is action `A` a conventional action with information `I` and `I'`?
  True: conventional
  False: unconventional
  none: this convention doesn't apply for this action. -/
  IsConventional (I : G.Info) (I' : Info) (A : G.Action) : Option Bool
  /-- Hoe does `me` update their info *after* `p` performs `A`?
  Here `I` is the game state known by a player *after* the action has occurred. -/
  update (I : G.Info) (I' : Info) : Info

namespace Convention
variable {Info : Type} {C : G.Convention Info}

/-- Does a convention apply to the current action? -/
def Applies (I : G.Info) (I' : Info) (A : G.Action) : Bool :=
  C.IsConventional I I' A |>.isSome

/-- Combine multiple conventions, where the priority of a convention is given by the order on `ι`.
An action is conventional if the largest convention that applies says it is.
`u` is an update function that is always applied first. -/
def combine [G.GoodKnowledge] {ι : Type} [CompleteLinearOrder ι] (C : ι → G.Convention Info)
  (u : Π (I : G.Info) (I' : Info), Info) :
    G.Convention Info where
  IsConventional I I' A :=
    /- The relevant convention. Note that when the set over which we take the supremum is empty,
    `combine` still gives the right value `none`. -/
    let i := sSup {i : ι | C i |>.Applies I I' A }
    C i |>.IsConventional I I' A
  update I I' :=
    /- todo: this is not right: the receiving player of the clue cannot always decide *which*
    convention was used to make this clue conventional.
    One way to fix this is to have a high-priority convention that encodes the ambiguity.
    e.g.
    * color-play clues can be given on a playable card
    * color-save clues can be given on a critical card (or 2) on chop
    * The save-convention could have higher-priority, and has to encode that the card is either
      playable or critical or a 2.
    -/
    let i := sSup {i : ι |
      ∃ pI pA, I.prev = some pI ∧ I.prevAction = some pA ∧
      (C i).IsConventional pI I' pA.2 == some true }
    C i |>.update I (u I I')

/--
Extend the conventional information.
To do this we need a projection `π` from the new datatype to the old one
and a modification function `m` such that `m I' I` is the information `I'`,
but with the part coming from `Info` coming updated with `I`.
-/
def extend {Info' : Type} (C : G.Convention Info) (m : Info' → Info → Info')
  (π : Info' → Info) : G.Convention Info' where
  IsConventional I I' A := C.IsConventional I (π I') A
  update I I' := m I' (C.update I (π I'))

end Convention

end Game
