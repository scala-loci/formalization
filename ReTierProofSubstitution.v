Require Import ReTierSyntax.
Require Import ReTierStaticSemantics.
Require Import ReTierDynamicSemantics.

Lemma substitution_preserves_typing_t : forall
    (typing: peerTyping)
    (ties: Ties)
    (react: reactEnv)
    (Delta: placeEnv)
    (Gamma: varEnv)
    (peer: P)
    (x: id)
    (U: T)
    (value: t)
    (term: t)
    (S: T),
  Context typing ties react Delta (idUpdate x U Gamma) peer |- term \in S ->
  Context typing ties react emptyPlaceEnv emptyVarEnv peer |- value \in U ->
  Context typing ties react Delta Gamma peer |- [x :=_t value] term \in S.

Lemma substitution_preserves_typing_s : forall
    (typing: peerTyping)
    (ties: Ties)
    (react: reactEnv)
    (Delta: placeEnv)
    (Gamma: varEnv)
    (peer: P)
    (x: id)
    (U: S)
    (value: t)
    (term: s)
    (S: T),
  PlacementContext typing ties react (idUpdate x U Delta) |~ term ->
  Context typing ties react emptyPlaceEnv emptyVarEnv peer |- value \in S ->
  PlacementContext typing ties react Delta |~ [x :=_s value] term.
