(* The Coq Proof Assistant, version 8.8.1 (July 2018)
compiled on Jul 12 2018 17:07:04 with OCaml 4.02.3 *)

(* NB : pb de compatibilité selon version de coq sur les
  arguments implicites => tout est explicité *)

Require Import Utf8.
Require Import Bool.
Require Import Arith.

Require Import Ensembles.
Require Import Constructive_sets.
Require Import Powerset_facts.
Require Import Finite_sets.
Require Import Finite_sets_facts.

Notation "x '∈' E"      := (In _ E x) (at level 40).
Notation "'∅'"          := (Empty_set _) (at level 40).
Notation "A '⊆' B"      := (Included _ A B) (at level 40).
Notation "S ∪ T"        := (Union _ S T) (at level 40).
Notation "S ∩ T"        := (Intersection _ S T) (at level 40).
Notation "'{|' x '|}'"  := (Singleton _ x) (at level 40).


Section BinaryTree.

(*****************************************************************************************************)
(******** LIFLC : TD2 Induction, Ensemble inductif des arbres binaires de recherche PARTIE 1 *********)
(*****************************************************************************************************)

(****** Exercice 2, question 1 *****)
(* TYPE DE DONNEES PRINCIPAL : LES ARBRES BINAIRES CONTENANT DES ENTIERS NATURELS DANS LES NOEUDS *)


(* éléments dans les noeuds de l'arbre *)
Context {E:Set}.

(* égalité décidable, prendre eq_nat_dec pour Nat *)
Hypothesis E_eq_dec : forall x y:E, {x = y}+{x <> y}.

(* Search ({_ = _} + {_ <> _}).*)
(* on trouve le théorème de l'égalité décidable sur les entiers *)
(* eq_nat_dec: ∀ n m : nat, {n = m} + {n ≠ m} *)

Open Scope bool_scope.
(* pour avoir les notations usuelles || et && des opérateurs binaires orb et andb *)

Inductive BinTree : Set :=
  | leaf : BinTree 
  | node : BinTree -> E -> BinTree -> BinTree.

(****** Exercice 2, question 2, version calculatoire dans Set *****)
(******** FONCTION ELEMENTS ********)

(* fonction de recherche générique, sans hypothèse sur les éléments de l'arbre *)
Fixpoint elts (t:BinTree) (a:E) : bool :=
match t with
 | leaf       => false
 | node l e r => match (E_eq_dec a e) with
                  | left  _ => true
                  | right _ => (elts l a) || (elts r a)
                 end
end.

(****** Exercice 2, question 2, version logique dans Prop *****)
(******** FONCTION ELEMENTS ********)
Fixpoint elements (t:BinTree) : Ensemble E :=
match t with
 | leaf       => Empty_set E
 | node l e r => ({| e |}) ∪ (elements l) ∪  (elements r)
end.

Lemma elements_is_finite : forall (t:BinTree), (Finite _ (elements t)).
Proof.
induction t as [|l IHl e r IHr];  simpl.
- (* leaf *)
  constructor.
- (* node l e r *)
  auto using Union_preserves_Finite, Singleton_is_finite.
Qed.

(****** Exercice 2, question 3 *****)
(******** FONCTION ELEMENTS ********)
(* Montrer par induction sur Bin E que pour un arbre binaire a comportant n occurrences de l’arbre vide, | elements(a) |≤ n − 1 *)

Fixpoint count_leaves (t:BinTree) : nat :=
match t with
 | leaf       => 1
 | node l e r => (count_leaves l) + (count_leaves r)
end.

Lemma count_leaves_pos : forall t, 1 ≤ count_leaves t.
Proof.
induction t; simpl; auto.
apply le_trans with (1 + 1); auto.
apply plus_le_compat; auto.
Qed.

Fixpoint count_nodes (t:BinTree) : nat :=
match t with
 | leaf       => 0
 | node l e r => 1 + (count_nodes l) + (count_nodes r)
end.

Lemma cardinal_singleton : forall U x, cardinal U ({| x |}) 1.
Proof.
intros U x.
rewrite <- Empty_set_zero'.
constructor.
constructor.
auto with sets.
Qed.

Lemma cardinal_union_inter : forall l r nl nr n p, (cardinal E l nl) -> (cardinal E r nr) -> (cardinal E (l ∪ r) n) -> (cardinal E (l ∩ r) p) -> n + p = nl + nr.
Proof.
(* TODO :trop dur pour moi à faire en Coq, mais on est convaincus que c'est vrai ^^ *)
Admitted.


Lemma cardinal_union_le : forall l r nl nr n, (cardinal E l nl) -> (cardinal E r nr) -> (cardinal E (l ∪ r) n) -> n <= nl + nr.
Proof.
 intros l r nl nr n Hl Hr H.
 assert (exists p, cardinal _ (l ∩ r) p).
 {  apply finite_cardinal.
    apply Intersection_preserves_finite.
    eauto using cardinal_finite.
 }
 destruct H0 as [p Hp].
 apply le_trans with (n + p); auto with arith.
 rewrite (cardinal_union_inter l r nl nr); auto.
Qed.

Theorem bin_n_leaves_has_lesser_nodes :
    forall (t:BinTree) (m:nat), cardinal _ (elements t) m -> m <= (count_leaves t)- 1.
Proof.
induction t as [|l IHl e r IHr];  simpl; intros m Ha.
- (* as t = [] *)
  apply cardinal_Empty in Ha.
  subst m; auto.
- (* as t = node l e r *)
  (* on détruit les hypothèse sur les cardinaux *)
  destruct (finite_cardinal _ (elements l)) as [nl Hnl]; auto using elements_is_finite .
  destruct (finite_cardinal _ (elements r)) as [nr Hnr]; auto using elements_is_finite .
  destruct (finite_cardinal _ (elements l ∪ elements r)) as [nu Hnu]; auto using elements_is_finite, Union_preserves_Finite .
  (* on peut simplifier les hypothèses d'induction *)
  assert (nl ≤ (count_leaves l) - 1) as IHl' by auto using IHl.
  assert (nr ≤ (count_leaves r) - 1) as IHr' by auto using IHl.
  (* on met l'hypothèse sur le cardinal de la somme en forme *)
  rewrite Union_associative in Ha.

  (* on introduit 2 indégalités intermédiaires *)
  assert (nu  ≤  nl + nr) by apply (cardinal_union_le (elements l) (elements r) nl nr nu Hnl Hnr Hnu).
  assert (m  ≤ 1 + nu) by (apply (cardinal_union_le ({|e|})  (elements l ∪ elements r)); auto using cardinal_singleton).

  (* pour réécrire notre but *)
  apply le_trans with (1 + (nl +nr)).
  apply le_trans with (1 + (nu)); auto.
  apply plus_le_compat; auto.

  (* un peu d'arithmétique fastidieuse *)
  assert (count_leaves l + count_leaves r - 1 = 1 + (count_leaves l - 1) + (count_leaves r - 1)).
  {
    rewrite le_plus_minus_r; auto using count_leaves_pos.
    rewrite Nat.add_sub_assoc; auto using count_leaves_pos.
  }

  (* et maintenant, tout découle de ∀ n m p q : nat, n ≤ m → p ≤ q → n + p ≤ m + q *)
  rewrite H1.
  rewrite <- plus_assoc.
  apply plus_le_compat; auto.
  apply plus_le_compat; auto.
Qed.

(****** Exercice 2, digression sur l'appartenance *****)
(* INDUCTIF POUR L'APPARTENANCE ET CORRECTION w.r.t. la fct elts *)


(* InT est une propriété inductive : InT t n indique que n est un élément de t *)
Inductive InT : BinTree -> E ->  Prop :=
  | inNodeL l x : forall  n r, InT l x -> InT (node l n r) x
  | inNodeR r x : forall  n l, InT r x -> InT (node l n r) x
  | inNodeN x e : forall  l r, x = e   -> InT (node l e r) x.

(* Théorème "d'inversion" de InT *)
Lemma InT_inv : forall (l r:BinTree) (e a:E),
  InT (node l e r) a <-> (InT l a) \/ (InT r a) \/ a = e.
Proof.
intros l r e a; split; intro H.
 - inversion_clear H; auto using inNodeL, inNodeR, inNodeN.
 - destruct H; [|destruct H] ; auto using inNodeL, inNodeR, inNodeN.
Qed.

(* on montre que la fonction elts est correcte : si elle calcule que a est dans t,
   alors on a une preuve de InT t a *) 
(* HINT : utiliser
   orb_true_iff
     : ∀ b1 b2 : bool, b1 || b2 = true ↔ b1 = true ∨ b2 = true *)
(* HINT : utiliser la tactique case_eq (E_eq_dec a e) pour tester les différents cas *)
Lemma elts_sound :
  forall (t:BinTree) (a:E), (elts t a) = true -> InT t a.
Proof.
intros t a H.
induction t as [|l IHl e r IHr].
 + (* cas t = leaf *)
   discriminate H.
 + (* cas recursif node *)
   case_eq (E_eq_dec a e); intros Heq Hdec.
   - (* case a = e *)
     rewrite Heq.
     auto  using inNodeN.
   - (* case a <> e *)
     simpl in H; rewrite Hdec in H. 
     apply orb_true_iff in H.
     destruct H; auto using inNodeL, inNodeR.
Qed.

(* on montre que la fonction elts est complete : si on a une preuve de InT t a
   alors elle elts t a renvoit true *) 
(* HINT : utiliser
   orb_true_intro
     : ∀ b1 b2 : bool, b1 = true ∨ b2 = true → b1 || b2 = true *)
Lemma elts_complete : 
  forall (t:BinTree) (a:E), InT t a -> (elts t a) = true.
Proof.
induction t as [|l IHl e r IHr] ; intros a H; inversion_clear H as [? ? ? ? HL| ? ? ? ?  HR| ? ? ? ? HN].
  * case_eq (E_eq_dec a e).
     - intros Heq Hdec.
       simpl. rewrite Hdec. trivial. 
     - intros Hneq Hdec. 
       simpl. rewrite Hdec. apply orb_true_intro. left. auto.
  * case_eq (E_eq_dec a e).
     - intros Heq Hdec.
       simpl. rewrite Hdec. trivial. 
     - intros Hneq Hdec. 
       simpl. rewrite Hdec. apply orb_true_intro. right. auto.
  * case_eq (E_eq_dec a e).
     - intros Heq Hdec.
       simpl. rewrite Hdec. trivial. 
     - intros Hneq Hdec. 
       contradiction.
Restart.
(* on peut factoriser les branches identiques *)
induction t as [|l IHl e r IHr] ; intros a H; inversion_clear H as [? ? ? ? HL| ? ? ? ?  HR| ? ? ? ? HN];
 case_eq (E_eq_dec a e); intros Hae Hdec; simpl; rewrite Hdec; auto.
  - apply orb_true_intro; left; auto.
  - apply orb_true_intro; right; auto.
Qed.

Theorem elts_correct : forall (t:BinTree) (x:E), InT t x <-> (elts t x) = true.
Proof.
split; auto using elts_complete, elts_sound.
Qed.



(****** Exercice 2, digression sur le plus à gauche générique, question 5 *****)
(* FONCTION DE RECHERCHE DE L'ELEMENT LE PLUS A GAUCHE *)

(* fonction de recherche du noeud le plus à gauche dans un arbre *)
Fixpoint left_most (t:BinTree) : option E :=
match t with
 | leaf       => None
 | node l e _ => match l with
                  | leaf        => Some e
                  | node l' x r => left_most l
                  end
end.

(****** Exercice 2, question 5*****)
(* LA FONCTION DE RECHERCHE DE L'ELEMENT LE PLUS A GAUCHE DONNE LE MINIMUM*)

(* Méthode générale de preuve pour (left_most t)
  induction sur t:
  + cas t = leaf
     => cas souvent dégénéré, à résoudre avec discriminate
  + cas t = node l a r
     => faire un cas sur l (pas besoin d'hypothèse inductive suppl.) 
        - cas l = leaf
        - cas l = node l1 al r1
  
  On peut utiliser la tactique suivante pour générer les 3 cas en nommant les hypo thèses :
  induction t as [|l IHl a r IHr]; [|destruct l as [|l1 el l2]].
*)

(* L'élément retourné, s'il y en a un, est bien un élément de l'arbre *)
Lemma left_most_some_implies_in : forall t (e:E),(left_most t = Some e) -> InT t e.
Proof.
intros t e Hmin.
induction t as [|l IHl a r IHr]; try discriminate Hmin.
destruct l as [|l1 el t2].
   * injection Hmin; intro H.
     rewrite H.
     auto using inNodeN.
   * apply IHl in Hmin.
     apply inNodeL.
     assumption.
Qed.

(* Lemme technique simple pour éliminer les cas impossibles où l'arbre serait vide *)
Lemma left_most_none_implies_leaf : forall t, (left_most t = None) -> t = leaf.
Proof.
intros t.
induction t as [|l IHl a r IHr]; intros H.
 + reflexivity.
 + destruct l.
   - discriminate H.
   - apply IHl in H.
     discriminate H.
Qed.


(* HINT : utiliser la tactique case_eq (left_most (node l1 el l2)). *)
Lemma elts_implies_left_most_some : forall t, (exists e, (elts t e) = true) -> (exists n, left_most t = Some n) .
Proof.
intros t [e He].
induction t as [|l IHl a r IHr]; [|destruct l as [|l1 el l2]].
 - (* t is leaf *) 
   discriminate He.
 - (* l1 is leaf *)
   exists a; auto.
 - (* l1 is node *)
   case_eq (left_most (node l1 el l2)).
  + intros n Hn.
    exists n.
    trivial.
  + intros H.
    apply left_most_none_implies_leaf  in H.
    discriminate H.
Qed.

(* HINT : il faut tout simplifier pour rendre les théorèmes précédents applicables *)
Theorem left_most_iff_elt :  forall t, (exists e, (elts t e = true)) <-> (exists n, left_most t = Some n) .
Proof.
split; intros H.
 - auto using elts_implies_left_most_some.
 - destruct H as  [n Hn].
   exists n.
   apply elts_correct.
   auto using left_most_some_implies_in.
Qed.

End BinaryTree.


(*****************************************************************************************************)
(******** LIFLC : TD2 Induction, Ensemble inductif des arbres binaires de recherche PARTIE 2 *********)
(*****************************************************************************************************)

(* ICI ON SE SPECIALISE AVEC NAT, MAIS ON POURRAIT LE FAIRE PLUS GENERALEMENT *)

Section BinarySearchTree.

(****** Exercice 2, question 4 *****)
(* BINARY SEARCH TREE *)
(* ================== *)

Definition NatBinTree := @BinTree nat.

(* Définition inductive de "être de recherche" *)
Inductive BST : NatBinTree  ->  Prop :=
 | bstLeaf : BST leaf
 | bstNode (l r:BinTree) (n:nat) :
   BST l -> (forall x:nat, InT l x -> x < n) -> 
   BST r -> (forall x:nat, InT r x -> n < x) -> BST (node l n r).


(****** Exercice 2, question 6 *****)
(* THEOREME PRINCIPAL : LA VALEUR LA PLUS A GAUCHE D'UN ARBRE BINAIRE DE RECHERCHE EST LA PLUS PETITE DE SES ELEMENTS *)

Theorem left_most_correct :
  forall t:NatBinTree, BST t ->
 (forall e:nat, left_most t = Some e -> (forall n, (InT t) n -> e < n \/ n = e)). 
Proof.
intros t. induction t as [|l IHl a r IHr]; intros HBST.
* (* t = leaf *)
  intros  e He n.
  simpl in He. discriminate He.
* (* t = node l a r *)
  destruct l as [|l1 el l2].
 + (* l = leaf *)
   intros e He n H.
   simpl in He. 
   inversion He as [Hae].
   rewrite Hae in H.
   inversion_clear H as  [? ? ? ? HL| ? ? ? ?  HR| ? ? ? ? HN].
   (* inversion de InT *)
   (* pour chacun des cas des 3 cas *)
    - (* InT (leaf nat) n *) 
      inversion HL.
    - (* InT r n *) 
      inversion_clear HBST as [|l1 r1 el HBSTl1 HMin1 HBSTr1 HMinr].
      left.
      rewrite Hae in HMinr. auto.
    - (* e = n *)
      right. auto.
 + (* l = node l1 el l2*)
      intros e He n H.
      inversion_clear H as  [? ? ? ? HL| ? ? ? ?  HR| ? ? ? ? HN].
    - (* elts l n *)
      apply IHl; [ inversion HBST | |]; auto.
    - (* elts r n *)
      inversion_clear HBST as [|tl tr te HBSTtl HMintl HBSTtr HMintr].
      apply HMintr in HR. (*we already have a < n, thus if e < a we're done *)
      left.
      apply lt_trans with (m := a) ; try assumption.
      auto using left_most_some_implies_in.
    - (* a = n *)
      left.
      rewrite HN. 
      inversion_clear HBST as [|tl tr te HBSTtl HMintl HBSTtr HMintr].
      auto using left_most_some_implies_in.
Qed.

(* on encapsule les résultats précédents dans l'énoncé de la propriété telle que formulée dans le TD2*)
Theorem left_most_td2 :
  forall (t:NatBinTree),
  BST t -> (left_most t = None /\ ~ exists e, (InT t e) )
             \/
           (exists e, left_most t = Some e /\ (InT t e) /\ (forall n, (InT t n) -> e < n \/ n = e)).
Proof.
induction t as [|l IHl a r IHr]; intros HBST; [left | right]. 
* (* case t = leaf *)
 split; auto.
 intros [x Hx].
 inversion Hx.
* (* case t = node l a r *)
  case_eq (left_most (node l a r)).
 - intros.
   exists n. split;trivial. split.
   + auto using left_most_some_implies_in.
   + eauto using left_most_correct.
 - intros H.
   apply left_most_none_implies_leaf in H.
   discriminate H.
Qed.


(*****************************************************************************************************)
(******** LIFLC : TD2 Induction, Ensemble inductif des arbres binaires de recherche PARTIE 3 *********)
(*****************************************************************************************************)

(* Du rab, mais on en a très envie  : la recherche dichotomique *)

(* FONCTION DE RECHERCHE DICHOTOMIQUE *)
(* ================================== *)

(* on utilise la comparaison nat_compare dans la fonction de recherche
  https://coq.inria.fr/library/Coq.Init.Datatypes.html#
  https://coq.inria.fr/library/Coq.Arith.Compare_dec.html

  On aura besoin des théorèmes qui montrent que cette comparaison est correcte

  nat_compare_lt
     : ∀ n m : nat, n < m ↔ nat_compare n m = Lt
  nat_compare_gt
     : ∀ n m : nat, n > m ↔ nat_compare n m = Gt
  nat_compare_eq_iff
     : ∀ n m : nat, nat_compare n m = Eq ↔ n = m

  on pourrait aussi  utiliser le théorème de trichotomie des entiers 
  lt_eq_lt_dec: ∀ n m : nat, {n < m} + {n = m} + {m < n}

*)


Fixpoint search (t:NatBinTree) (n:nat) : bool :=
match t with
 | leaf       => false
 | node l e r => match  (Nat.compare n e) with
                  | Lt => search l n
                  | Eq => true
                  | Gt => search r n
                 end
end.

(* on va montrer que search fait la même chose que elts quand l'arbre est de recherche,
   c'est à dire, que la fonction de recherche dichotomique est correcte *)
(* HINT : utiliser case_eq (nat_compare n a) et les théorème de correction de nat_compare
   sur chacun des 3 cas possibles *)
Lemma search_correct_l : forall t n, BST t -> search t n = true -> InT t n.
Proof.
intros t n HBst H.
induction t as [|l IHl a r IHr].
* discriminate  H.
* case_eq (Nat.compare n a); intro Hcmp; simpl in H; rewrite Hcmp in H.
 - apply nat_compare_eq in Hcmp.
   auto using inNodeN.
 - apply nat_compare_lt in Hcmp.
   apply InT_inv.
   left. apply IHl; inversion HBst; assumption.
 - apply nat_compare_gt in Hcmp.
   apply InT_inv.
   right. left. apply IHr; inversion HBst; assumption.
Qed.

(* HINT : ici, on va utiliser le lemme InT_inv qui est le "jumeau" de la comparaison *)
Lemma search_correct_r : forall t n, BST t -> InT t n -> search t n = true.
Proof.
intros t n HBst H.
induction t as [|l IHl a r IHr].
* inversion H.
* apply InT_inv in H.
  destruct H; [|destruct H].
 - (* elts l n *)
   inversion_clear HBst as [|tl tr te HBSTtl HMintl HBSTtr HMintr].
   assert (H' := H). (* on duplique l'hypothèse *)
   apply HMintl in H.
   apply nat_compare_lt in H.
   simpl.
   rewrite H.
   auto.
 - (* elts r n *) 
   inversion_clear HBst as [|tl tr te HBSTtl HMintl HBSTtr HMintr].
   assert (H' := H).
   apply HMintr in H.
   apply nat_compare_gt in H.
   simpl.
   rewrite H.
   auto.
 - (* a = n *)
   apply (Nat.compare_eq_iff) in H.
   simpl.
   rewrite H.
   trivial.
Qed.

Theorem search_correct : forall t n, BST t -> (InT t n <-> search t n = true).
Proof.
split; auto using search_correct_r, search_correct_l.
Qed.


(* On en déduit l'équivalence finalement recherchée *)
(* une autre façon de répondre à la question 6 finalement *)
Corollary search_is_elts : forall t n, BST t -> (elts (eq_nat_dec) t n = true <-> search t n = true).
Proof.
intros t n HBST; split; intros H.
 - apply elts_correct in H.
   apply search_correct; auto.
 - apply elts_correct.
   apply search_correct; auto.
Qed.


End BinarySearchTree.