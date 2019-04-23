Require Import Utf8.

(*****************************************************************************************************)
(******************************      LIFLF : document de travail   ***********************************)
(****************************** EXPRESSIONS REGULIERES DERIVEES EN COQ  ******************************)
(*****************************************************************************************************)

(* Quelques éléments des expression régulières/rationnelles (RegExp) en Coq avec une partie 
   purement sur les langages et la sémantique des RegExp, suivie des dérivées de [Brzozowski].
   L'ensemble est ainsi assez peu calculatoire, plutôt orienté preuves (dans Prop et non dans Set).*)

(* /!\ En l'état, je crois que seul le début est accessible aux étudiants en TP. /!\
   Il y a un peu de manipulation de listes.
   Certains résultats trouveraient tout à fait leur place en TD comme les lemmes 'd'inversion' ou
   la correction de la fonction nu (assez intuitive). *)
   
(* La réalisation est inspirée/reprise de @tchajed dont les preuves sont très automatisé.
   il y a BEAUCOUP TROP de tactiques et de ltac pour que ce soit accessible
   j'y capte pas grand chose à tout dire, c'est aussi pour ça que je refais les preuves...
   https://github.com/tchajed/regex-derivative *)

(* REFERENCES *)
(* Brzozowski, J. A. (1964). Derivatives of Regular Expressions.
   Journal of the ACM, 11(4), 481–494. doi:10.1145/321239.321249
   https://sci-hub.tw/10.1145/321239.321249  *)
(* SCOTT OWENS (a1), JOHN REPPY (a2) and AARON TURON (a3) Regular-expression derivatives re-examined
   https://doi.org/10.1017/S0956796808007090
   https://www.cs.kent.ac.uk/people/staff/sao/documents/jfp09.pdf *)

(* /!\ pour aller voir les preuves des théorèmes de la librairie standard /!\ *)
(* https://github.com/coq/coq/blob/master/theories/ *)

(* Théorèmes sur les fcts usuelles de  listes en Coq *)
(* https://coq.inria.fr/library/Coq.Lists.List.html *)
Require Import List.
(* Pour les notations classiques Haskell [x1, x2] *)
Import ListNotations.

(* on va utiliser List.In : le prédicat d'appartenance à une liste
  List.In : ∀ A : Type, A → list A → Prop := 
  λ A : Type, fix In (a : A) (l : list A) {struct l} : Prop :=
                match l with
                | [] => False
                | b :: m => b = a ∨ In a m
                end
       
*)

(* Définition de base en Coq  : "Definition Ensemble := U -> Prop."
   D'abord le fichier avec toutes les defs *)
(* https://coq.inria.fr/library/Coq.Sets.Ensembles.html *)
Require Import Ensembles.

(* Les théorèmes 'techniques'/'fondamentaux' sur la définition des opérateurs (lemmes d'inversion), 
   valides en logique instuitionniste *)
(* https://coq.inria.fr/library/Coq.Sets.Constructive_sets.html *)
Require Import Constructive_sets.

(* Les théorèmes usuels sur entre opérateurs ou sur l'inclusion, valides en logique instuitionniste *)
(* https://coq.inria.fr/library/Coq.Sets.Powerset_facts.html *)
Require Import  Powerset_facts.

(* on va utiliser les définitions standards Coq de "Ensembles" avec pretty-printing :
   - un peu de bruit administratif dans les preuves à cause de Extensionality_Ensembles par exemple
   - on doit aller chercher les théorèmes dans la lib standard (mais ça évite de les reprouver !) 
   - les énoncés sont ceux de la pratique mathématique usuelle sans abus de notation, comme en TD *)
Notation "x '∈' E"      := (In _ E x) (at level 40).
Notation "'∅'"          := (Empty_set _) (at level 40).
Notation "A '⊆' B"      := (Included _ A B) (at level 40).
Notation "S ∪ T"        := (Union _ S T) (at level 40).
Notation "'{|' x '|}'"  := (Singleton _ x) (at level 40).

(* Pour faire un peu d'arithmétique sur des exemples *)
Require Import Nat PeanoNat.

(* Pour la construction de relations bien-fondées à partir d'autres *)
Require Import Wellfounded.

(*****************************************************************************************************)
(************************** CONCATENATION DE LANGAGES ET ETOILE DE KLEENE  ***************************)
(*****************************************************************************************************)

(* TODO : bon, là, faudrait ptet utiliser les Sections voire les Modules Coq mais c'est un
   peu technique pour moi *)
Section Brzozowski.

(* un alphabet Sigma, i.e. un type dont l'égalité est décidable *)
(* à ce stade, pas besoin d'hypothèse de finitude sur Sigma *)

(* "Sigma" l'alphabet dont l'égalité est décidable *)
Context {Sigma:Set}.
Hypothesis Sigma_eq_dec : forall x y:Sigma, {x = y}+{x <> y}.

(* "String" les listes Coq d'éléments de "Sigma" *)
Definition String := list Sigma.

(* "Language" est en fait un alias pour le type String -> Prop *)
Definition Language := Ensemble String.


(* la décision de l'égalité sur les chaines est héritée de celle de Sigma.
   Nécessaire pour la partie calculatoire plus tard, mais en fait on s'en fout en l'état *)
Lemma String_eq_dec : forall (s s': String), {s = s'} + {s <> s'}.
Proof.
exact (List.list_eq_dec Sigma_eq_dec).
Qed.

(* On a définir les opération sur les languages : Kleene's star et concatenation *)
(* et quelques unes de leurs propriétés *)

(* on commence par la concaténation : "Concat" *)
Inductive Concat (l1: Language) (l2: Language): Language :=
| Concat_pair : forall s1 s2, s1 ∈ l1 ->  s2 ∈ l2 -> (s1 ++ s2) ∈ (Concat l1 l2).

Hint Constructors Concat.

(* petit lemme pour montrer qu'une définition alternative qu'on voit souvent est équivalente *)
Lemma Concat_inv : forall s l1 l2,
  s ∈ (Concat l1 l2) <-> (exists s1 s2, s = s1 ++ s2 /\ s1 ∈ l1 /\ s2 ∈ l2).
Proof.
intros s l1 l2.
split; intros H.
 - (* -> *)
   destruct H.
   exists s1. exists s2.
   auto.
 - (* <- *)
  destruct H as [s1 [s2 [H [Hs1 Hs2]]]].
  subst s.
  constructor; auto.
Qed.

(* On va réviser un peu les ensembles, avec typiquement l'axiome (!)
   Extensionality_Ensembles : ∀ (U : Type) (A B : Ensemble U), Same_set U A B → A = B *)

(* NB : pour les étudiants, rien que chercher cet axiome va être un exercice *)

(* Cinq petits lemmes pour montrer que les langages sont équipés d'une structure de monoide
   < Language, Concat, {| [] |} > avec un élément (∅) absorbant *)
Lemma Concat_absorb_l : forall l, Concat (∅) l = ∅.
Proof.
intros l.
apply Extensionality_Ensembles; split; intros w H; repeat destruct H.
Qed.

Lemma Concat_absorb_r : forall l, Concat l (∅) = ∅.
Proof.
intros l.
apply Extensionality_Ensembles; split; intros w H; destruct H.
destruct H0.
Qed.

(* là on va avoir besoin de théorèmes sur la concatenation de chaines "app" notée "++" 
   comme par exemple app_nil_l : ∀ (A : Type) (l : list A), [] ++ l = l *)
(* on a aussi besoin du plus fondamental Singleton_inv : ∀ (U : Type) (x y : U), y ∈ ({|x|}) → x = y *)
Lemma Concat_neutral_l : forall l, Concat ({| [] |}) l = l.
Proof.
intros l.
apply Extensionality_Ensembles; split; intros w H.
 - destruct H.
   apply Singleton_inv in H.
   subst s1. simpl. trivial.
 - rewrite <- app_nil_l. constructor.
   auto with sets. trivial.
Qed.

Lemma Concat_neutral_r : forall l, Concat l ({| [] |}) = l.
Proof.
intros l.
apply Extensionality_Ensembles; split; intros w H.
 - destruct H.
   apply Singleton_inv  in H0. subst s2. rewrite app_nil_r. trivial.
 - rewrite <- app_nil_r. constructor.
   trivial.
   auto with sets. 
Qed.

Hint Resolve Concat_absorb_l Concat_absorb_r Concat_neutral_l Concat_neutral_r.

(* rien d'autre que app_assoc lifté au final
   app_assoc :∀ (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n *)

Lemma Concat_assoc : forall l1 l2 l3, Concat (Concat l1 l2) l3 = Concat  l1 (Concat l2 l3).
Proof.
intros l1 l2 l3.
apply Extensionality_Ensembles; split; intros w H.
 - destruct H. destruct H.
   rewrite <- app_assoc.
   constructor; auto.
 - destruct H. destruct H0.
   rewrite app_assoc.
   constructor; auto.
Qed.

(* et maintenant l'étoile de Kleene *)
(* là, il doit falloir expliquer un peu le truc ! *)
(* je me demande si la définition avec "s1 ∈ (Kleene_star l)" ne serait pas plus pratique *)

(* PC: fiou! Là tu utilise le fait que Ensemble A est en fait A ->
Prop. La notation ∈ est déroutante ici pour qqun qui a l'habitude des
inductifs. Pour les étudiants ça passera peut-être omme une lettre à
la poste *)

Inductive Kleene_star (l: Language) : Language :=
| Kleene_star_empty : [] ∈ (Kleene_star l)
| Kleene_star_iter : forall s1 s2,
    s1 ∈ l ->
    s2 ∈ (Kleene_star l) ->
    (s1 ++ s2) ∈ (Kleene_star l).

Hint Constructors Kleene_star.

(* On va démontrer quelques classiques (axiomes d'une algèbre de Kleene) *)
(* Plus facile et conceptuellement plus sain de la faire dès ici plutôt que dans les RegExp *)
Lemma Kleene_star_idempotent : forall l, Kleene_star (Kleene_star l) = (Kleene_star l ).
Proof.
intros l.
apply Extensionality_Ensembles; split; intros w H.
 - (* -> *)
   induction H. (* /!\ induction H /!\ *)
   * constructor.
   * induction H.
     simpl; auto.
     rewrite <- app_assoc.
     constructor; auto.
 - (* <- *)
    rewrite <- app_nil_r.
    constructor; auto.
Qed.

Lemma Kleene_star_empty_is_singleton : Kleene_star (∅) = {| [] |}.
Proof.
apply Extensionality_Ensembles; split; intros w H.
 - destruct H.
    * auto with sets.
    * destruct H.
 - destruct H. auto.
Qed.

Hint Resolve Kleene_star_empty_is_singleton.

(* on va montrer un petit lemme d'inversion sur les listes pour l'étoile de Kleene *)
Lemma  Kleene_star_inv_l : forall l w,
  w ∈ (Kleene_star l) -> exists ls, w = (concat ls) /\ (forall x, (List.In x ls) -> (x ∈ l)).
Proof.
intros l w H.
induction H as [| w1 w2 H1 H2 IH].
- (* w = [] *)
  exists [].
  split; auto.
  intros.
  destruct H.
- (* w = w1 ++ w2 *)
  destruct IH as [ls [Hls IH]].
  exists (w1::ls).
  split.
  * simpl.
    subst w2.
    trivial.
  * intros x Hx.
    destruct Hx.
    + subst x. trivial.
    + exact (IH x H).
Qed.

Lemma  Kleene_star_inv_r : forall l w,
  (exists ls, w = (concat ls) /\ (forall x, (List.In x ls) -> (x ∈ l))) -> w ∈ (Kleene_star l).
Proof.
intros l w H.
destruct H as [ls Hls].
generalize dependent w.  (* HINT : piège là : il faut généraliser sur w AVANT induction ! *)
induction ls. 
- (* ls = [] *)
  intros w [Hw H].
  subst w.
  constructor.
- (*ls = (a::ls) *)
  intros w [Hw H].
  simpl in Hw.
  subst w.
  constructor.
  + (* the 'a' part *)
    apply H.
    simpl. left; auto.
  + (* the 'ls' part *)
    apply IHls.
    split; auto.
    intros w Hw.
    apply H.
    simpl.
    right; trivial.
Qed.

(* encapsuler les deux lemmes précédents pour utiliser la tactique rewrite *)
Lemma Kleene_star_inv : forall l w, 
  (exists ls, w = (concat ls) /\ (forall x, (List.In x ls) -> (x ∈ l))) <-> w ∈ (Kleene_star l).
Proof.
split; auto using Kleene_star_inv_r, Kleene_star_inv_l.
Qed.


Lemma Kleene_star_concat_l : forall l w1 w2,
  w1 ∈ (Kleene_star l) -> w2 ∈ (Kleene_star l)  -> (w1 ++ w2) ∈ (Kleene_star l).
Proof.
intros l w1 w2.
(* on casse tout avec le lemme d'inversion *)
repeat (rewrite <- Kleene_star_inv).
intros [ls1 [Hw1 H1]] [ls2 [Hw2 H2]].
(* ça donne une preuve où on voit bien le témoin *)
exists (ls1 ++ ls2).
subst w1.
subst w2.
rewrite concat_app.
split; trivial.
intros w H.
(* in_app_iff : ∀ ..., List.In a (l ++ l') ↔ List.In a l ∨ List.In a l' *)
rewrite -> in_app_iff in H.
destruct H; auto.
Qed.

(* on a très envie de montrer la réciproque de Kleene_star_concat_l :
   ∀ l w1 w2, (w1 ++ w2) ∈ (Kleene_star l) -> (w1 ∈ (Kleene_star l) /\ w2 ∈ (Kleene_star l)).
   mais ce n'est pas possible. Les contres exemples c'est relou en Coq (il faut tout construire)
   dont voici L = (ab)*, 'a'++'b' est bien dans L mais ni 'a' ni 'b' seuls ne sont dans L *)


(*****************************************************************************************************)
(*************************** LES EXPRESSION REGULIRES ET LEUR SEMANTIQUE  ****************************)
(*****************************************************************************************************)

(* le type inductif "Regex" des expression régulières *)
Inductive Regex :=
| Empty
| Char (c:Sigma)
| Or   (r1:Regex) (r2:Regex)
| Seq  (r1:Regex) (r2:Regex)
| Star (r:Regex).

(* on rajoute un peu de sucre syntaxique.
   C'est peut être une fausse bonne idée tout ce sucre, ça va donner des caries aux étudiants *)
Definition ε            := Star Empty.
Notation "'#'"          := Empty.
Notation "'$' c"        := (Char c)(at level 40).
Notation "e1 '@' e2"    := (Seq e1 e2)(at level 15, left associativity).
Notation "e1 ':+:' e2"  := (Or e1 e2)(at level 20, left associativity).
Notation "e '^*'"       := (Star e)(at level 10).

(* Maintenance, on donne la sémantique des expressions régulières comme le langage
   qu'elles reconnaissent. On utilise la notation 'semantic brackets' *)
(* avec tout le sucre, on retrouve à peu de chose près les définitions en notation usuelle *)
Reserved Notation "'[[' e ']]'"  (at level 30).
Fixpoint Denotation (r:Regex) : Language :=
  match r with
  | #           => ∅
  | $ c         => {| [c] |}
  | r1 :+: r2   => [[r1]] ∪ [[r2]]
  | r1 @ r2     => Concat ([[r1]])  ([[r2]])
  | r^*         => Kleene_star ([[r]])
  end
where "'[[' e ']]'"  := (Denotation e).

(* C'est tellement con une fois qu'on a compris, mais ça va mieux en l'écrivant *)
Lemma Eps_is_singleton : [[ ε ]] = {| [] |}.
Proof.
simpl.
rewrite Kleene_star_empty_is_singleton.
reflexivity.
Qed.
Hint Resolve Eps_is_singleton.

(* Exemple gentil  :+: commute *)
Lemma Or_commutes : forall e1 e2, [[e1 :+: e2]]  =  [[e2 :+: e1]].
Proof.
intros e1 e2.
simpl.
rewrite Union_commutative.
trivial.
Restart. (* si on veut faire à la main *)
intros e1 e2.
apply Extensionality_Ensembles; split; intros w H; destruct H; simpl.
 - apply Union_intror; trivial.
 - apply Union_introl; trivial.
 - apply Union_intror; trivial.
 - apply Union_introl; trivial.
Qed.


(* un exemple plus construit : (a|b)* = a*(a|b)* *)
(* https://math.stackexchange.com/questions/1199451/proving-that-two-expressions-are-equivalent *)

Lemma Semantic_example : forall e1 e2, [[(e1 :+: e2)^*]] = [[(e1^*) @ (e1 :+: e2)^*]].
Proof.
intros e1 e2.
apply Extensionality_Ensembles; split; intros w H.
- (* -> : trivial, qui peut le + peut le moins *)
  rewrite <- app_nil_l.
  constructor; auto.  constructor.
- (* <- *)
  destruct H.
  simpl.
  apply Kleene_star_concat_l; auto.
  simpl in H.
  induction H; auto.
  constructor; auto.
  left; auto.
Qed.


(* Exercice intéressant qui consiste à aller chercher les bons théorèmes sur le modulo *)
(*PC: Deux commandes utiles:
 1) Search Foo Bar. qui affiche tous les lemmes sur Foo ET Bar à la fois.
 2) Locate "mod". qui affiche les infos sur les notation contenant "mod".
*)

(* Ici une fois qu'on voit que "mod" en fait c'est modulo, on fait Search modulo plus. 
   et on trouve le lemme intéressant. Exemple de requêtes pour guider *)
(* Search app plus.
   Search modulo plus.
   SearchPattern (_ + 0 = _). *)
Lemma Semantic_example_length : forall a b w, w ∈ [[(($a) @ ($b))^*]] -> modulo  (length w) 2 = 0.
Proof.
intros a b w H.
induction H; auto.
rewrite app_length.
rewrite PeanoNat.Nat.add_mod; auto with arith.
rewrite IHKleene_star.
rewrite PeanoNat.Nat.add_0_r.
rewrite PeanoNat.Nat.mod_mod; auto with arith.
assert (Hs1 : length s1  = 2).
{
  destruct H as [wa wb Ha Hb].
  destruct Ha.
  destruct Hb.
  simpl.
  trivial.
}
rewrite Hs1.
auto.
Qed.

(*****************************************************************************************************)
(***************** Interlude : si une chaîne match une expression, alors tous les  *******************)
(************* éléments de la chaîne apparaissent comme constantes dans l'expression *****************)
(*****************************************************************************************************)

(* d'abord on collecte toutes les constantes, i.e. les feuilles de l'arbre de syntaxe de la regexp,
  dans une string *)
Fixpoint stringize (r : Regex) : String :=
  match r with
  | #         => []
  | $ x       => [x]
  | r1 :+: r2 => stringize r1 ++ stringize r2
  | r1 @ r2   => stringize r1 ++ stringize r2
  | r^*       => stringize r
  end.


Theorem stringize_matches : ∀ (w : String) (r : Regex) (x : Sigma),
  w ∈ [[r]] → List.In x w → List.In x (stringize r).
Proof.
intros w r. generalize dependent w. induction r;  intros w x Hr H;   simpl in Hr;   simpl.
 - (* cas r = # *)
  destruct Hr.
 - (* cas r = $ c*)
  destruct Hr.
  destruct H; auto.
 - (* cas r = r1 :+: r2 *)
  apply in_or_app.
  destruct Hr as [w Hw |  w Hw].
  + left. apply (IHr1 w); trivial.
  + right. apply (IHr2 w); trivial.
 - (* cas r = r1 @ r2 *)
  apply in_or_app.
  destruct Hr as [w1 w2].
  apply in_app_or in H.
  destruct H.
  + left. apply (IHr1 w1); trivial.
  + right. apply (IHr2 w2); trivial.
 - (* cas r = r1^* *)
  induction Hr as [| w1 w2 ].
  + destruct H.
  + apply in_app_or in H.
    destruct H.
    * apply (IHr w1); auto.
    * auto.
Qed.

(*****************************************************************************************************)
(*********************************** Interlude : le lemme d'Arden ************************************)
(*****************************************************************************************************)

(* Arden's rule states that the set A*⋅B is the smallest language that is a solution for X in the linear equation X = A⋅X ∪ B where X, A, B are sets of strings. Moreover, if the set A does not contain the empty word, then this solution is unique. *)

(* https://www7.in.tum.de/um/courses/auto/ws0910/ex/ex01-sol.pdf *)

Lemma Arden_is_solution : ∀ (A B: Regex), [[A^* @ B]] = [[A@(A^* @ B) :+: B]].
Proof.
intros A B.
apply Extensionality_Ensembles; split ; simpl; intros w H.
- (* [[A ^* @ B]] ⊆ [[A @ (A ^* @ B) :+: B]] *)
  destruct H as [w1 w2 H HB].
  induction H as [| w1a w1b HA HAKS IH].
  * now right.
  * rewrite <- app_assoc.
    left.
    constructor; auto.
- (* [[A @ (A ^* @ B) :+: B]] ⊆ [[A ^* @ B]] *) 
  induction H.
   * destruct H as [w1 w2 H1 H2].
     destruct H2 as [w2 w3 H2 H3].
     rewrite app_assoc.
     constructor; auto.
   * rewrite <- app_nil_l.
     constructor; auto.
Qed.


Lemma Arden_is_minimal : ∀ (A B L: Regex), [[L]] = [[(A@L) :+: B]] ->  [[A^* @ B]] ⊆ [[L]] .
Proof.
intros A B L HL w H.
destruct H as [w1 w2 H1 H2].
induction H1 as [| w1 w1' H1 H1' IH].
- simpl.
  rewrite HL.
  now right.
- rewrite <- app_assoc.
  rewrite HL.
  left.
  now constructor.
Qed.

(* https://stackoverflow.com/questions/45872719/how-to-do-induction-on-the-length-of-a-list-in-coq *)
(* 
Require Import Omega.

Section list_length_ind.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. omega.
      - apply IHxs. simpl in Hlen. omega.
    }
    intros xs.
    apply H_ind with (xs := xs).
    omega.
  Qed.
End list_length_ind. *)

(* Et une version bien plus élégante avec well_founded *)

Section list_length_ind.
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis IH : forall xs, (forall l, length l < length xs -> P l) -> P xs.
  Definition length_order (x : list A) (y : list A) := length x < length y.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
  apply well_founded_ind with (R := length_order); auto.
  unfold length_order.
  apply wf_inverse_image.
  exact Nat.lt_wf_0.
  Qed.
End list_length_ind.

About list_length_ind.


(* NB : pas trouvé de façon simple de le faire sans induction sur la longueur *)
Lemma Arden_is_unique : ∀ (A B L: Regex), ~([] ∈ [[A]]) -> [[L]] = [[(A@L) :+: B]] ->  [[L]] ⊆ [[A^* @ B]].
Proof.
intros A B L HA HL w.
induction w as [w IH] using list_length_ind; intros H.
rewrite HL in H.
rewrite Arden_is_solution.
destruct H as [w H | w H].
- (* w ∈ [[A @ L]] *)
  inversion H as [s1 s2 H1 H2 Hw].
  left.
  assert (length s2 < length w).
  {
    rewrite <- Hw.
    rewrite app_length.
    (* SearchHead ((_ < _ + _)). *)
    apply Nat.lt_add_pos_l.
    destruct s1.
     + contradiction.
     + simpl; auto with arith.
  }
  constructor; auto.
- (* w ∈ [[B] *)
  now right.
Qed.

(*****************************************************************************************************)
(***************** LA FCT "nu" QUI TEST SI LE MOT VIDE EST RECONNU PAR UNE REGEXP  *******************)
(*****************************************************************************************************)

(* On commence à rentrer dans Brzozowski avec la fonction qui dit si le mot vide est accepté ou pas *)
(* Là c'est CALCULATOIRE : on reste dans Set *)
Fixpoint nu_b (r:Regex) : bool :=
  match r with
  | #         => false
  | $ _       => false
  | r1 :+: r2 => (nu_b r1) || (nu_b r2)
  | r1 @ r2   => (nu_b r1) && (nu_b r2)
  | r^*       => true
  end.

(* on plonge les booléens dans les regex *)
Definition bool_to_regex (b:bool) : Regex :=
match b with
  | true    => ε
  | false   => #
end.

(* un simple composition *)
Definition nu (r:Regex) : Regex := bool_to_regex (nu_b r).

Lemma nu_is_boolean : forall r, [[nu r]] = ∅ \/ [[nu r]] = {| [] |}.
Proof. (* par cas sur nu_b r *)
unfold nu.
intros r.
case_eq (nu_b r); intros H; simpl; [right | left]; auto.
Qed.

(* là on va utiliser 2 théorèmes qui font le lien entre bool et Prop
     - Bool.orb_true_iff : ∀ b1 b2 : bool, (b1 || b2)%bool = true ↔ b1 = true ∨ b2 = true
     - Bool.andb_true_iff : ∀ b1 b2 : bool, (b1 && b2)%bool = true ↔ b1 = true ∧ b2 = true
*)

Lemma nu_b_checks_if_empty_string_is_recognized_l :
  forall r, nu_b r = true ->  [] ∈ [[r]].
Proof.
induction r; simpl; intros H; try discriminate H. (* on simplifie direct les cas simples false = true *)
 - (* Search orb. *)
   apply Bool.orb_true_iff in H.
   destruct H; [left|right] ; auto.
 - (* Search andb. *)
   apply Bool.andb_true_iff in H.
   destruct H.
   rewrite <- app_nil_l.
   constructor; auto.
 - auto.
Qed.

Lemma nu_b_checks_if_empty_string_is_recognized_r :
  forall r, [] ∈ [[r]] -> nu_b r = true .
Proof.
induction r; simpl; intros H; auto.
- destruct H.
- apply Singleton_inv  in H.
  discriminate.
- destruct H; apply Bool.orb_true_iff.
  left; auto.
  right; auto.
- rewrite <- app_nil_l in H. inversion H as [s1 s2 H1 H2 Hw].
  apply app_eq_nil in Hw; destruct Hw. subst.
  apply Bool.andb_true_iff; split; auto.
Qed.


Theorem nu_checks_correct : forall r, [] ∈ [[r]] <-> [] ∈ [[ nu r ]] .
Proof.
unfold nu.
split; case_eq (nu_b r); simpl; intros Hb H.
 - trivial.
 - apply nu_b_checks_if_empty_string_is_recognized_r in H. 
   rewrite Hb in H. discriminate H.
 - apply nu_b_checks_if_empty_string_is_recognized_l; trivial.
 - destruct H.
Qed.

(* lemme pour enlever une couche de bool_to_regex *)
Lemma nu_b_idem : forall r, nu_b (nu r) = nu_b r.
Proof.
unfold nu.
intros r.
case_eq (nu_b r); simpl; intros Hb; auto.
Qed.

(* On va utiliser les thms généraux du début les suivants sur les ensembles 
     Empty_set_zero : ∀ (U : Type) (X : Ensemble U), (∅) ∪ X = X
     Union_idempotent : ∀ (U : Type) (A : Ensemble U), A ∪ A = A
     Empty_set_zero_right : ∀ (U : Type) (X : Ensemble U), X ∪ (∅) = X
   Et ceux sur Concat (monoide avec zéro)
*)

(* on montre que l'image de || dans bool est :+: dans regex : ∅ est neutre *)
Lemma nu_orb : forall r1 r2, [[nu (r1 :+: r2)]] = [[(nu r1) :+: (nu r2)]].
Proof.
intros r1 r2; unfold nu.
case_eq (nu_b r1); intros Hb1; case_eq (nu_b r2); intros Hb2; simpl.
- rewrite Union_idempotent. rewrite Hb1; rewrite Hb2; auto.
- rewrite Empty_set_zero_right. rewrite Hb1; rewrite Hb2; auto.
- rewrite Empty_set_zero. rewrite Hb1; rewrite Hb2; auto.
- rewrite Empty_set_zero. rewrite Hb1; rewrite Hb2; auto.
Qed.

(* on montre que l'image de && dans bool est @ dans regex : ∅ est absorbant et ε neutre *)
Lemma nu_andb : forall r1 r2, [[nu (r1 @ r2)]] = [[(nu r1) @ (nu r2)]].
Proof.
intros r1 r2; unfold nu.
case_eq (nu_b r1); intros Hb1; case_eq (nu_b r2); intros Hb2; simpl.
 - rewrite Kleene_star_empty_is_singleton.
   rewrite Concat_neutral_r.
   rewrite Hb1; rewrite Hb2; auto.
 - rewrite Concat_absorb_r.
   rewrite Hb1; rewrite Hb2; auto.
 - rewrite Concat_absorb_l.
   rewrite Hb1; rewrite Hb2; auto.
 - rewrite Concat_absorb_l.
   rewrite Hb1; rewrite Hb2; auto.
Qed.



(*****************************************************************************************************)
(******************* DEFINITION DE LA DERIVATION DE REGEXP AU SENS DE BRZOZOWSKI  ********************)
(*****************************************************************************************************)

(* maintenant, on va pouvoir taper dans le dur, avec la dérivation d'expression rationnelles *)
(* d'abord, la définition sémantique *)

Definition Derivative (c:Sigma) (l: Language) : Language :=
    fun w => (c::w) ∈ l.

(* maintenant le calcul. Notons que c'est la première fois qu'on se sert de
   l'égalité décidable sur Sigma. En lisant le cas @, on comprend pourquoi
   on a lifté nu dans Regexp et pas pris une fct booléenne *)

Reserved Notation "c '//' e"  (at level 30).
Fixpoint Derivate (c:Sigma) (e:Regex) : Regex :=
  match e with
  | #           => #
  | $ c'        => if Sigma_eq_dec c c' then ε else Empty
  | r1 :+: r2   => (c // r1) :+:  (c // r2)
  | r1 @ r2     => ((c // r1) @ r2) :+: ((nu r1) @ (c // r2))
  | r^*         => (c // r) @ (r^*)
  end
where "c '//' e "  := (Derivate c e).


Lemma Derivate_is_derivative_l : forall c e, [[c // e]] ⊆ (Derivative c ([[e]])).
Proof.
induction e; intros w H.
- (* cas r = # *)
  destruct H.
- (* cas r = $ c : on va avoir c=c0 et c<> c0 *)
  case_eq (Sigma_eq_dec c c0); intros.
  * subst c.
    simpl. simpl in H. rewrite H0 in H.
    rewrite Eps_is_singleton in H.
    apply Singleton_inv in H.
    subst w.
    unfold Derivative.
    red.
    auto with sets.
  * simpl in H. rewrite H0 in H.
    simpl in H. destruct H.
- (* cas r = r1 :+: r2 *) 
  simpl in H. destruct H; simpl.
  * left. apply IHe1. trivial.
  * right. apply IHe2. trivial.
- (* cas r = r1 @ r2, un peu plus compliqué à cause du test sur (nu e1) *) 
  simpl in H. destruct H; simpl.
  * apply Concat_inv in H.
    destruct H.   destruct H.   destruct H.   destruct H0.
    subst x.
    unfold Derivative.
    red.
    rewrite app_comm_cons .
    constructor.
    apply IHe1. trivial. trivial.
  * unfold Derivative. red.
    destruct H.
    (* et une analyse par cas sur le résultat de nu *)
    destruct (nu_is_boolean e1).
     + rewrite H1 in H.
       destruct H.
     + rewrite H1 in H.
       apply Singleton_inv in H.
       subst s1.
       simpl.
       rewrite <- app_nil_l.
       constructor.
       ++ apply nu_checks_correct. (* /!\ le premier/seul ! endroit où on utilise le lemme /!\ *)
          rewrite H1.
          auto with sets.
       ++ apply IHe2.
          trivial.
- (* cas r = r1^$ *)
  unfold Derivative. red.
  simpl in  H.
  destruct H.
  rewrite app_comm_cons.
  constructor; trivial.
  apply IHe; trivial.
Qed.

(* le cas le + dur pour moi lors de la rédaction.
   L'argument de [Brzozowski] est d'assez haut niveau, faut se taper tous les détails *)
Lemma Derivate_is_derivative_r_star_case : forall c e, (Derivative c ([[e]]) ⊆ [[c // e]]) -> (Derivative c ([[e^*]])) ⊆ [[c // (e^*)]] .
Proof.
unfold Derivative. simpl.
intros c e IH  w H.
red in H.
apply Kleene_star_inv in H.
destruct H as [ls [Hw H] ].
(* la, on doit montrer que la décomposition de (c::w) doit être de la forme ls= [c::w1', w2, ..., wn]
   puis (c::w) = (c::w1') ++ (w2 ++ ... ++ wn) pour pouvoir utiliser le constructeur de concat *)
generalize dependent w.
induction ls as [ | l ls'].
- (* la décompo ne peut pas être vide *)
  intros. inversion Hw.
- (* ls = [l, ls'] *)
  intros.
  rewrite concat_cons in Hw.
  destruct l.
  + (* cas l = [], trivial *)
    apply IHls'; simpl in * |- *; auto.
  + (* on peut enfin exprimer (c::w) de la forme voulue *)
   simpl in Hw.
   injection Hw; intros Hw2 H1. subst s.
   rewrite Hw2.
   (* le désiré cas "c :: w = c :: l ++ concat ls'" *)
   constructor.
   * apply (IH l).
     red.
     apply H.
     simpl. left; auto.
   * apply Kleene_star_inv.
     exists ls'. split; auto.
     intros.
     apply H.
     simpl.
     right.
     trivial.
Qed.

Lemma Derivate_is_derivative_r : forall c e, (Derivative c ([[e]])) ⊆ [[c // e]] .
Proof.
induction e; intros w H;  unfold Derivative in H; red in H.
- (* cas r = # *)
  destruct H.
- (* cas r = $ c : on va avoir c=c0 et c<> c0 *)
  case_eq (Sigma_eq_dec c c0); intros.
   * subst c.
     simpl.
     rewrite H0.
     inversion H.
     rewrite Eps_is_singleton.
     auto with sets.
   * simpl.
     rewrite H0.
     exfalso.
     simpl in H.
     apply Singleton_inv in H.
     injection H. intros.
     auto.
- (* cas r = r1 :+: r2 *) 
  simpl. inversion_clear H.
  * left. apply IHe1. auto.
  * right. apply IHe2. auto.
- (* cas r = r1 @ r2*) 
  inversion H.
  (* analyse par cas sur s1 (l'hypothese d'induction ne servirait à rien) *)
  destruct s1.
   * right. simpl. 
     simpl in H0.
     subst s2.
     rewrite (nu_checks_correct) in H1.
     assert ([[nu e1]] = {| [] |}).
     {
       destruct (nu_is_boolean e1).
       rewrite H0 in H1.
       destruct H1.
       trivial.
     }
     rewrite H0.
     rewrite Concat_neutral_l.
     apply IHe2.
     trivial.
   * rewrite <- app_comm_cons in H0.
     injection H0.
     intros.
     subst s. subst w.
     left.
     simpl.
     constructor.
     apply IHe1.
     trivial.
     trivial.
- (* cas r = r1^* qu'on a prouvé dans un lemme*) 
  apply Derivate_is_derivative_r_star_case; auto.
Qed.

Theorem Derivate_is_correct : forall c e, (Derivative c ([[e]])) = [[c // e]].
Proof.
intros c e.
apply Extensionality_Ensembles; split.
exact (Derivate_is_derivative_r c e).
exact (Derivate_is_derivative_l c e).
Qed.

(*****************************************************************************************************)
(******************* TEST DE RECONNAISSANCE  ********************)
(*****************************************************************************************************)

(* enfin, on peut montrer que ce truc sert à quelque chose : on fold Derivate pour
   savoir si un mot est reconnu ! *)
   
(* par contre, il faut passer ce machin en '100% calculatoire' *)

Fixpoint regex_match (w:String) (r:Regex) :   Regex :=
  match w with
  | []        => (nu r)
  | (x::ls)   => regex_match ls (x // r)
  end.

(* le théorème de correction de regex_match qui 'fold' Derivate_is_correct*)
Theorem regex_match_is_correct  : forall r w, [] ∈ [[(regex_match w r)]] <-> w ∈ [[r]].
Proof.
intros r; split; generalize r; induction w as [|a w' IH].
- (* cas -> pour w = [] *)
  apply nu_checks_correct.
- (* cas -> pour w = a::w' *)
  intros r'.
  replace ((a :: w') ∈ [[r']]) with (w' ∈ (Derivative a ([[r']]) )) by auto.
  rewrite Derivate_is_correct.
  simpl.
  intros H.
  apply IH.
  auto.
- (* cas <- pour w = [] *)
  apply nu_checks_correct.
- (* cas <- pour w = a::w' *)
  intros r'.
  replace ((a :: w') ∈ [[r']]) with (w' ∈ (Derivative a ([[r']]) )) by auto.
  simpl.
  intros H.
  apply IH.
  rewrite <- Derivate_is_correct.
  auto.
Qed.

(* on prouve que le test "[] ∈ [[nu r]]" est décidable. Pour cela, on s'appui sur le plongement
   de bool dans Regex *)
Definition includes_nil_dec r :  {[] ∈ [[nu r]] } + { ~([] ∈ [[nu r]]) }.
induction r.
- (* [] ∈ [[nu #]] *)
  right. simpl; auto with sets.
- (* [] ∈ [[nu ($ c)]] *)
  right. simpl; auto with sets.
- (* [] ∈ [[nu (r1 :+: r2)]] *)
   destruct IHr1 as [IHr1 | IHr1].
   * (* [] ∈ [[nu r1]] *)
     rewrite nu_orb. left. left. auto.
   * (* ¬ [] ∈ [[nu r1]] *) 
     destruct IHr2 as [IHr2 | IHr2].
     + (* [] ∈ [[nu r2]] *)
       rewrite nu_orb. left. right. auto.
     + (* ¬ [] ∈ [[nu r2]] *)
       rewrite nu_orb. right; intros H.
       destruct H; auto.
- (* [] ∈ [[nu (r1 @ r2)]] *)
  destruct IHr1 as [IHr1 | IHr1].
  + (* [] ∈ [[nu r1]] *)
    destruct IHr2 as [IHr2 | IHr2].
    * (* [] ∈ [[nu r2]] *)
      left. rewrite nu_andb.
      rewrite <- app_nil_l.
      constructor; auto.
    * (* ¬ [] ∈ [[nu r2]] *)
      right.  rewrite nu_andb. intros H.
      rewrite <- app_nil_r in H.
      inversion H as  [w1 w2 H1 H2 Hw].
      apply app_eq_nil in Hw. destruct Hw. subst. contradiction.
  + (* ¬ [] ∈ [[nu r1]] *) 
    right. rewrite nu_andb. intros H.
    rewrite <- app_nil_r in H.
    inversion H as [s1 s2 H1 H2 Hx].
    apply IHr1.
    apply app_eq_nil in Hx; destruct Hx as [Hs1 Hs2]; subst s1; auto.
- (* [] ∈ [[nu (r ^* )]] *)
  left.
  simpl. auto.
Defined.

(******** TODO ************)
Definition regex_match_dec w r :  {[] ∈ [[regex_match w r]] } + { ~([] ∈ [[regex_match w r]]) }.
generalize dependent r; induction w as [| c w].
- intros r; exact (includes_nil_dec r).
- intros r. destruct (IHw (c//r)); [left| right]; auto.
Defined.

End Brzozowski.

(*****************************************************************************************************)
(********************* EXTRACTION DE PROGRAMME (PARTIE CALCULATOIRE DANS SET)  ***********************)
(*****************************************************************************************************)

(* https://github.com/coq/coq/wiki/Extraction
   https://coq.inria.fr/refman/addendum/extraction.html *)

Require Import Extraction.

Extraction Language Haskell.

(* on va imposer les types de Haskell pour ceux de Coq, pour éviter que Coq ne regénère tout *)
Extract Inductive sumbool => bool [ true false ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive  Extraction regex_match_dec.

(*****************************************************************************************************)
(***************** ICI DONNER DES EXEMPLES CONCRETS (avec un Sigma fixé)  *******************)
(*****************************************************************************************************)

(* On définit un alphabet concret *)
Inductive ABC: Set := A | B | C.

(* un langage qui ne contient que qu'un seul mot "AB" *)
Definition ab: (@Language ABC):= {| [A ; B] |}.


Definition ABC_eq_dec : forall x y:ABC, {x = y}+{x <> y}.
intros x y.
decide equality.
Defined.


(* PC: Voici le contre-exemple au lemme d'inversion faux réciproque de "Kleene_star_concat_r".
   On a dû attendre la sortie de la section. *)
Lemma contre_exemple: 
  ∃ A (l:@Language A) w1 w2, (w1 ++ w2) ∈ (Kleene_star l) -> ¬(w1 ∈ (Kleene_star l) /\ w2 ∈ (Kleene_star l)).
Proof.
  exists ABC, ab, [A],[B].
  intros H. 
  intro abs.
  destruct abs as [abs1 abs2].
  inversion abs1 as [| s1 s2 h h1 h2 ].
  inversion h.
  subst.
  inversion h2.
Qed.


Require Import Sumbool.

Definition myRegex   := Star (Seq (Char A) (Char B)).
Definition myString1 := [A; B; A; B].
Definition myString2 := [A; B; A; B; C].

Eval vm_compute in (if (regex_match_dec ABC_eq_dec [] myRegex) then true else false).
Eval vm_compute in (if (regex_match_dec ABC_eq_dec  myString1 myRegex) then true else false).
Eval vm_compute in (if (regex_match_dec ABC_eq_dec  myString2 myRegex) then true else false).


(*
(* /!\ lol /!\ *)
Eval vm_compute in (regex_match ABC_eq_dec [] myRegex).
Eval vm_compute in (regex_match ABC_eq_dec myString1 myRegex).
Eval vm_compute in (regex_match ABC_eq_dec myString2 myRegex).

(* /!\ lol^2 /!\ *)
Eval vm_compute in ((regex_match_dec  ABC_eq_dec  [] myRegex)).
Eval vm_compute in (regex_match_dec ABC_eq_dec myString1 myRegex).
Eval vm_compute in (regex_match_dec ABC_eq_dec myString2 myRegex). 
*)



