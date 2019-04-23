Require Import Utf8.
Require Import List.
Require Import Arith.
Require Import Relations.
Require Import Wellfounded.

Import ListNotations.

Section TD2_wf.


(*****************************************************************************************************)
(********* LIFLC : TD2 Induction, exercice sur les ordre avec la bonne fondation de suffixe **********)
(*****************************************************************************************************)

(**********************************************************************************************)
(* 3 définitions équivalente de la relation suffixe et les preuves qu'elles sont bien fondées *)
(**********************************************************************************************)


(* lemmes techniques sur les listes *)

Lemma list_cons_app_neq (A:Set) : forall (l l':list A), l' <> [] -> l' ++ l <> l.
Proof.
unfold not.
intros.
assert (l' ++ l = [] ++ l).
auto.
apply app_inv_tail in H1.
auto.
Qed.

Lemma cons_neq : forall (A:Set) (x:A) xs, xs <> x::xs.
Proof.
induction xs as [|x' xs IHxs]; intro H. 
- apply (nil_cons H).
- injection H; intros.
  rewrite H1 in H0.
  apply (IHxs H0).
Qed.




(*************************************************************************************)
(* Definition inductive et généralités sur suffixe (ou égal)                         *)
(*************************************************************************************)

(* La relation inductive "xs est un suffixe de ys" *)
Inductive suffix (A:Set) : list A -> list A -> Prop :=
 | suffix_nil : forall (l:list A), suffix A l l
 | suffix_cons : forall (s l:list A) (a:A), suffix A s l-> suffix A s (a::l).

Hint Constructors suffix : suffix.

(* exemples *)
Section exemples_suffix.
Variable A : Set.
Variable a b c : A.

Goal suffix A [] [].
auto with suffix.
Qed.

Goal suffix A [] [a; b].
auto with suffix.
Qed.

Goal suffix A [b; c] [a; b; c].
auto with suffix.
Qed.
End exemples_suffix.

(* lemme : [] n'a que lui même comme suffixe *)
Lemma suffix_nil_implies_nil : forall (A: Set) (xs : list A), suffix A xs [] -> xs = [].
Proof.
induction xs.
auto with suffix.
intros H; inversion H.
Qed.

(* lemme : [] est un suffixe de toute les listes*)
Lemma suffix_app_nil : forall (A: Set) (xs: list A), suffix A [] xs .
Proof.
intros. induction xs; auto with suffix.
Qed.

Lemma suffix_strict_or_same : forall (A:Set) (xs:list A) (ys:list A) (y:A),
   suffix A xs (y::ys) -> (suffix A xs ys \/ xs = y::ys).
Proof.
intros; inversion_clear H; auto.
Qed.

Lemma suffix_reflex : forall (A:Set) (xs:list A), suffix A xs xs.
Proof.
induction xs; auto with suffix.
Qed.

Lemma suffix_anti : forall (A:Set) (xs ys:list A) (x y:A),
   suffix A (x::xs) (y::ys) -> (suffix A xs ys).
Proof with auto with suffix.
induction ys.
 + intros.
   destruct (suffix_strict_or_same _ _ _ y H).
   destruct (suffix_nil_implies_nil _ (x::xs) H0)...
   injection H0; intros; subst xs...
 + intros. inversion_clear H...
   constructor.
   apply (IHys x a)...
Qed.

Hint Resolve suffix_nil_implies_nil suffix_app_nil suffix_strict_or_same suffix_reflex suffix_anti : suffix.


(*************************************************************************************)
(* Equivalence entre la def inductive de suffix et ∃ws, ys = ws ++ xs                *)
(*************************************************************************************)

Definition suffix_app (A: Set) (xs ys: list A) := exists ws, ys = ws ++ xs.
Hint Unfold suffix_app : suffix.

Lemma suffix_app_l : forall (A: Set) (xs ys: list A),
  suffix A xs ys ->  suffix_app A xs ys.
Proof.
intros X xs ys; induction ys as [|y ys IHys];
intros H; inversion_clear H as [| ? ? ? Hxsys ];
[exists []| exists []| ]; trivial.
 apply IHys in Hxsys as [zs Hzs].
 exists (y::zs).
 rewrite Hzs.
 trivial.
Qed.

Lemma suffix_app_r : forall (A: Set) (ws ys: list A), suffix A ys (ws ++ ys) .
Proof.
intros.
induction ws; simpl; auto with suffix.
Qed.

(* le théorème qui regroupe les 2 sens *)
Theorem suffix_app_equiv_suffix : forall (A: Set) (xs ys: list A), suffix A xs ys <->  suffix_app A xs ys.
Proof.
intros A xs ys.
split.
 - apply suffix_app_l.
 - intros [ws H].
   rewrite H. 
   apply suffix_app_r.
Qed.

Hint Resolve suffix_app_l suffix_app_r : suffix.



(*************************************************************************************)
(* La relation "être un suffixe de" est un ordre partiel                             *)
(*************************************************************************************)

(* on va raisonner en utilisant l'équivalence avec suffix_app pour pouvoir utiliser
   les théorèmes de la concatenation dans la lib standard
    app_assoc
         : ∀ (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n
    app_inv_tail
         : ∀ (A : Type) (l l1 l2 : list A), l1 ++ l = l2 ++ l → l1 = l2
    app_eq_nil
         : ∀ (A : Type) (l l' : list A), l ++ l' = [] → l = [] ∧ l' = []
*)

Theorem suffix_antisymmetric : forall (A:Set), antisymmetric (list A) (suffix A).
Proof.
unfold antisymmetric.
intros A xs ys Hxy Hyx.
(* on réécrit avec la definition de suffix_app *)
apply (suffix_app_l A) in Hxy; destruct Hxy as [ws Hxy].
apply (suffix_app_l A) in Hyx; destruct Hyx as [ws' Hyx].
(* si  ys = ws ++ xs et xs = ws' ++ ys, on va montrer que ws = ws' = [] *)
rewrite Hxy in Hyx.
rewrite <- (app_nil_l xs) in Hyx at 1.
rewrite app_assoc in Hyx.
apply app_inv_tail in Hyx.
symmetry in Hyx.
apply app_eq_nil in Hyx.
destruct Hyx as  [H0 H1].
rewrite H1 in Hxy.
auto.
Qed.

Theorem suffix_refl : forall (A:Set), reflexive (list A) (suffix A).
Proof.
intros A xs.
apply suffix_nil.
Qed.

Theorem suffix_trans : forall (A:Set), transitive (list A) (suffix A).
Proof.
unfold transitive.
intros A xs ys zs Hxy Hyz.
apply (suffix_app_l A) in Hxy; destruct Hxy as [ws Hxy].
apply (suffix_app_l A) in Hyz; destruct Hyz as [ws' Hyz].
(* l'associativité de la concatenation va permettre de conclure *)
rewrite Hxy in Hyz.
rewrite app_assoc in Hyz.
rewrite Hyz.
apply suffix_app_r.
Qed.

(*************************************************************************************)
(* Définition de la relation suffixe STRICT                                          *)
(*************************************************************************************)

(* on définit la relation "xs un suffixe STRICT de ys" *)
(* /!\ on devrait pouvoir faire des trucs avec order en coq > 8.4 /!\ *)
Definition suffix_strict (A:Set) (xs:list A) (ys:list A) := suffix A xs ys /\ xs <> ys.

(* equivalence avec ∃ws, ws <> [] /\ ys = ws ++ xs *)
Theorem suffix_strict_equiv_app (A:Set) (xs ys:list A) : (exists ws, ws <> [] /\  ys = ws ++ xs) <-> suffix_strict A xs ys .
Proof.
split.
- intros.
  destruct H as [ws [wsneq H]].
  rewrite H.
  split.
   * exact (suffix_app_r A ws xs).
   * intros H'.
     destruct (list_cons_app_neq A xs ws wsneq).
     auto.
- intros.
  destruct H.
  destruct (suffix_app_l A xs ys H) as [ws Hws].
  exists ws.
  split.
  * intro Hneq.
    rewrite Hneq in Hws.
    simpl in Hws.
    symmetry in Hws.
    contradiction.
  * exact Hws.
Qed.


(* on déduit la transitivité de celle de suffix et de son anti symmétrie *)
Theorem suffix_strict_trans :  forall (A:Set), transitive (list A) (suffix_strict A).
Proof.
unfold transitive.
intros A xs ys zs [Hxy Hxyneq] [Hyz Hyzneq].
unfold suffix_strict in *.
split.
- exact (suffix_trans A xs ys zs Hxy Hyz).
- unfold not. intros.
  rewrite <- H in Hyz.
  assert (xs = ys). 
  apply suffix_antisymmetric; assumption.
  contradiction.
Qed.

(*************************************************************************************)
(* Bonne fondation de suffixe STRICT                                                 *)
(*************************************************************************************)

(* le lemme principale de la preuve de bonne fondation *)
Lemma suffix_strict_wf_main_lemma: forall (A:Set) (ns xs:list A), suffix_strict A xs ns -> Acc (suffix_strict A) xs.
Proof.
induction ns.
  - intros. destruct H. 
    apply suffix_nil_implies_nil in H.
    contradiction.
  - intros ys Hys. constructor. intros zs Hzs.
    apply IHns.
    destruct Hys.
    destruct Hzs.
    split.
    apply suffix_trans with (ys); auto.
    inversion H.
    rewrite H4 in H0. exfalso. apply H0; auto. assumption.
    unfold not. intros.
    destruct (suffix_strict_or_same A ys ns a) ; auto.
    rewrite <- H3 in H4.
    apply H2.
    apply (suffix_antisymmetric A zs ys H1 H4).
Defined.


(* le thm principal qui dérive assez directement du lemme *)
(* la technique de preuve est au final assez similaire à celle de wf pour lt *)
Theorem suffix_strict_wf (A:Set): well_founded (suffix_strict A).
Proof.
unfold well_founded.
intro xs. induction xs as [|x xs].
- apply Acc_intro. intros.
  destruct H.
  apply suffix_nil_implies_nil in H.
  contradiction. 
- intros.  apply (suffix_strict_wf_main_lemma A (x::x::xs)).
  split ; auto with suffix.  intro. injection H. intros. 
  apply (cons_neq A x xs). trivial.
Defined.



(**************************************************************************************)
(* AUTRE PREUVE de la bonne fondation de suffixe STRICT par induction sur la longueur *)
(**************************************************************************************)

(* on montre que les suffixes de xs sont plus courts que xs*)
Lemma suffix_is_le :  forall (A:Set) (xs ys:list A), suffix A xs ys -> length xs <= length ys.
Proof.
induction ys as [|y ys IHys]; intros H.
- apply suffix_nil_implies_nil in H. rewrite H. auto.
- inversion_clear H as [| ? ? ? Hxs ]; auto.
  simpl.
  apply le_trans with (length ys); auto.
Qed.

(* et similairement pour suffixe strict *)
Lemma suffix_strict_is_lt :  forall (A:Set) (xs ys:list A), suffix_strict A xs ys -> length xs < length ys.
Proof.
unfold suffix_strict in *.
induction ys as [|y ys IHys]; intros [H Hneq].
- apply suffix_nil_implies_nil in H. contradiction.
- apply suffix_strict_or_same in H.
  destruct H; try   contradiction.
  apply le_lt_trans with (length ys).
  auto using suffix_is_le.
  simpl.
  auto with arith.
Qed.

(* on montre que la relation "être + court" est bien fondée car < l'est *)
Definition shorter (A:Set) (xs ys:list A) : Prop :=  length xs < length ys. 

Lemma shorter_is_well_founded : forall (A:Set), well_founded (shorter A).
Proof.
intros A.
apply (wf_inverse_image (list A) (nat) (lt) (@length A) ).
exact (lt_wf).
Restart.
(* ou + directement encore *)
intros A.
exact (well_founded_ltof (list A) (@length A)).
Defined.

(* maintenant, on peut utiliser le principe d'induction sur la longueur des listes 
   well_founded_ind
     : ∀ (A : Type) (R : A → A → Prop), well_founded R → ∀ P : A → Prop,
         (∀ x : A, (∀ y : A, R y x → P y) → P x) → ∀ a : A, P a
*)

Theorem suffix_strict_wf_2 (A:Set): well_founded (suffix_strict A).
Proof.
intros xs.
induction xs using (@well_founded_ind (list A) (shorter A) (shorter_is_well_founded A)).
apply Acc_intro.
intros ys Hys.
apply H.
exact (suffix_strict_is_lt A ys xs Hys).
Defined.


(**************************************************************************************)
(* 3ème définition de suffixe basée sur la fermeture transitive de cons               *)
(**************************************************************************************)

Definition suffix_immediate (A:Set) : list A -> list A -> Prop :=
 fun xs ys : list A => exists x:A, x ::xs = ys.

(* la fermetutre transitive de suffix_immediate, qui n'est autre que l'itération de cons *)
Definition suffix_clos_trans (A:Set) : list A -> list A -> Prop := 
  clos_trans _ (suffix_immediate A).

(* on montre que cette nouvelle définition est équivalente aux 2 autres *)

(* ce sens est facile *)
Lemma suffix_clos_trans_equiv_strict_l (A:Set) : inclusion (list A) (suffix_clos_trans A)  (suffix_strict A).
Proof.
unfold inclusion.
intros xs ys.
unfold suffix_clos_trans.
unfold suffix_immediate.
unfold suffix_strict.
(* par induction sur clos_trans *)
induction 1.
- destruct H.
  rewrite <- H.
  split; auto using cons_neq with suffix.
- split; destruct IHclos_trans1; destruct IHclos_trans2.
  apply suffix_trans with y; auto.
  intro Hxz.
  rewrite  Hxz in H1.
  apply H4.
  apply (suffix_antisymmetric A y z H3 H1).
Qed. 


Lemma suffix_clos_trans_equiv_strict_r (A:Set) : inclusion (list A) (suffix_strict A)  (suffix_clos_trans A)  .
Proof.
unfold inclusion.
intros xs ys.
rewrite <- suffix_strict_equiv_app.
induction ys as [| y ys IHys].
(* case ys = [] : impossible *)
- intros [ws [Nws H]].
  symmetry in H.
  apply app_eq_nil in H.
  destruct H; contradiction.
(* case ys = y::ys' *)
- intros [ws [Nws H]].
  (* on a y :: ys = ws ++ xs et ws <> []*)
  case_eq ws; intros; try contradiction.
    (* donc ws = a::l et y :: ys = y :: (l ++ xs) *)
    (* on a besoin que xs soit un prefixe strict de ys pour l'induction *)
    (* HINT : on va regarder les deux cas possibles pour l *)
    case_eq l.
     (* l = [], donc xs = ys et c'est facile par t_step *)
     + intros.
       rewrite H1 in H0.
       rewrite H0 in H.
       injection H; intros.
       rewrite H2.
       apply t_step; exists y; trivial.
     (* l = a0::l0, donc ys = a0 :: l0 ++ xs *)
     + intros.
       rewrite H0 in H.
       injection H; intros.
       (* on montre xs << ys par induction et ys << y::ys par définition de suffix_immediate *)
       apply t_trans with (ys).
       * apply IHys.
         exists l.
         split; try assumption.
         rewrite H1.
         discriminate.
       * apply t_step; exists y; trivial.
Qed.


(**************************************************************************************)
(* 3ème preuve de well founded                                                        *)
(**************************************************************************************)

(* la relation entre (xs) et (x::xs) est bien fondée : facile car il n'y a au plus qu'un seul successeur *)
Lemma suffix_immediate_wf (A:Set) : well_founded (suffix_immediate A).
Proof.
unfold well_founded.
intros xs.
induction xs; apply Acc_intro; intros ys H; unfold suffix_immediate in H; destruct H as [y Hys].
- discriminate Hys.
- injection Hys; intros.
  rewrite H. assumption.
Defined.


(* la fermeture transitive d'une relation bien fondée est bien fondée *)
Lemma suffix_clos_trans_wf (A:Set): well_founded (suffix_clos_trans A).
Proof.
exact (wf_clos_trans _ (suffix_immediate A) (suffix_immediate_wf  A)).
Defined.

(* on utilise le fait que tout sous ensemble d'une relation bien fondée l'est aussi *)
Theorem suffix_strict_wf_3 (A:Set): well_founded (suffix_strict A).
Proof.
apply (wf_incl (list A) _ (suffix_clos_trans A)).
exact (suffix_clos_trans_equiv_strict_r A).
exact (suffix_clos_trans_wf A).
Defined.




