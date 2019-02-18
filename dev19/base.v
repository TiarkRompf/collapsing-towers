Require Import Arith.
Require Import String.
Require Import List.
Export List ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Require Import Omega.

Inductive op1 :=
| OCar
| OCdr
| OIsNat
| OIsStr
| OIsPair
.

Inductive op2 :=
| OCons
| OEq
| OPlus
| OMinus
| OTimes
.

Inductive exp :=
| EVar (n: nat)
| EApp (e1 e2: exp)
| ELam (e0: exp)
| ELet (e1 e2: exp)
| ELift (e1: exp)
| ERun (e0 e1: exp)
| ENat (n: nat)
| EStr (t: string)
| EIf (e0 e1 e2: exp)
| EOp1 (op: op1) (e1: exp)
| EOp2 (op: op2) (e1 e2: exp)
| EError (msg: string)
.

Inductive val :=
| VClo (env: list val) (e0: exp)
| VCode (e0: exp)
| VNat (n: nat)
| VStr (t: string)
| VPair (va vd: val)
| VError (msg: string)
.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | nil => None
    | cons a l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Definition state := (nat * list exp)%type.

Definition fresh (s: state) :=
  match s with
  | (n, acc) => ((n + 1, acc), EVar(n))
  end.

Definition reflect (s: state) (e: exp) :=
  match s with
  | (n, acc) => fresh (n, e::acc)
  end.

Definition reify (se: state * exp) :=
  match se with
  | (s, e) => fold_right ELet e (snd s)
  end.

Fixpoint anf (s: state) (env: list exp) (e: exp): (state * exp) :=
  match e with
  | ENat n => (s, ENat n)
  | EStr t => (s, EStr t)
  | EVar n => (s, match index n env with
                  | Some v => v
                  | None => EError "unbound var"
                  end)        
  | EApp e1 e2 =>
    match anf s env e1 with
    | (s1, r1) =>
      match anf s1 env e2 with
      | (s2, r2) => reflect s2 (EApp r1 r2)
    end
  end
  | ELam e0 =>
    match fresh s with
    | (s1,v1) =>
      match fresh s1 with
      | (s2, v2) =>
        match anf (fst s2, nil) (v2::v1::env) e0 with
        | (s0, v0) => reflect (fst s, snd s2) (ELam (reify (s0,v0)))
        end
      end
    end
  | ELet e1 e2 =>
    match anf s env e1 with
    | (s1, v1) => anf s1 (v1::env) e2
    end
  | EIf e0 e1 e2 =>
    match anf s env e0 with
    | (s0, v0) =>
      reflect s0 (EIf v0
               (reify (anf (fst s0,nil) env e1))
               (reify (anf (fst s0,nil) env e2)))
    end
  | EOp1 op e1 =>
    match anf s env e1 with
    | (s, v1) => reflect s (EOp1 op v1)
    end
    | EOp2 op e1 e2 =>
    match anf s env e1 with
    | (s, v1) =>
      match anf s env e2 with
      | (s, v2) => reflect s (EOp2 op v1 v2)
      end
    end
  | ELift e1 =>
    match anf s env e1 with
    | (s1, v1) => reflect s1 (ELift v1)
    end
  | ERun e0 e1 =>
    match anf s env e0 with
    | (s0, v0) =>
      match anf s0 env e1 with
      | (s1, v1) => reflect s1 (ERun v0 v1)
      end
    end
  | EError msg => (s, e)
  end.

Definition anf0 (e: exp) := reify (anf (0, nil) nil e).

Eval vm_compute in (anf0 (ELam (EVar 1))).

Definition reifyc (sv: state * val) :=
  match sv with
  | (s, VError msg) => EError msg
  | (s, VCode e) => reify (s,e)
  | (s, _) => EError "expected code"
  end.
Definition reflectc s e :=
  match reflect s e with
  | (s, EError msg) => (s, VError msg)
  | (s, v) => (s, VCode v)
  end.
Definition reifyv (sv: state * val) :=
  match sv with
  | ((_, nil), v) => v
  | (s, VError msg) => VError msg
  | (s, VCode e) =>  VCode(reify (s,e))
  | (s, _) => VError "expected code"
  end.

Fixpoint lift (s: state) (fuel: nat) (v: val): (state * exp) :=
  match fuel with
  | 0 => (s, EError "run out of fuel")
  | S fuel =>
    match v with
    | VNat n => (s, ENat n)
    | VStr t => (s, EStr t)
    | VPair v1 v2 =>
      match (v1, v2) with
      | (VCode e1, VCode e2) => reflect s (EOp2 OCons e1 e2)
      | _ => (s, EError "expected code")
      end
    | VClo env0 e0 =>
      match fresh s with
      | (s1,v1) =>
        match fresh s1 with
        | (s2, v2) =>
          match ev (fst s2, nil) fuel ((VCode v2)::(VCode v1)::env0) e0 with
          | (s0, VCode r0) => reflect (fst s, snd s2) (ELam (reify (s0,r0)))
          | (s0, VError msg) => (s0, EError msg)
          | (s0, _) => (s0, EError "expected code")
          end
        end
      end
    | VCode e0 => reflect s (ELift e0)
    | VError msg => (s, EError msg)
    end
  end
with ev (s: state) (fuel: nat) (env: list val) (e: exp): (state * val) :=
  match fuel with
  | 0 => (s, VError "run out of fuel")
  | S fuel =>
    match e with
    | ENat n => (s, VNat n)
    | EStr t => (s, VStr t)
    | EVar n =>
      match index n env with
      | Some v => (s, v)
      | None => (s, VError "unbound var")
      end
    | EApp e1 e2 =>
      match ev s fuel env e1 with
      | (s0, VError msg) => (s0, VError msg)
      | (s0, VClo env0 e0) =>
        match ev s0 fuel env e2 with
        | (s2, VError msg) => (s2, VError msg)
        | (s2, v2) => ev s2 fuel (v2::(VClo env0 e0)::env0) e0
        end
      | (s0, VCode e1) =>
        match ev s0 fuel env e2 with
        | (s2, VError msg) => (s2, VError msg)
        | (s2, VCode e2) => reflectc s2 (EApp e1 e2)
        | (s2, _) => (s2, VError "expected code")
        end
      | (s0, _) => (s0, VError "app expected function")
      end
    | ELam e0 => (s, VClo env e0)
    | ELet e1 e2 =>
      match ev s fuel env e1 with
      | (s1, VError msg) => (s1, VError msg)
      | (s1, v1) => ev s1 fuel (v1::env) e2
      end
    | EIf e0 e1 e2 =>
      match ev s fuel env e0 with
      | (s0, VNat (S _)) => ev s0 fuel env e1
      | (s0, VNat 0) => ev s0 fuel env e2
      | (s0, VCode v0) =>
        match ((ev (fst s0,nil) fuel env e1),
               (ev (fst s0,nil) fuel env e2)) with
        | ((_, VError msg), _) => (s0, VError msg)
        | (_, (_, VError msg)) => (s0, VError msg)
        | (r1, r2) => reflectc s0 (EIf v0 (reifyc r1) (reifyc r2))
        end
      | (s0, VError msg) => (s0, VError msg)
      | (s0, _) => (s0, VError "expected nat")
      end
    | EOp1 op e1 =>
      match ev s fuel env e1 with
      | (s, v1) =>
        match (op, v1) with
        | (_, VError msg) => (s, VError msg)
        | (_, VCode v1) => reflectc s (EOp1 op v1)
        | (OCar, VPair va vd) => (s, va)
        | (OCdr, VPair va vd) => (s, vd)
        | (OIsNat, VNat _) => (s, VNat 1)
        | (OIsNat, _) => (s, VNat 0)
        | (OIsStr, VStr _) => (s, VNat 1)
        | (OIsStr, _) => (s, VNat 0)
        | (OIsPair, VPair _ _) => (s, VNat 1)
        | (OIsPair, _) => (s, VNat 0)
        | _ => (s, VError "unexpected op")
        end
      end
    | EOp2 op e1 e2 =>
      match ev s fuel env e1 with
      | (s, v1) =>
        match ev s fuel env e2 with
        | (s, v2) =>
          match (op, v1, v2) with
          | (_, VError msg, _) => (s, VError msg)
          | (_, _, VError msg) => (s, VError msg)
          | (_, VCode v1, VCode v2) => reflectc s (EOp2 op v1 v2)
          | (_, VCode v1, _) => (s, VError "stage error")
          | (_, _, VCode v2) => (s, VError "stage error")
          | (OCons, v1, v2) => (s, VPair v1 v2)
          | (OPlus, VNat n1, VNat n2) => (s, VNat (n1 + n2))
          | (OMinus, VNat n1, VNat n2) => (s, VNat (n1 - n2))
          | (OTimes, VNat n1, VNat n2) => (s, VNat (n1 * n2))
          | (OEq, v1, v2) =>
            (s, VNat (
                    match (v1,v2) with
                    | (VNat n1, VNat n2) => if (beq_nat n1 n2) then 1 else 0
                    | (VStr t1, VStr t2) => if (string_dec t1 t2) then 1 else 0
                    | _ => 0
                    end))
          | _ => (s, VError "unexpected op")
          end
        end
      end
    | ELift e1 =>
      match ev s fuel env e1 with
      | (s1, VError msg) => (s1, VError msg)
      | (s1, v1) =>
        match lift s1 fuel v1 with
        | (s2, EError msg) => (s2, VError msg)
        | (s2, v2) => (s2, VCode v2)
        end
      end
    | ERun e0 e1 =>
      match ev s fuel env e0 with
      | (s0, VError msg) => (s0, VError msg)
      | (s0, VCode v0) =>
        match ev (fst s0, nil) fuel env e1 with
        | (s1, v1) => reflectc s0 (ERun v0 (reifyc (s1,v1)))
        end
      | (s0, _) =>
        match reifyc (ev (length env, snd s0) fuel env e1) with
        | code => (s0, reifyv (ev (fst s0, nil) fuel env code))
        end
      end
    | EError msg => (s, VError msg)
    end
  end.

Definition ev0 e := ev (0, nil) 100 nil e.

Eval vm_compute in ev0 (ELam (EVar 1)).
Eval vm_compute in ev0 (anf0 (ELam (EVar 1))).
Eval vm_compute in ev0 (ELam (ELam (EVar 1))).
Eval vm_compute in ev0 (anf0 (ELam (ELam (EVar 1)))).
Eval vm_compute in reifyc (ev0 (ELift (ELam (EVar 1)))).
Eval vm_compute in (anf0 (ELam (EVar 1))).
Eval vm_compute in reifyc (ev0 (ELift (ELam (ELift (ELam (EVar 1)))))).
Eval vm_compute in (anf0 (ELam (ELam (EVar 1)))).
Eval vm_compute in (ev0 (ERun (ELam (EVar 1)) (ELift (ELam (EVar 1))))).
Eval vm_compute in reifyc (ev0 (ELift (ELam (EApp (EVar 0) (EVar 1))))).

Fixpoint to_lifted (e: exp): exp :=
  match e with
  | EVar n => e
  | EApp e1 e2 => EApp (to_lifted e1) (to_lifted e2)
  | ELam e0 => ELift (ELam (to_lifted e0))
  | ELet e1 e2 => ELet (to_lifted e1) (to_lifted e2)
  | ELift e1 => EError "liftlam: lift not allowed"
  | ERun e0 e1 => EError "liftlam: run not allowed"
  | ENat n => ELift e
  | EStr t => ELift e
  | EIf e0 e1 e2 => EIf (to_lifted e0) (to_lifted e1) (to_lifted e2)
  | EOp1 op e1 => EOp1 op (to_lifted e1)
  | EOp2 op e1 e2 => EOp2 op (to_lifted e1) (to_lifted e2)
  | EError msg => e
  end.

Eval vm_compute in (anf0 (ELam (ELam (EApp (EVar 3) (EVar 1))))).
(* ELet (ELam (ELet (ELam (ELet (EApp (EVar 3) (EVar 1)) (EVar 4))) (EVar 2))) (EVar 0) *)
Eval vm_compute in (reifyc (ev0 (to_lifted (ELam (ELam (EApp (EVar 3) (EVar 1))))))).

Lemma env_inv1_extend: forall env1 e1,
  (forall n v1, index n env1 = Some v1 -> exists e, v1 = VCode e) ->
  (forall n v1, index n ((VCode e1)::env1) = Some v1 -> exists e, v1 = VCode e).
Proof.
  intros.
  simpl in H0.
  case_eq (n =? Datatypes.length env1); intros E.
  rewrite E in H0. inversion H0. eexists. reflexivity.
  rewrite E in H0. eapply H. eapply H0.
Qed.

Lemma env_inv2_extend: forall env1 env2 e1,
    (length env1 = length env2) ->
    (forall n e, index n env1 = Some (VCode e) -> index n env2 = Some e) ->
    (forall n e, index n ((VCode e1)::env1) = Some (VCode e) -> index n (e1::env2) = Some e).
Proof.
  intros.
  simpl in H1.
  case_eq (n =? Datatypes.length env1); intros E.
  rewrite E in H1. inversion H1. subst.
  simpl. rewrite <- H. rewrite E. reflexivity.
  simpl. rewrite <- H. rewrite E.
  rewrite E in H1. apply H0. apply H1.
Qed.

Theorem anf_like_lift: forall n, forall fuel, fuel < n -> forall e s env1 env2,
    (length env1 = length env2) ->
    (forall n v1, index n env1 = Some v1 -> exists e, v1 = VCode e) ->
    (forall n e, index n env1 = Some (VCode e) -> index n env2 = Some e) ->
    (exists s' msg, (ev s fuel env1 (to_lifted e)) = (s', VError msg)) \/
    (exists s' e', (ev s fuel env1 (to_lifted e)) = (s', VCode e') /\ (anf s env2 e) = (s', e')).
Proof.
  intros nMax. induction nMax; intros fuel Hfuel.
  inversion Hfuel.
  intros.
  destruct fuel.
  simpl. left. repeat eexists.
  destruct e.
  - simpl.
    case_eq (index n env1).
    intros v1 Hv.
    specialize (H0 n v1 Hv). destruct H0 as [x1 Hx1].
    rewrite Hx1 in Hv.
    specialize (H1 n x1 Hv). subst. right.
    eexists. eexists. split. reflexivity. rewrite H1. reflexivity.
    intros Hv. left. repeat eexists.
  - simpl.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega. instantiate (1:=e1) in H2. destruct H2 as [s1 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s1 [n1 [Hev1 Ha1]]].
    rewrite Hev1.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega. instantiate (1:=e2) in H2. destruct H2 as [s2 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s2 [n2 [Hev2 Ha2]]].
    rewrite Hev2. right. rewrite Ha1. rewrite Ha2.
    unfold reflectc. unfold reflect. simpl.
    destruct s2 as [n2' acc2].
    eexists. eexists. split. reflexivity. reflexivity.
  - simpl. destruct fuel as [| fuel].
    simpl. left. repeat eexists.
    simpl. destruct s as [ns accs]. simpl.
    edestruct IHnMax with (env1:=(VCode (EVar (ns + 1)) :: VCode (EVar ns) :: env1)) (env2:=(EVar (ns + 1))::(EVar ns)::env2); eauto.
    instantiate (1:=fuel). omega.
    simpl. omega.
    apply env_inv1_extend. apply env_inv1_extend. auto.
    apply env_inv2_extend. simpl. omega. apply env_inv2_extend. simpl. omega. auto.
    instantiate (1:=e) in H2. destruct H2 as [s1 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s' [n' [Hev Ha]]].
    rewrite Hev. rewrite Ha. right. repeat eexists.
  - simpl.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega.
    instantiate (1:=e1) in H2. destruct H2 as [s' [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [s' [n' [Hev1 Ha1]]].
    rewrite Hev1. rewrite Ha1.
    edestruct IHnMax with (env1:=(VCode n' :: env1)) (env2:=(n' :: env2)).
    instantiate (1:=fuel). omega.
    simpl. omega.
    apply env_inv1_extend. auto.
    apply env_inv2_extend. simpl. omega. auto.
    destruct H2 as [? [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [? [? [Hev2 Ha2]]].
    rewrite Hev2. rewrite Ha2. right. repeat eexists.
  - simpl. left. repeat eexists.
  - simpl. left. repeat eexists.
  - simpl.
    destruct fuel as [|fuel].
    simpl. left. repeat eexists.
    simpl. right. exists s. exists (ENat n). split. reflexivity. reflexivity.
  - simpl.
    destruct fuel as [|fuel].
    simpl. left. repeat eexists.
    simpl. right. exists s. exists (EStr t). split. reflexivity. reflexivity.
  - simpl.
    edestruct IHnMax; eauto. instantiate (1:=fuel). omega. instantiate (1:=e1) in H2. destruct H2 as [s1 [msg Herr]].
    rewrite Herr. left. repeat eexists.
    destruct H2 as [? [? [Hev Ha]]].
    rewrite Hev. rewrite Ha.
    unfold reflectc. unfold reflect. destruct x. simpl.
    edestruct IHnMax with (fuel:=fuel) (e:=e2) (s:=(n,[]):state); eauto.
    omega. destruct H2 as [? [msg Herr]]. rewrite Herr.
    left. repeat eexists.
    destruct H2 as [? [? [Hev1 Ha1]]].
    rewrite Hev1. rewrite Ha1.
    edestruct IHnMax with (fuel:=fuel) (e:=e3) (s:=(n,[]):state); eauto.
    omega. destruct H2 as [? [msg Herr]]. rewrite Herr.
    left. repeat eexists.
    destruct H2 as [? [? [Hev2 Ha2]]].
    rewrite Hev2. rewrite Ha2.
    right. simpl. repeat eexists.
  - simpl.
    edestruct IHnMax with (fuel:=fuel) (e:=e); eauto. omega.
    destruct H2 as [? [msg Herr]]. rewrite Herr.
    destruct op; left; repeat eexists; reflexivity.
    destruct H2 as [s' [e' [Hev Ha]]].
    rewrite Hev. rewrite Ha.
    unfold reflectc. unfold reflect. destruct s'. simpl.
    destruct op; right; repeat eexists.
  - simpl. admit.
  - simpl. left. repeat eexists.
Admitted.

Theorem anf_like_lift0: forall e,
    (exists msg, reifyc (ev0 (to_lifted e)) = EError msg) \/ reifyc (ev0 (to_lifted e)) = anf0 e.
Proof.
  intros. unfold ev0. unfold anf0.
  destruct anf_like_lift with (n:=101) (fuel:=100) (s:=(0,nil):state) (env1:=nil:list val) (env2:=nil:list exp) (e:=e); auto.
  - intros. simpl in H. inversion H.
  - intros. simpl in H. inversion H.
  - destruct H as [s' [msg Herr]].
    rewrite Herr. simpl. left. exists msg. reflexivity.
  - destruct H as [s' [n' [Hev Ha]]].
    rewrite Hev. rewrite Ha. simpl. right. reflexivity.
Qed.