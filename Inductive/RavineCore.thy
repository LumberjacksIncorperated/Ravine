theory RavineCore imports Main begin

(*datatype 'a list = Nil | Cons 'a "'a list")*)
datatype 'a optional = None | Some 'a

fun list_length :: "'a list \<Rightarrow> nat" where
"list_length Nil = 0" |
"list_length (Cons n N) = Suc (list_length N)"

fun list_append :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"list_append Nil a = Cons a Nil" |
"list_append (Cons n N) a = Cons n (list_append N a)"

fun list_update :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" where
"list_update Nil _ _ = Nil" |
"list_update (Cons m M) v 0 = (Cons v M)" |
"list_update (Cons m M) v (Suc n) = (Cons m (list_update M v n))"


type_synonym security = nat
type_synonym var_name = nat
datatype type = Type security
type_synonym type_sources = "type list"
datatype mapping = Map type type_sources
datatype state = State "mapping list"

fun add_mapping' :: "mapping list \<Rightarrow> mapping \<Rightarrow> mapping list" where
"add_mapping' Nil m = Cons m Nil" |
"add_mapping' (Cons n N) m = Cons n (add_mapping' N m)" 

fun add_mapping :: "state \<Rightarrow> mapping \<Rightarrow> state" where
"add_mapping (State sl) m = State (add_mapping' sl m)"

(*
fun get_last_var_name' :: "mapping \<Rightarrow> mapping list \<Rightarrow> var_name" where
"get_last_var_name' m Nil = 0" |
"get_last_var_name' m (Cons n N) = Suc (get_last_var_name' n N)"

fun get_last_var_name :: "state \<Rightarrow> var_name optional" where
"get_last_var_name (State Nil) = None" |
"get_last_var_name (State (Cons n N)) = Some (get_last_var_name' n N)"
*)

fun update_mapping :: "state \<Rightarrow> mapping \<Rightarrow> var_name \<Rightarrow> state" where
"update_mapping (State l) m name = State (list_update l m name)"

inductive 
  is_last_var_name :: "state \<Rightarrow> var_name \<Rightarrow> bool"
where
is_last_var_name_0: "is_last_var_name (State (Cons n Nil)) 0" |
is_last_var_name_S: "is_last_var_name (State N) x \<Longrightarrow> is_last_var_name (State (Cons n N)) (Suc x)"

lemma is_last_var_name_inversion1:
  "is_last_var_name (State (Cons n N)) (Suc x) \<Longrightarrow> is_last_var_name (State N) x"
  using is_last_var_name.cases by blast


inductive 
  is_mapped :: "mapping \<Rightarrow> state \<Rightarrow> var_name \<Rightarrow> bool"
where
is_mapped_0: "is_mapped m (State (Cons m M)) 0" |
is_mapped_S: "is_mapped m (State M) n \<Longrightarrow> is_mapped m (State (Cons w M)) (Suc n)"


(*meta lemmas*)

lemma is_last_var_name_lemma_1:
  "is_last_var_name (State Nil) x \<Longrightarrow> False" using is_last_var_name.cases by blast

lemma is_last_var_name_lemma_2:
  "is_last_var_name (State (Cons n Nil)) 0"
apply (rule RavineCore.is_last_var_name.intros(1))
done

lemma is_last_var_name_lemma_3:
  "is_last_var_name (State (Cons n Nil)) x \<Longrightarrow> x = 0"
apply (induction x)
apply simp
apply (frule is_last_var_name_inversion1)
apply (frule is_last_var_name_lemma_1)
apply simp
done

lemma is_last_var_name_lemma_4:
  "is_last_var_name (State N) x \<Longrightarrow> is_last_var_name (State (Cons n N)) (Suc x)"
apply (rule RavineCore.is_last_var_name.is_last_var_name_S)
apply assumption
done

(*\<And>*)

lemma is_mapped_lemma_1'':
  "\<forall> s1. add_mapping s1 m = State xa \<Longrightarrow> Ex (is_mapped m (State xa))"
apply (induction xa)
apply auto
apply (rule_tac x="0" in exI)
apply auto[1]
apply (simp add: is_mapped_0)

sorry


lemma is_mapped_lemma_1':
  "add_mapping (State xa) m = s2 \<Longrightarrow> Ex (is_mapped m s2)"
apply (induction xa arbitrary: s2)
try

sorry

lemma is_mapped_lemma_1:
  "add_mapping s1 m = s2 \<Longrightarrow> \<exists>x. is_mapped m s2 x"
apply (induction s1)
apply (rule is_mapped_lemma_1')
apply auto
done


lemma is_mapped_lemma_2'':
  "\<lbrakk>add_mapping s1 m = s2; is_last_var_name s2 x; is_mapped m s2 xa\<rbrakk> \<Longrightarrow> xa = x"
sorry

lemma is_mapped_lemma_2':
  "\<lbrakk>add_mapping s1 m = s2; is_last_var_name s2 x; is_mapped m s2 xa\<rbrakk> \<Longrightarrow> is_mapped m s2 x"
apply (frule is_mapped_lemma_2'')
apply auto
done

lemma is_mapped_lemma_2:
  "\<lbrakk>add_mapping s1 m = s2; is_last_var_name s2 x\<rbrakk> \<Longrightarrow> is_mapped m s2 x"
apply (frule is_mapped_lemma_1)
apply (erule exE)
apply (rule is_mapped_lemma_2')
apply auto
done


lemma add_mapping_lemma_1:
  "is_last_var_name (add_mapping s m) n \<Longrightarrow> is_mapped m (add_mapping s m) n"
by (simp add: is_mapped_lemma_2)


(*
is_last_var_name
add_mapping
update_mapping
is_mapped
*)



(*core language*)


datatype expr = NULL | NOP | INIT type var_name | SEQ expr expr | IF expr expr expr | SEC security expr

inductive 
  eval :: "expr \<Rightarrow> state \<Rightarrow> security \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
where
Nop: "eval (NOP, s) (NULL, s)" |
Seq: "[eval (e1, s1) (e1', s1'), eval (e2,s1') (e2',e2)] \<Longrightarrow> eval (SEQ e1 e2, s1) (e2', s2)" |
Seq_nop: "eval (SEQ NOP e, s) (e, s)" |
Init: "is_last_var_name s n \<Longrightarrow> eval ((INIT t n), s) (NOP, (add_mapping s (Map t Nil)))" 



(*security lemmas*)








(* OLD STUFF *)

list_length sl = n







inductive 
  is_mapped :: "mapping \<Rightarrow> state \<Rightarrow> var_name \<Rightarrow> bool"
where
is_mapped_0: "is_mapped m (State (Cons m M)) 0" |
is_mapped_S: "is_mapped m (State M) n \<Longrightarrow> is_mapped m (State (Cons w M)) (Suc n)"




thm is_mapped_S

lemma asjhqwjhbq: 
  "is_mapped (Map (Type 0) Nil) (State (Cons (Map (Type 0) Nil) Nil)) 0"
apply (rule is_mapped_0)
done 


lemma asdasdasd:
  "is_mapped (Map (Type 0) Nil) (State (Cons (Map (Type 1) Nil) (Cons (Map (Type 0) Nil) Nil))) 1"
apply simp
apply (rule is_mapped_S)
apply (rule is_mapped_0)

sorry



inductive 
  is_mapped :: mapping \<Rightarrow> state \<Rightarrow> var_name \<Rightarrow> bool
where
Is_mapped: (is_mapped m s n)
  



fun get_mapping :: "state \<Rightarrow> var_name \<Rightarrow> mapping optional" where
"get_mapping (State Nil) _ = None" |
"get_mapping (State (Cons m M)) 0 = Some m" |
"get_mapping (State (Cons m M)) (Suc n) = get_mapping (State (M)) n"




(*definition is_a_new_mapping :: "state \<Rightarrow> mapping \<Rightarrow> state \<Rightarrow> var_name \<Rightarrow> bool" where
"is_a_new_mapping s1 s2 m var_name = (0 \<equiv> 0)"*)

prop "is_a_new_mapping s1 s2 m var_name = (0 \<equiv> 0)"


lemma mapping_lemma1:
  "get_mapping (State Nil) 0 = None"
apply (simp)
done


create_mapping
last_mapping




lemma list_append_lemma1:
  "\<forall>s1 m. get_mapping (State (list_append s1 m)) (list_length s1) = optional.Some m"
apply (auto)

sorry

lemma mapping_lemma2:
  "\<forall>s2 s1 m n. add_mapping (State s1) m = (n, (State s2)) \<longrightarrow> get_mapping (State s2) n = Some m"
apply (simp)
apply (rule list_append_lemma1)
done





type_synonym vname = string
type_synonym val = 
type_synonym state = "vname \<Rightarrow> val"

fun get ::


datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (s1 x) (s1 p) (s n)  = (s1)" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a)
apply (auto)
done

end
