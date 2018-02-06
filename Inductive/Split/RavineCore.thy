theory RavineCore imports Main begin

(* General List Functions *)

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

(* Created Data Types For Language *)

type_synonym security = nat
type_synonym var_name = nat
datatype type = Type security
datatype mapping = Map var_name type
datatype state = State "mapping list"

(* Function and Inductive Definitions *)

fun add_mapping :: "state \<Rightarrow> mapping \<Rightarrow> state" where
  "add_mapping (State sl) m = State (m # sl)"


definition empty_state :: "state" where
"empty_state = State []"


(*fun update_mapping :: "state \<Rightarrow> mapping \<Rightarrow> var_name \<Rightarrow> state" where
  "update_mapping (State l) m name = State (list_update l m name)"*)

inductive 
  is_mapped :: "state \<Rightarrow> var_name \<Rightarrow> type \<Rightarrow> bool"
where
  is_mapped_0: "is_mapped (State (Cons (Map n t) M)) n t" |
  is_mapped_S: "n2 \<noteq> n \<Longrightarrow> is_mapped (State M) n t \<Longrightarrow> is_mapped (State (Cons (Map n2 t2) M)) n t"

(* Meta Lemmas *)


lemma mapping_soundness:
  "add_mapping s1 (Map n t) = s2 \<Longrightarrow> is_mapped s2 n t"
  by (metis add_mapping.simps is_mapped_0 state.exhaust)



lemma mapping_preservation: "n \<noteq> n2 \<Longrightarrow> is_mapped s1 n t \<Longrightarrow> 
  add_mapping s1 (Map n2 t2) = s2 \<Longrightarrow> is_mapped s2 n t"
  by (smt add_mapping.simps is_mapped.simps)

lemma empty_state_existance: "\<not>(is_mapped empty_state n t)"
  by (metis empty_state_def is_mapped.simps list.simps(3) state.inject)

(* Core Language *)

datatype expr = NULL | NOP | SEQ expr expr | INIT type var_name | VALUE type 
  | VAR var_name | ASSIGN var_name expr | OP expr expr | IF expr expr expr | WHILE expr expr

inductive 
  eval :: "expr \<Rightarrow> state \<Rightarrow> security \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
  where

Seq: "    eval e1 s1 sec1 e1' s2 
      \<Longrightarrow> eval e2 s2 sec2 e2' s3 
      \<Longrightarrow> sec1 \<ge> sec3 
      \<Longrightarrow> sec2 \<ge> sec3 
      \<Longrightarrow> eval (SEQ e1 e2) s1 sec3 (SEQ e1' e2') s3" |

Seq_null: "eval (SEQ NULL NULL) s sec NULL s" |

Null: "eval NULL s sec NULL s" |

Nop: "eval NOP s sec NULL s" |

Init: "     \<not>(\<exists>t. is_mapped s' n t)
        \<Longrightarrow> s = (add_mapping s' (Map n (Type tsec)))
        \<Longrightarrow> tsec \<ge> sec
        \<Longrightarrow> eval (INIT (Type tsec) n) s' sec NULL s" |

Assign: "    is_mapped s n (Type vsec)
         \<Longrightarrow> eval e s' sec (VALUE (Type tsec)) s
         \<Longrightarrow> vsec \<ge> tsec
         \<Longrightarrow> vsec \<ge> sec
         \<Longrightarrow> eval (ASSIGN n e) s' sec NULL s" |

Var: "is_mapped s' n t \<Longrightarrow> eval (VAR n) s' sec (VALUE t) s" |

Op: "    tsec3 = max tsec1 tsec2
     \<Longrightarrow> eval e1 s1 sec (VALUE (Type tsec1)) s2
     \<Longrightarrow> eval e2 s2 sec (VALUE (Type tsec2)) s3
     \<Longrightarrow> eval (OP e1 e2) s1 sec (VALUE (Type tsec3)) s3" |

If_then: "    eval econd s1 sec (VALUE (Type tsec)) s2
          \<Longrightarrow> eval ethen s2 tsec ethen2 s3
          \<Longrightarrow> eval eelse s2 tsec eelse2 s3 
          \<Longrightarrow> eval (IF econd ethen eelse) s1 sec ethen2 s3" |

If_else: "    eval econd s1 sec (VALUE (Type tsec)) s2 
          \<Longrightarrow> eval ethen s2 tsec ethen2 s3 
          \<Longrightarrow> eval eelse s2 tsec eelse2 s3
          \<Longrightarrow> eval (IF econd ethen eelse) s1 sec eelse2 s3" |

While_true: "    eval econd s1 sec (VALUE (Type tsec)) s2
             \<Longrightarrow> eval eloop s2 tsec eloop2 s3 
             \<Longrightarrow> eval (WHILE econd eloop) s1 tsec (WHILE econd eloop2) s3" |

While_false: "    eval econd s1 sec (VALUE (Type tsec)) s2 
              \<Longrightarrow> eval eloop s2 tsec eloop2 s3 
              \<Longrightarrow> eval (WHILE econd eloop) s1 tsec (NULL) s2"

(* Inversion Lemmas *)

lemma seq_inversion: "eval (SEQ e1' e2') s3' sec3 e3 s3 \<Longrightarrow> 
  (\<exists>sec1 e1 s4 sec2 e2. (eval e1' s3' sec1 e1 s4 \<and> eval e2' s4 sec2 e2 s3 \<and> sec1 \<ge> sec3 \<and> sec2 \<ge> sec3))"
  apply (rule eval.cases)
  apply (auto)
  apply blast+
  using Null by blast

lemma init_inversion: "eval (INIT t vn) s' sec e s \<Longrightarrow>
  (\<exists> tsec n. (e = NULL \<and> t = (Type tsec) \<and> tsec \<ge> sec \<and> s = (add_mapping s' (Map n (Type tsec))) \<and> \<not>(\<exists> t. is_mapped s' n t)))"
  apply (rule eval.cases)
  apply (auto)
  done

lemma assign_inversion: "eval (ASSIGN n e) s' sec er s \<Longrightarrow>
  (\<exists> vsec tsec . (er = NULL \<and> vsec \<ge> sec \<and> vsec \<ge> tsec \<and> eval e s' sec (VALUE (Type tsec)) s \<and> is_mapped s n (Type vsec)))"
  apply (rule eval.cases)
  apply (auto)
  done

lemma var_inversion: "eval (VAR n) s' sec e s \<Longrightarrow> (\<exists> t. (e = (VALUE t) \<and> is_mapped s' n t))"
  apply (rule eval.cases)
  apply auto
  done

lemma op_inversion: "eval (OP e1 e2) s1 sec e s3 \<Longrightarrow>
  (\<exists> tsec3 tsec1 tsec2 s2. (e = (VALUE (Type tsec3)) \<and> tsec3 = max tsec1 tsec2 
  \<and> eval e1 s1 sec (VALUE (Type tsec1)) s2 \<and> eval e2 s2 sec (VALUE (Type tsec2)) s3))"
  apply (rule  eval.cases)
  apply auto
  done

lemma if_inversion: "eval (IF econd ethen eelse) s1 sec ethen2_or_eelse2 s3 \<Longrightarrow> 
  (\<exists>tsec s2 eelse2 ethen2. (eval econd s1 sec (VALUE (Type tsec)) s2 
  \<and> eval eelse s2 tsec eelse2 s3 \<and> eval ethen s2 tsec ethen2 s3 \<and> 
  (ethen2_or_eelse2 = eelse2 \<or> ethen2_or_eelse2 = ethen2)))"
  apply (rule  eval.cases)
  apply auto
  done

lemma while_inversion: "eval (WHILE econd eloop) s1 tsec e sss \<Longrightarrow>
  (\<exists>s3 eloop2 sec s2.(eval econd s1 sec (VALUE (Type tsec)) s2 \<and> eval eloop s2 tsec eloop2 s3
   \<and> ((sss = s3 \<and> e = (WHILE econd eloop2)) \<or> (sss = s2 \<and> e = NULL))))"
  apply (rule  eval.cases)
  apply auto
  done

(*
(* Completeness *)
(*e1' \<noteq> NULL \<longrightarrow> e2' \<noteq> NULL \<longrightarrow> *)
lemma Completeness_Seq: "eval (SEQ e1' e2') s3' sec3 e3 s3 \<Longrightarrow> 
  (\<exists>s1' sec1 e1 s1 s2' sec2 e2 s2. (eval e1' s1' sec1 e1 s1 \<and> eval e2' s2' sec2 e2 s2))"
  using seq_inversion by fastforce
*)


(* Sec Increasing and Complete*)
lemma SecIncreasingComplete_Seq: "eval (SEQ e1' e2') s3' sec3 e3 s3 
  \<Longrightarrow> (\<exists> sec1 e1 e2 sec2 s2'. (eval e1' s3' sec1 e1 s2' \<and> eval e2' s2' sec2 e2 s3 \<and> sec1 \<ge> sec3 \<and> sec2 \<ge> sec3))"
  apply(frule seq_inversion)
  apply(auto)
  apply blast+
  done

lemma SecIncreasingComplete_Assign: "eval (ASSIGN n ev') s' sec e s \<Longrightarrow> 
  (\<exists> ev' s1' sec1 e1 s1. eval ev' s1' sec1 e1 s1 \<and> sec1 \<ge> sec)"
  by blast

 ASSIGN var_name expr | OP expr expr | IF expr expr expr | WHILE expr expr

(*assignment mapping*)

lemma Assignment_Mapping: "\<forall>n e s' sec e2 s. eval (ASSIGN n e) s' sec e2 s \<longrightarrow> (\<exists>vsec. is_mapped (Map (Type vsec)) s' n)"
  sorry

(*init validity*)

lemma Init_Validity: "\<forall>t n s' sec e2 s. eval (INIT t n) s' sec e2 s \<longrightarrow> is_mapped (Map t) s n"
  sorry

(*var validity*)

lemma Var_Validity: "\<forall>n s' sec t s. eval (VAR n) s' sec (VALUE t) s \<longrightarrow> is_mapped (Map t) s' n"
  apply (auto)
  apply (rule var_inversion)
  apply (simp)
  done

(*security lemmas*)




lemma Assignment_Security: "\<forall>n e s' esec s2' s2 e2 sec s vsec e3. eval (ASSIGN n e) s' sec e3 s 
  \<longrightarrow> eval e s2' esec e2 s2 \<longrightarrow> is_mapped (Map (Type vsec)) s' n \<longrightarrow> vsec \<ge> esec"
  sorry


lemma Init_Security: "\<forall> tsec n s' sec e s. eval (INIT (Type tsec) n) s' sec e s \<longrightarrow> tsec \<ge> sec"
  sorry











(* OLD STUFF *)

(*list_length sl = n*)







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
