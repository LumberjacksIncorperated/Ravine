theory RavineCore imports Main begin

(*----------------------------------------------------------------------------------------------------*)
(*                                        General List Functions                                      *)
(*----------------------------------------------------------------------------------------------------*)

(*
  List Length - Recurses down the list one element at a time
*)
fun list_length :: "'a list \<Rightarrow> nat" where
  "list_length Nil = 0" |
  "list_length (Cons n N) = Suc (list_length N)"

(*
  List Append - Appends an element to the innermost element position
*)
fun list_append :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_append Nil a = Cons a Nil" |
  "list_append (Cons n N) a = Cons n (list_append N a)"

(*
  List Update - Changes list entry for corresponding variable 
*)
fun list_update :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list_update Nil _ _ = Nil" |
  "list_update (Cons m M) v 0 = (Cons v M)" |
  "list_update (Cons m M) v (Suc n) = (Cons m (list_update M v n))"


(*----------------------------------------------------------------------------------------------------*)
(*                                    Created Data Types For Language                                 *)
(*----------------------------------------------------------------------------------------------------*)

(* Security Level for Variable/Operation *)
type_synonym security = nat

(* Variable name is represented as an Natural Number *)
type_synonym var_name = nat

(* The Security Type of a Variable/Expression *)
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
  is_mapped :: "state \<Rightarrow> mapping \<Rightarrow> bool"
where
  is_mapped_0: "is_mapped (State (Cons (Map n t) M)) (Map n t)" |
  is_mapped_S: "n2 \<noteq> n \<Longrightarrow> is_mapped (State M) (Map n t) \<Longrightarrow> is_mapped (State (Cons (Map n2 t2) M)) (Map n t)"

(*is_mapped_inversion*)

lemma is_mapped_inversion: "is_mapped s m \<Longrightarrow> ((\<exists> n t M. (s = (State (Cons (Map n t) M)) \<and> m = (Map n t))) 
                                            \<or> (\<exists> n2 n M t t2. (is_mapped (State M) (Map n t) \<and> n2 \<noteq> n \<and> 
                                                  (s = (State (Cons (Map n2 t2) M)) \<and> m = (Map n t)))))"
  apply (rule is_mapped.cases)
  apply blast+
  done


(* Meta Lemmas *)


lemma mapping_soundness:
  "add_mapping s1 (Map n t) = s2 \<Longrightarrow> is_mapped s2 (Map n t)"
  by (metis add_mapping.simps is_mapped_0 state.exhaust)



lemma mapping_preservation: "n \<noteq> n2 \<Longrightarrow> is_mapped s1 (Map n t) \<Longrightarrow> 
  add_mapping s1 (Map n2 t2) = s2 \<Longrightarrow> is_mapped s2 (Map n t)"
  by (smt add_mapping.simps is_mapped.simps)

lemma empty_state_existance: "\<not>(is_mapped empty_state (Map n t))"
  by (metis empty_state_def is_mapped.simps list.simps(3) state.inject)

(* Core Language *)

datatype expr = NULL | NOP | SEQ expr expr | INIT type var_name | VALUE type 
  | VAR var_name | ASSIGN var_name expr | OP expr expr | IF expr expr expr | WHILE expr expr
  | RAISE security expr

inductive 
  eval :: "expr \<Rightarrow> state \<Rightarrow> security \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
  where

Constant: "eval (VALUE t) s sec (VALUE t) s" |

Null: "eval NULL s sec NULL s" |

Nop: "eval NOP s sec NULL s" |

Raise: "secr \<ge> sec \<Longrightarrow> eval e s' secr NULL s \<Longrightarrow> 
        eval (RAISE secr e) s' sec NULL s" |

Seq: "    eval e1 s1 sec1 NULL s2 
      \<Longrightarrow> eval e2 s2 sec2 NULL s3 
      \<Longrightarrow> sec1 \<ge> sec3 
      \<Longrightarrow> sec2 \<ge> sec3 
      \<Longrightarrow> eval (SEQ e1 e2) s1 sec3 NULL s3" |

Init: "     \<not>(\<exists>t. is_mapped s' (Map n t))
        \<Longrightarrow> s = (add_mapping s' (Map n (Type tsec)))
        \<Longrightarrow> tsec \<ge> sec
        \<Longrightarrow> eval (INIT (Type tsec) n) s' sec NULL s" |

Assign: "    is_mapped s' (Map n (Type vsec))
         \<Longrightarrow> eval e s' sec (VALUE (Type tsec)) s
         \<Longrightarrow> vsec \<ge> tsec
         \<Longrightarrow> vsec \<ge> sec
         \<Longrightarrow> eval (ASSIGN n e) s' sec NULL s" |

Var: "is_mapped s (Map n t) \<Longrightarrow> eval (VAR n) s sec (VALUE t) s" |

Op: "    tsec3 = max tsec1 tsec2
     \<Longrightarrow> eval e1 s1 sec (VALUE (Type tsec1)) s2
     \<Longrightarrow> eval e2 s2 sec (VALUE (Type tsec2)) s3
     \<Longrightarrow> eval (OP e1 e2) s1 sec (VALUE (Type tsec3)) s3" |

If_then: "    eval econd s1 sec (VALUE (Type tsec)) s2
          \<Longrightarrow> eval ethen s2 tsec NULL s3
          \<Longrightarrow> eval eelse s2 tsec NULL s4 
          \<Longrightarrow> tsec \<ge> sec
          \<Longrightarrow> eval (IF econd ethen eelse) s1 sec NULL s3" |

If_else: "    eval econd s1 sec (VALUE (Type tsec)) s2 
          \<Longrightarrow> eval ethen s2 tsec NULL s3 
          \<Longrightarrow> eval eelse s2 tsec NULL s4
          \<Longrightarrow> tsec \<ge> sec
          \<Longrightarrow> eval (IF econd ethen eelse) s1 sec NULL s4" |

While: "eval (IF econd (SEQ eloop (WHILE econd eloop)) NULL) s' sec NULL s
  \<Longrightarrow> eval (WHILE econd eloop) s' sec NULL s"

(*
While_true: "    eval econd s1 sec (VALUE (Type tsec)) s2
             \<Longrightarrow> eval eloop s2 tsec NULL s3 
             \<Longrightarrow> sec \<ge> tsec
             \<Longrightarrow> eval (WHILE econd eloop) s1 tsec (WHILE econd eloop) s3" |

While_false: "    eval econd s1 sec (VALUE (Type tsec)) s2 
              \<Longrightarrow> eval eloop s2 tsec NULL s3 
              \<Longrightarrow> sec \<ge> tsec
              \<Longrightarrow> eval (WHILE econd eloop) s1 tsec (NULL) s2"
*)



(* Inversion Lemmas *)

lemma seq_inversion: "eval (SEQ e1' e2') s3' sec3 e3 s3 \<Longrightarrow> 
  (\<exists>sec1  s4 sec2 . (eval e1' s3' sec1 NULL s4 \<and> eval e2' s4 sec2 NULL s3 \<and> sec1 \<ge> sec3 \<and> sec2 \<ge> sec3))"
  apply (rule eval.cases)
  apply (auto)
  done

lemma init_inversion: "eval (INIT t vn) s' sec e s \<Longrightarrow>
  (\<exists> tsec. (e = NULL \<and> t = (Type tsec) \<and> tsec \<ge> sec \<and> s = (add_mapping s' (Map vn (Type tsec))) \<and> \<not>(\<exists> t. is_mapped s' (Map vn t))))"
  apply (rule eval.cases)
  apply (auto)
  done

lemma assign_inversion: "eval (ASSIGN n e) s' sec er s \<Longrightarrow>
  (\<exists> vsec tsec . (er = NULL \<and> vsec \<ge> sec \<and> vsec \<ge> tsec \<and> eval e s' sec (VALUE (Type tsec)) s \<and> is_mapped s' (Map n (Type vsec))))"
  apply (rule eval.cases)
  apply (auto)
  done

lemma var_inversion: "eval (VAR n) s' sec e s \<Longrightarrow> (\<exists> t. (e = (VALUE t) \<and> is_mapped s' (Map n t)))"
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
  (\<exists>tsec s2 eelse2 ethen2 s5 s6. (eval econd s1 sec (VALUE (Type tsec)) s2 
  \<and> tsec \<ge> sec \<and> eval eelse s2 tsec NULL s5 \<and> eval ethen s2 tsec NULL s6 \<and> (s5 = s3 \<or> s6 = s3)))"
  apply (rule  eval.cases)
  apply auto
  done

lemma while_inversion: "eval (WHILE econd eloop) s' sec e s \<Longrightarrow>
  (e = NULL \<and> eval (IF econd (SEQ eloop (WHILE econd eloop)) NULL) s' sec NULL s)"
  apply (rule  eval.cases)
  apply auto
  done

(*
lemma while_inversion: "eval (WHILE econd eloop) s1 tsec e sss \<Longrightarrow>
  (\<exists>s3 sec eloop2 s2.(eval econd s1 sec (VALUE (Type tsec)) s2 \<and> sec \<ge> tsec \<and> eval eloop s2 tsec NULL s3
   \<and> ((sss = s3 \<and> e = (WHILE econd eloop2)) \<or> (sss = s2 \<and> e = NULL))))"
  apply (rule  eval.cases)
  apply auto
  done
*)


(*
(* Completeness *)
(*e1' \<noteq> NULL \<longrightarrow> e2' \<noteq> NULL \<longrightarrow> *)
lemma Completeness_Seq: "eval (SEQ e1' e2') s3' sec3 e3 s3 \<Longrightarrow> 
  (\<exists>s1' sec1 e1 s1 s2' sec2 e2 s2. (eval e1' s1' sec1 e1 s1 \<and> eval e2' s2' sec2 e2 s2))"
  using seq_inversion by fastforce
*)


(* Sec Increasing and Complete*)


lemma SecIncreasingComplete_Raise: "eval (RAISE secr e) s' sec er s 
  \<Longrightarrow> (\<exists> sec2. (eval e s' sec2 NULL s \<and> er = NULL \<and> sec2 \<ge> secr \<and> secr \<ge> sec))"
  apply (rule eval.cases)
  apply auto
  done



lemma SecIncreasingComplete_Seq: "eval (SEQ e1' e2') s3' sec3 e3 s3 
  \<Longrightarrow> (\<exists> sec1 e1 e2 sec2 s2'. (eval e1' s3' sec1 e1 s2' \<and> eval e2' s2' sec2 e2 s3 \<and> sec1 \<ge> sec3 \<and> sec2 \<ge> sec3))"
  apply(frule seq_inversion)
  apply(auto)
  apply blast+
  done

lemma SecIncreasingComplete_Assign: "eval (ASSIGN n ev') s' sec e s \<Longrightarrow> 
  (\<exists> s1' sec1 e1 s1. eval ev' s' sec1 e1 s1 \<and> sec1 \<ge> sec)"
  by (meson assign_inversion dual_order.refl)


lemma SecIncreasingComplete_Op: "eval (OP e1' e2') s3' sec3 e3 s3 
  \<Longrightarrow> (\<exists> sec1 e1 e2 sec2 s2' s4. (eval e1' s3' sec1 e1 s2' \<and> eval e2' s2' sec2 e2 s4 \<and> sec1 \<ge> sec3 \<and> sec2 \<ge> sec3))"
  by (meson le_less op_inversion)


lemma SecIncreasingComplete_If: "eval (IF e1' e2' e3') s3' sec3 e3 s3 
  \<Longrightarrow> (\<exists> sec1 e1 sec2 s2' s4 q1 q3 sec. (eval e1' s3' sec1 e1 s2' \<and> eval e2' s2' sec2 NULL s4 \<and> eval e3' q1 sec NULL q3 \<and> sec1 \<ge> sec3 \<and> sec2 \<ge> sec3 \<and> sec \<ge> sec3))"
  using if_inversion by fastforce


lemma SecIncreasingComplete_While: "eval (WHILE e1' e2') s3' sec3 e3 s3 
  \<Longrightarrow> (\<exists> sec1 e1 e2 sec2 s2' s4. (eval e1' s3' sec1 e1 s2' \<and> eval e2' s2' sec2 e2 s4 \<and> sec1 \<ge> sec3 \<and> sec2 \<ge> sec3))"
  apply (frule while_inversion)
  apply clarsimp
  apply (frule if_inversion)
  by (meson le_trans order_refl seq_inversion)
  



 (*

datatype expr =
  | OP expr expr | IF expr expr expr | WHILE expr expr

*)

(*assignment mapping*)

lemma Assignment_Mapping: "eval (ASSIGN n e) s' sec e2 s 
  \<Longrightarrow> (\<exists>vsec. is_mapped s' (Map n (Type vsec)))"
  apply (frule assign_inversion)
  apply auto
  done

(*Assignment Expression value*)

lemma Assignment_Value_Expression_Complete: "eval (ASSIGN n ev') s' sec e s \<Longrightarrow> 
  (\<exists> t s1. eval ev' s' sec (VALUE t) s1)"
  using assign_inversion by blast

(*init validity*)

lemma Init_Validity: "eval (INIT t n) s' sec e2 s \<Longrightarrow> is_mapped s (Map n t)"
  apply (frule init_inversion)
  using mapping_soundness by blast

(*var validity*)

lemma Var_Validity: "eval (VAR n) s' sec (VALUE t) s \<Longrightarrow> is_mapped s' (Map n t)"
  using var_inversion by blast





(*is_mapped determinism*)

lemma is_mapped_determinism': "is_mapped (State xa) (Map n t1) \<Longrightarrow> is_mapped (State xa) (Map n t2) \<Longrightarrow> t1 = t2"
  apply (induction xa arbitrary: n t1 t2)
  using empty_state_def empty_state_existance apply auto[1]
  apply (drule is_mapped_inversion)
  apply (drule is_mapped_inversion)
  by auto

lemma is_mapped_determinism: "is_mapped s' (Map n t1) \<Longrightarrow> is_mapped s' (Map n t2) \<Longrightarrow> t1 = t2"
  apply (induct s')
  apply (rule is_mapped_determinism')
  apply simp+
  done



(*value determinism*)


lemma asjkhqwjkhge: "eval NULL s' sec1 (VALUE t1) s1 \<Longrightarrow> eval NULL s' sec2 (VALUE t2) s2 \<Longrightarrow> t1 = t2"
  try
  sorry

lemma value_determinism: "eval e s' sec1 (VALUE t1) s1 \<Longrightarrow> eval e s' sec2 (VALUE t2) s2 \<Longrightarrow> t1 = t2"
  apply (induction e arbitrary: s' sec1 sec2 s1 s2 t1 t2)
  try
  
  apply (induction e arbitrary: s' sec1 sec2 s1 s2 t1 t2)
  
  apply simp+
  using Var_Validity is_mapped_determinism apply blast
  
  apply simp
  apply (drule op_inversion)
  apply (drule op_inversion)
  
             
           
  sorry





(*security lemmas*)




lemma Assignment_Security_Type': "eval (ASSIGN n e) s' sec e3 s 
   \<Longrightarrow> (\<exists> vsec ve. eval e s' sec (VALUE (Type ve)) s \<and> is_mapped s' (Map n (Type vsec)) \<and> vsec \<ge> ve)"
  using assign_inversion by blast




lemma Assignment_Security_Type: "eval (ASSIGN n e) s' sec e3 s \<Longrightarrow> eval e s' sec (VALUE (Type ve)) s
   \<Longrightarrow> is_mapped s' (Map n (Type vsec)) \<Longrightarrow> vsec \<ge> ve"
  by (metis assign_inversion is_mapped_determinism type.inject value_determinism)


lemma Assignment_Security_Context: "eval (ASSIGN n e) s' sec e3 s \<Longrightarrow> is_mapped s' (Map n (Type vsec)) \<Longrightarrow> vsec \<ge> sec"
  using assign_inversion is_mapped_determinism by blast

lemma Init_Security_Context: "eval (INIT (Type tsec) n) s' sec e s \<Longrightarrow> tsec \<ge> sec"
  using init_inversion by blast

