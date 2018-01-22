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

fun get_mapping :: "state \<Rightarrow> var_name \<Rightarrow> mapping optional" where
"get_mapping (State Nil) _ = None" |
"get_mapping (State (Cons m M)) 0 = Some m" |
"get_mapping (State (Cons m M)) (Suc n) = get_mapping (State (M)) n"

fun add_mapping' :: "mapping list \<Rightarrow> mapping \<Rightarrow> mapping list" where
"add_mapping' Nil m = Cons m Nil" |
"add_mapping' (Cons n N) m = Cons n (add_mapping' N m)" 

fun add_mapping :: "state \<Rightarrow> mapping \<Rightarrow> state" where
"add_mapping (State sl) m = State (add_mapping' sl m)"


fun get_last_var_name' :: "mapping \<Rightarrow> mapping list \<Rightarrow> var_name" where
"get_last_var_name' m Nil = 0" |
"get_last_var_name' m (Cons n N) = Suc (get_last_var_name' n N)"

fun get_last_var_name :: "state \<Rightarrow> var_name optional" where
"get_last_var_name (State Nil) = None" |
"get_last_var_name (State (Cons n N)) = Some (get_last_var_name' n N)"

fun update_mapping :: "state \<Rightarrow> mapping \<Rightarrow> var_name \<Rightarrow> state" where
"update_mapping (State l) m name = State (list_update l m name)"


definition is_a_new_mapping :: "state \<Rightarrow> mapping \<Rightarrow> state \<Rightarrow> var_name \<Rightarrow> prop" where
"is_a_new_mapping s1 s2 m var_name = True"


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
