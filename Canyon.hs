
-----------------------------------------------------------------------------------------------------
--
-- PROJECT
----------
-- Canyon Implementation
--
-- DESCRIPTION
--------------
-- Implementation of language model from Project Ravine, done as closely as possible
--
-- AUTHOR
---------
-- Lumberjacks Incorperated (2018)
--
-----------------------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------------------
-- INCLUDES
-----------------------------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
import GHC.TypeLits

-----------------------------------------------------------------------------------------------------
-- HELPER FUNCTIONS
-----------------------------------------------------------------------------------------------------
isJust :: Maybe a -> Bool
isJust Nothing = False
isJust _ = True

add_mapping :: State -> Mapping -> State
add_mapping (State sl) m = State (m : sl)

apply_to_map_modal_object :: State -> Varname -> (Model_obj_map -> Model_obj_map) -> State
apply_to_map_modal_object s _ _ = s

get_mapping :: State -> Varname -> Maybe Mapping
get_mapping _ _ = Nothing

-----------------------------------------------------------------------------------------------------
-- MONADIC LANGUAGE DATATYPE
-----------------------------------------------------------------------------------------------------
data Obj = O deriving Show

type Model_obj_map = Obj
type Model_obj_value = Obj
type Model_obj_init = Obj
type Model_obj_op = Obj

-----------------------------------------------------------------------------------------------------
-- CORE LANGUAGE DATATYPE
-----------------------------------------------------------------------------------------------------
type Security = Int
type Varname = Int

data TYPE = Type Security deriving Show
data Mapping = Map Model_obj_map Varname TYPE deriving Show
data State = State [Mapping] deriving Show

empty_state = State []
base_security = 0

data Expr = NULL | NOP | SEQ Expr Expr | INIT Model_obj_init TYPE Varname | VALUE Model_obj_value TYPE 
  | VAR Varname | ASSIGN Varname Expr | OP Model_obj_op Expr Expr | IF Expr Expr Expr | WHILE Expr Expr 
  | EXPR_ERROR String      deriving Show

-----------------------------------------------------------------------------------------------------
-- MONADIC FUNCTION DEFINITIONS
-----------------------------------------------------------------------------------------------------
modal_eval_assign :: Model_obj_value -> Model_obj_map -> Model_obj_map
modal_eval_assign _ _ = O

modal_eval_init :: Model_obj_init -> Model_obj_map
modal_eval_init _ = O

modal_eval_op :: Model_obj_op -> Model_obj_value -> Model_obj_value -> Model_obj_value
modal_eval_op _ _ _ = O

modal_eval_branch :: Model_obj_value -> Bool
modal_eval_branch _ = True

modal_eval_value :: Model_obj_map -> Model_obj_value
modal_eval_value _ = O

-----------------------------------------------------------------------------------------------------
-- CORE FUNCTION DECLARATIONS
-----------------------------------------------------------------------------------------------------
eval_step :: Expr -> State -> Security -> (Expr, State)

eval_step (EXPR_ERROR es) s _ = (EXPR_ERROR es, s)
eval_step (SEQ (EXPR_ERROR es) _) s _ = (EXPR_ERROR es, s)
eval_step (SEQ _ (EXPR_ERROR es)) s _ = (EXPR_ERROR es, s)
eval_step (ASSIGN _ (EXPR_ERROR es)) s _ = (EXPR_ERROR es, s)
eval_step (OP _ (EXPR_ERROR es) _) s _ = (EXPR_ERROR es, s)
eval_step (OP _ _ (EXPR_ERROR es)) s _ = (EXPR_ERROR es, s)
eval_step (IF (EXPR_ERROR es) _ _) s _ = (EXPR_ERROR es, s)
eval_step (IF _ (EXPR_ERROR es) _) s _ = (EXPR_ERROR es, s)
eval_step (IF _ _ (EXPR_ERROR es)) s _ = (EXPR_ERROR es, s)
eval_step (WHILE (EXPR_ERROR es) _) s _ = (EXPR_ERROR es, s)
eval_step (WHILE _ (EXPR_ERROR es)) s _ = (EXPR_ERROR es, s)

eval_step (SEQ (VALUE _ _) _) s _ = (EXPR_ERROR "Trash", s)
eval_step (SEQ _ (VALUE _ _)) s _ = (EXPR_ERROR "Trash", s)
eval_step (ASSIGN _ NULL) s _ = (EXPR_ERROR "Trash", s)
eval_step (OP _ NULL _) s _ = (EXPR_ERROR "Trash", s)
eval_step (OP _ _ NULL) s _ = (EXPR_ERROR "Trash", s)
eval_step (IF NULL _ _) s _ = (EXPR_ERROR "Trash", s)
eval_step (IF _ (VALUE _ _) _) s _ = (EXPR_ERROR "Trash", s)
eval_step (IF _ _ (VALUE _ _)) s _ = (EXPR_ERROR "Trash", s)
eval_step (WHILE NULL _) s _ = (EXPR_ERROR "Trash", s)
eval_step (WHILE _ (VALUE _ _)) s _ = (EXPR_ERROR "Trash", s)

eval_step (VALUE mobj t) s sec = (VALUE mobj t, s)

eval_step NULL s sec = (NULL, s)

eval_step NOP s sec = (NULL, s)

eval_step (SEQ NULL NULL) s sec = (NULL, s) 
eval_step (SEQ NULL e2) s sec = eval_step e2 s sec
eval_step (SEQ e1 e2) s sec = let (er1, sr1) = eval_step e1 s sec in (SEQ er1 e2, sr1)

eval_step (INIT mobj (Type tsec) n) s' sec | (tsec >= sec) = (NULL, (add_mapping s' (Map (modal_eval_init mobj) n (Type tsec))))

eval_step (ASSIGN n (VALUE mobj (Type tsec))) s' sec | (isJust (get_mapping s' n) == True) = let (Just (Map mapped_mobj mapped_n (Type vsec))) = get_mapping s' n in (if ((vsec >= tsec) && (vsec >= sec)) then (NULL, apply_to_map_modal_object s' n (modal_eval_assign mobj)) else (EXPR_ERROR "ASSIGN!!! trash program (Some trash wrote trash...)", s'))
eval_step (ASSIGN n e') s' sec = let (e, s) = eval_step e s sec in (ASSIGN n e, s)

eval_step (VAR n) s sec | (isJust (get_mapping s n)) = let (Just (Map mobj n t)) = get_mapping s n in (VALUE (modal_eval_value mobj) t, s)

eval_step (OP mobjop (VALUE mobj1 (Type tsec1)) (VALUE mobj2 (Type tsec2))) s sec = ((VALUE (modal_eval_op mobjop mobj1 mobj2) (Type (max tsec1 tsec2))), s) 
eval_step (OP mobjop (VALUE mobj1 (Type tsec1)) e2') s' sec = let (e2, s) = eval_step e2' s' sec in (OP mobjop (VALUE mobj1 (Type tsec1)) e2, s)
eval_step (OP mobjop e1' e2') s' sec = let (e1, s) = eval_step e1' s' sec in (OP mobjop e1 e2', s)

eval_step (IF (VALUE mobj (Type tsec)) NULL NULL) s sec | (tsec >= sec && modal_eval_branch mobj == True) = (NULL, s)
eval_step (IF (VALUE mobj (Type tsec)) NULL eelse') s' sec | (tsec >= sec && modal_eval_branch mobj == True) = let (eelse, s) = eval_step eelse' s' tsec in (IF (VALUE mobj (Type tsec)) NULL eelse, s')
eval_step (IF (VALUE mobj (Type tsec)) ethen' eelse') s' sec | (tsec >= sec && modal_eval_branch mobj == True) = let (ethen, s) = eval_step ethen' s' tsec in (IF (VALUE mobj (Type tsec)) ethen eelse', s)
eval_step (IF (VALUE mobj (Type tsec)) NULL NULL) s sec | (tsec >= sec && modal_eval_branch mobj == False) = (NULL, s)
eval_step (IF (VALUE mobj (Type tsec)) NULL eelse') s' sec | (tsec >= sec && modal_eval_branch mobj == False) = let (eelse, s) = eval_step eelse' s' tsec in (IF (VALUE mobj (Type tsec)) NULL eelse, s)
eval_step (IF (VALUE mobj (Type tsec)) ethen' eelse') s' sec | (tsec >= sec && modal_eval_branch mobj == False) = let (ethen, s) = eval_step ethen' s' tsec in (IF (VALUE mobj (Type tsec)) ethen eelse', s')
eval_step (IF expr' ethen' eelse') s' sec = let (expr, s) = eval_step expr' s' sec in (IF expr ethen' eelse', s)

eval_step (WHILE econd eloop) s' sec = (IF econd (SEQ eloop (WHILE econd eloop)) NULL, s')

eval_step _ s _ = (EXPR_ERROR "trash program (Some trash wrote trash...)", s)

-----------------------------------------------------------------------------------------------------
-- HIGHER LANGUAGE FUNCTION DECLARATIONS
-----------------------------------------------------------------------------------------------------
exec_canyon' :: Int -> (Expr, State) -> (Expr, State)
exec_canyon' n (e, s) 
                  | n <= 0 = (e, s)
                  | n > 0 = exec_canyon' (n-1) (eval_step e s 0)

exec_canyon :: Expr -> Int -> (Expr, State)
exec_canyon e n = exec_canyon' n (e, empty_state)

-----------------------------------------------------------------------------------------------------
-- TEST DRIVER
-----------------------------------------------------------------------------------------------------
program_test = OP O (OP O ((VALUE O (Type 2))) (VALUE O (Type 6))) (VALUE O (Type 99))

program_result = exec_canyon program_test 2

main = do
    putStrLn ""  
    putStrLn (show (program_result))
    putStrLn ""







