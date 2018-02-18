
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

isNothing :: Maybe a -> Bool
isNothing Nothing = True
isNothing _ = False


-- default -> list -> index
item_at_index :: a -> [a] -> Int -> a
item_at_index d [] _ = d
item_at_index d (x:xs) n | (n <= 0) = x
                         | (n > 0) = item_at_index d xs (n-1)




add_mapping :: State -> Mapping -> State
add_mapping (State sl) m = State (m : sl)

apply_to_map_modal_object :: State -> Varname -> (Model_obj_map -> Model_obj_map) -> State
apply_to_map_modal_object (State []) _ _ = (State [])
apply_to_map_modal_object (State ((Map mobj n1 t):xs)) n2 f | (n1 == n2) = (State ((Map (f mobj) n1 t):xs))
apply_to_map_modal_object (State (x:xs)) n f = let (State xsr) = (apply_to_map_modal_object (State xs) n f) in (State (x:(xsr)))


get_mapping :: State -> Varname -> Maybe Mapping
get_mapping (State []) _ = Nothing
get_mapping (State ((Map mobj n1 t):xs)) n2 | (n1 == n2) = Just ((Map mobj n1 t))
get_mapping (State (x:xs)) n = get_mapping (State xs) n

-----------------------------------------------------------------------------------------------------
-- MONADIC LANGUAGE DATATYPE
-----------------------------------------------------------------------------------------------------

type Model_obj_map = Model_obj_map_canyon
type Model_obj_value = Model_obj_value_canyon
type Model_obj_init = Model_obj_init_canyon
type Model_obj_op = Model_obj_op_canyon

-----------------------------------------------------------------------------------------------------
-- CORE LANGUAGE DATATYPE
-----------------------------------------------------------------------------------------------------
type Security = Int
type Varname = Int

data TYPE = Type Security deriving (Eq, Show)
data Mapping = Map Model_obj_map Varname TYPE deriving (Eq, Show)
data State = State [Mapping] deriving (Eq, Show)

empty_state = State []
base_security = 0

data Expr = NULL | NOP | SEQ Expr Expr | INIT Model_obj_init TYPE Varname | VALUE Model_obj_value TYPE 
  | VAR Varname | ASSIGN Varname Expr | OP Model_obj_op Expr Expr | IF Expr Expr Expr | WHILE Expr Expr 
  | RAISE Security Expr
  | EXPR_ERROR String      deriving (Eq, Show)

-----------------------------------------------------------------------------------------------------
-- MONADIC FUNCTION DEFINITIONS
-----------------------------------------------------------------------------------------------------
modal_eval_assign :: Model_obj_value -> Model_obj_map -> Model_obj_map
modal_eval_assign = modal_eval_assign_canyon

modal_eval_init :: Model_obj_init -> Model_obj_map
modal_eval_init = modal_eval_init_canyon

modal_eval_op :: Model_obj_op -> Model_obj_value -> Model_obj_value -> Model_obj_value
modal_eval_op = modal_eval_op_canyon

modal_eval_branch :: Model_obj_value -> Bool
modal_eval_branch = modal_eval_branch_canyon

modal_eval_value :: Model_obj_map -> Model_obj_value
modal_eval_value = modal_eval_value_canyon

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

eval_step (RAISE secr NULL) s' sec | (secr >= sec) = (NULL, s')
eval_step (RAISE secr e) s' sec | (secr >= sec) = let (er1, sr1) = eval_step e s' secr in (RAISE secr er1, sr1)

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


eval_step (IF (VALUE mobj (Type tsec)) ethen eelse) s sec | (tsec >= sec && modal_eval_branch mobj == True) = (ethen, s)
eval_step (IF (VALUE mobj (Type tsec)) ethen eelse) s sec | (tsec >= sec && modal_eval_branch mobj == False) = (eelse, s)
eval_step (IF expr' ethen' eelse') s' sec = let (expr, s) = eval_step expr' s' sec in (IF expr ethen' eelse', s)

eval_step (WHILE econd eloop) s' sec = (IF econd (SEQ eloop (WHILE econd eloop)) NULL, s')

eval_step _ s _ = (EXPR_ERROR "trash program (Some trash wrote trash...)", s)

-----------------------------------------------------------------------------------------------------
-- HIGHER LANGUAGE FUNCTION DECLARATIONS
-----------------------------------------------------------------------------------------------------






exec_core' :: Int -> (Expr, State) -> IO (Expr, State)
exec_core' n (NULL, s) = return (NULL, s)
exec_core' n (e, s) 
                  | n <= 0 = do return (e, s)
                  | n > 0 = do 
                              let getchar_deuehbhjqwdhvq = get_mapping s meta_GetChar_vn
                              if (getchar_deuehbhjqwdhvq /= Nothing) then do
                                 let (Just (Map (CM d1 (value)) d2 d3)) = getchar_deuehbhjqwdhvq
                                 if (value == (CL_Bool True)) then do
                                    in_char <- getChar
                                    retval <- (exec_core' (n-1) (eval_step e (apply_to_map_modal_object s meta_GetChar_vn (modal_eval_assign_canyon ((CV (CL_Char in_char))))) 0))
                                    return retval
                                 else do
                                    retval <- (exec_core' (n-1) (eval_step e s 0))
                                    return retval
                              else do
                                 retval <- (exec_core' (n-1) (eval_step e s 0))
                                 return retval

                              

                              --retval <- 
                              --return retval

exec_core :: Expr -> Int -> IO (Expr, State)
exec_core e n = exec_core' n (e, empty_state)


-----------------------------------------------------------------------------------------------------
-- TOP LEVEL LANGUAGE
-----------------------------------------------------------------------------------------------------


type Variable = String
type SecurityLevel = Int

data CanyonType = C_Bool | C_Int | C_Char | C_List CanyonType     deriving (Eq, Show)

data CanyonValue = CL_Bool Bool | CL_Int Int | CL_Char Char | CL_List [CanyonValue] | CL_Null   deriving (Eq, Show)

data CanyonOp = Not | Eq | Gr | Le | Plus | Concat | Append | Index   deriving (Eq, Show)

data CanyonExpr = Dave | Jimmy | Block [CanyonExpr] | Init SecurityLevel CanyonType Variable | Assign SecurityLevel Variable CanyonExpr 
                    | Const SecurityLevel CanyonValue | Var Variable
                    | If SecurityLevel CanyonExpr CanyonExpr CanyonExpr | While SecurityLevel CanyonExpr CanyonExpr
                    | Un CanyonOp CanyonExpr | Bin CanyonOp CanyonExpr CanyonExpr    
                    | GetChar SecurityLevel Variable    deriving Show

data CanyonCompilationStatus = Success | Failure String deriving (Show, Eq)

data CanyonCompilationState = CCS Varname [Variable]
empty_canyon_compilation_state = CCS 0 []



meta_GetChar = "GetChar_Meta"
meta_GetChar_vn = 0

initial_canyon_compilation_state = CCS 1 [meta_GetChar]
initial_canyon_compilation_expr = (INIT (CI C_Char CL_Null) (Type base_security) meta_GetChar_vn)


new_variable_mapping :: CanyonCompilationState -> Variable -> (CanyonCompilationState, Maybe Varname)
new_variable_mapping (CCS nextN ls) v = if ((get_variable_mapping (CCS nextN ls) v) /= Nothing) then ((CCS nextN ls), Nothing)
                                            else ((CCS (nextN+1) (v:ls)), Just nextN)


get_variable_mapping :: CanyonCompilationState -> Variable -> Maybe Varname
get_variable_mapping (CCS 0 []) _ = Nothing
get_variable_mapping (CCS n (y1:ys)) y2 | (y1 == y2) = Just (n-1)
get_variable_mapping (CCS n (y:ys)) v = get_variable_mapping (CCS (n-1) (ys)) v





compile_canyon :: CanyonExpr -> (CanyonCompilationStatus, Expr)
compile_canyon e = let (status, state, expr) = compile_canyon' initial_canyon_compilation_state e in (status, SEQ initial_canyon_compilation_expr expr)





compile_canyon' :: CanyonCompilationState -> CanyonExpr -> (CanyonCompilationStatus, CanyonCompilationState, Expr)

compile_canyon' st (GetChar sec v) =   let maybe_vn = get_variable_mapping st v in
                                             if (isNothing maybe_vn) then (Failure ("Variable not initilised - " ++ v), st, NULL) else (
                                                  let (Just vn) = maybe_vn in (Success, st, SEQ (SEQ (ASSIGN meta_GetChar_vn (VALUE (CV (CL_Bool True)) (Type base_security))) (RAISE sec (ASSIGN vn (VAR meta_GetChar_vn)))) (ASSIGN meta_GetChar_vn (VALUE (CV (CL_Null)) (Type base_security))))
                                             )
                                             


compile_canyon' st (Dave) = (Success, st, NULL)
compile_canyon' st (Jimmy) = (Success, st, NOP)

compile_canyon' st (Block []) = (Success, st, NULL)
compile_canyon' st (Block (x:xs)) =   let (x_s, x_st, x_e) = compile_canyon' st x in 
                                     if (x_s /= Success) then (x_s, x_st, NULL) else (
                                        let (xs_s, xs_st, xs_e) = compile_canyon' x_st (Block xs) in
                                           if (xs_s /= Success) then (xs_s, xs_st, NULL) else (Success, xs_st, SEQ x_e xs_e)
                                     )

compile_canyon' st' (Init sec t v) =  let (st, maybe_vn) = new_variable_mapping st' v in  
                                          if (isNothing maybe_vn) then (Failure ("Variable initilised twice - " ++ v), st, NULL) else (
                                              let (Just vn) = maybe_vn in (Success, st, INIT (CI t CL_Null) (Type sec) vn)
                                          )



compile_canyon' st' (Assign sec v e') =   let (s, st, e) = compile_canyon' st' e' in
                                             if (s /= Success) then (s, st, NULL) else (
                                                let maybe_vn = get_variable_mapping st v in
                                                   if (isNothing maybe_vn) then (Failure ("Variable not initilised - " ++ v), st, NULL) else (
                                                       let (Just vn) = maybe_vn in (Success, st', RAISE sec (ASSIGN vn e))
                                                    )
                                             )


compile_canyon' st (Const sec v) = (Success, st, VALUE (CV v) (Type sec))


compile_canyon' st (Var v) =  let maybe_vn = get_variable_mapping st v in
                                 if (isNothing maybe_vn) then (Failure ("Variable not initilised - " ++ v), st, NULL) else (
                                    let (Just vn) = maybe_vn in (Success, st, VAR vn)
                                 )


compile_canyon' st (If sec e1' e2' e3') =  let (s_e1, st_e1, e1) = compile_canyon' st e1' in 
                                               if (s_e1 /= Success) then (s_e1, st_e1, NULL) else (
                                                  let (s_e2, st_e2, e2) = compile_canyon' st e2' in 
                                                     if (s_e2 /= Success) then (s_e2, st_e2, NULL) else (
                                                        let (s_e3, st_e3, e3) = compile_canyon' st e3' in 
                                                           if (s_e3 /= Success) then (s_e3, st_e3, NULL) else (
                                                              (Success, st, RAISE sec (IF e1 e2 e3))
                                                           )
                                                     )
                                               )


compile_canyon' st (While sec e1' e2') =      let (s_e1, st_e1, e1) = compile_canyon' st e1' in 
                                                 if (s_e1 /= Success) then (s_e1, st_e1, NULL) else (
                                                    let (s_e2, st_e2, e2) = compile_canyon' st e2' in 
                                                       if (s_e2 /= Success) then (s_e2, st_e2, NULL) else (
                                                          (Success, st, RAISE sec (WHILE e1 e2))
                                                       )
                                                 )


compile_canyon' st (Bin cop e1' e2') =        let (s_e1, st_e1, e1) = compile_canyon' st e1' in 
                                                 if (s_e1 /= Success) then (s_e1, st_e1, NULL) else (
                                                    let (s_e2, st_e2, e2) = compile_canyon' st e2' in 
                                                       if (s_e2 /= Success) then (s_e2, st_e2, NULL) else (
                                                          (Success, st, OP (CO cop) e1 e2)
                                                       )
                                                 )

compile_canyon' st (Un cop e1') =             let (s_e1, st_e1, e1) = compile_canyon' st e1' in 
                                                 if (s_e1 /= Success) then (s_e1, st_e1, NULL) else (
                                                    (Success, st, OP (CO cop) e1 (VALUE (CV CL_Null) (Type base_security)))
                                                 )



--compile_canyon' st _ = (Failure "Dave", st, NULL)











-----------------------------------------------------------------------------------------------------
-- CONCREATE MONADIC DEFINITIOANS
-----------------------------------------------------------------------------------------------------


--data Obj = O deriving Show



data Model_obj_map_canyon = CM CanyonType CanyonValue deriving (Eq, Show)
data Model_obj_value_canyon = CV CanyonValue deriving (Eq, Show)
data Model_obj_init_canyon = CI CanyonType CanyonValue deriving (Eq, Show)
data Model_obj_op_canyon = CO CanyonOp deriving (Eq, Show)






modal_eval_assign_canyon :: Model_obj_value_canyon -> Model_obj_map_canyon -> Model_obj_map_canyon
modal_eval_assign_canyon (CV v) (CM t _) = (CM t v)

modal_eval_init_canyon :: Model_obj_init_canyon -> Model_obj_map_canyon
modal_eval_init_canyon (CI t v) = (CM t v)


modal_eval_op_canyon :: Model_obj_op_canyon -> Model_obj_value_canyon -> Model_obj_value_canyon -> Model_obj_value_canyon

modal_eval_op_canyon (CO Not) (CV (CL_Bool True)) _ = (CV (CL_Bool False))
modal_eval_op_canyon (CO Not) _ _ = (CV (CL_Bool True))

modal_eval_op_canyon (CO Eq) v1 v2 = (CV (CL_Bool (v1 == v2)))

modal_eval_op_canyon (CO Gr) (CV (CL_Int i1)) (CV (CL_Int i2)) = (CV (CL_Bool (i1 > i2)))

modal_eval_op_canyon (CO Le) (CV (CL_Int i1)) (CV (CL_Int i2)) = (CV (CL_Bool (i1 < i2)))

modal_eval_op_canyon (CO Plus) (CV (CL_Int i1)) (CV (CL_Int i2)) = (CV (CL_Int (i1 + i2)))

modal_eval_op_canyon (CO Concat) (CV (CL_List l1)) (CV (CL_List l2)) = (CV (CL_List (l1 ++ l2)))

modal_eval_op_canyon (CO Append) (CV (CL_List l1)) (CV v) = (CV (CL_List (l1 ++ [v])))

modal_eval_op_canyon (CO Index) (CV (CL_List l)) (CV (CL_Int index)) = (CV (item_at_index (CL_Null) l index))

modal_eval_op_canyon _ _ _ = CV (CL_Null)



modal_eval_branch_canyon :: Model_obj_value_canyon -> Bool
modal_eval_branch_canyon (CV (CL_Bool True)) = True
modal_eval_branch_canyon _ = False

modal_eval_value_canyon :: Model_obj_map_canyon -> Model_obj_value_canyon
modal_eval_value_canyon (CM _ v) = CV v




--	NULL | NOP | SEQ Expr Expr | INIT Model_obj_init TYPE Varname | VALUE Model_obj_value TYPE 
 -- | VAR Varname | ASSIGN Varname Expr | OP Model_obj_op Expr Expr | IF Expr Expr Expr | WHILE Expr Expr 
 -- | EXPR_ERROR String      deriving Show


-----------------------------------------------------------------------------------------------------
-- TEST DRIVER
-----------------------------------------------------------------------------------------------------
--program_test = OP O (OP O ((VALUE O (Type 2))) (VALUE O (Type 6))) (VALUE O (Type 99))

--program_result = exec_core program_test 2

canyon_program = Block (Init 0 C_Char "x" : GetChar 0 "x" : (If 0 (Const 0 (CL_Bool True)) (Jimmy) (Dave)) : [])


--(Const 55 (CL_Int 23))
--canyon_program2 = Block (Dave : (Const 55 (CL_Int 23)) : Dave : [])
--(_, cp3cpo_e) = Block ((If 0 (Const 0 (CL_Bool True)) (Jimmy) (Dave)) : [])
(canyon_program_s, canyon_program_e) = (compile_canyon canyon_program)

main :: IO ()
main = do
    putStrLn ""  
    --putStrLn (show (program_result))
    --putStrLn (show (Block [Init 3 C_Bool "Hello"]))
    --putStrLn (show (compile_canyon canyon_program))
    
    --putStrLn (show canyon_program)
    --putStrLn (show canyon_program_e)
    vvv <- (exec_core canyon_program_e 10000)
    putStrLn (show vvv)
    --putStrLn (show (exec_core canyon_program_e 2))
    --putStrLn (show (exec_core canyon_program_e 3))
    --putStrLn (show (exec_core canyon_program_e 4))
    putStrLn ""








