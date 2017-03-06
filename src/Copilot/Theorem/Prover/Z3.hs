--------------------------------------------------------------------------------

{-# LANGUAGE LambdaCase, NamedFieldPuns, FlexibleInstances, RankNTypes, GADTs,
    MultiParamTypeClasses, FlexibleContexts, DataKinds #-}
{-# LANGUAGE Trustworthy #-}

module Copilot.Theorem.Prover.Z3
  ( module Data.Default
  , Options (..)
  , induction, kInduction, onlySat, onlyValidity
  )
where

import Copilot.Theorem.IL.Translate
import Copilot.Theorem.Prove (Output (..), check, Proof, Universal, Existential)
import Copilot.Theorem.IL as IL
import qualified Copilot.Theorem.Prove as P

import Control.Monad (msum, mzero, when, void, unless)
import Control.Monad.State (StateT, runStateT, get, modify)
import Control.Monad.Trans.Maybe (MaybeT (..))

import Data.Word
import Data.Maybe (fromJust, fromMaybe)
import Data.Default (Default(..))
import Data.List (foldl')

import Data.Set (Set, (\\), union)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Language.SMTLib2 as SMT
import Language.SMTLib2.Pipe
import Language.SMTLib2.Strategy
import Language.SMTLib2.Debug

import Language.SMTLib2.Pipe.Internals hiding (Var, vars)

import System.Console.ANSI
import System.IO
import Control.Monad.Trans

--------------------------------------------------------------------------------

-- | Tactics

data Options = Options
  { nraNLSat :: Bool
  , startK   :: Word32
  -- The maximum number of steps of the k-induction algorithm the prover runs
  -- before giving up.
  , maxK     :: Word32

  -- If `debug` is set to `True`, the SMTLib/TPTP queries produced by the
  -- prover are displayed in the standard output.
  , debug    :: Bool
  }

instance Default Options where
  def = Options
    { nraNLSat = True
    , startK = 0
    , maxK   = 10
    , debug  = False
    }

onlySat :: Options -> Proof Existential
onlySat opts = check P.Prover
  { P.proverName  = "OnlySat"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = onlySat'
  , P.closeProver = const $ return ()
  }

onlyValidity :: Options -> Proof Universal
onlyValidity opts = check P.Prover
  { P.proverName  = "OnlyValidity"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = onlyValidity'
  , P.closeProver = const $ return ()
  }

induction :: Options -> Proof Universal
induction opts = check P.Prover
  { P.proverName  = "Induction"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = kInduction' 0 0
  , P.closeProver = const $ return ()
  }

kInduction :: Options -> Proof Universal
kInduction opts = check P.Prover
  { P.proverName  = "K-Induction"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = kInduction' (startK opts) (maxK opts)
  , P.closeProver = const $ return ()
  }

-------------------------------------------------------------------------------

-- | Checks the Copilot specification with k-induction

type Solver = DebugBackend SMTPipe

type ProofScript = MaybeT (StateT ProofState IO)

runPS :: ProofScript a -> ProofState -> IO (Maybe a, ProofState)
runPS ps = runStateT (runMaybeT ps)

data ProofState = ProofState
  { options  :: Options
  , solvers  :: Map SolverId Solver
  , vars     :: Map SolverId TransState
  , assumps  :: Map SolverId (Set IL.Expr)
  , spec     :: IL
  }

data SolverId = Base | Step
  deriving (Show, Ord, Eq)

getModels :: [PropId] -> [PropId] -> ProofScript ([IL.Expr], [IL.Expr], [IL.Expr], [IL.Expr], Bool)
getModels assumptionIds toCheckIds = do
  IL {modelInit, modelRec, properties, inductive} <- spec <$> get
  let (as, as')       = selectProps assumptionIds properties
      (as'', toCheck) = selectProps toCheckIds properties
  return (as ++ as', modelInit, modelRec ++ as ++ as' ++ as'', toCheck, inductive)

getSolver :: SolverId -> ProofScript Solver
getSolver sid = do
  solvers <- solvers <$> get
  case Map.lookup sid solvers of
    Nothing -> startNewSolver sid
    Just solver -> return solver

setSolver :: SolverId -> Solver -> ProofScript ()
setSolver sid solver =
  (lift . modify) $ \s -> s { solvers = Map.insert sid solver (solvers s) }

getVars :: SolverId -> ProofScript TransState
getVars sid = do
  vars <- vars <$> get
  return $ case Map.lookup sid vars of
    Nothing -> noVars
    Just vs -> vs

setVars :: SolverId -> TransState -> ProofScript ()
setVars sid vs =
  (lift . modify) $ \s -> s { vars = Map.insert sid vs (vars s) }

newAssumps :: SolverId -> [IL.Expr] -> ProofScript [IL.Expr]
newAssumps sid as' = do
  assumps <- assumps <$> get
  case Map.lookup sid assumps of
    Nothing -> do
      modify $ \s -> s { assumps = Map.insert sid (Set.fromList as') assumps }
      return as'
    Just as -> do
      let as'' = (Set.fromList as') `union` as
      modify $ \s -> s { assumps = Map.insert sid as'' assumps }
      return $ Set.elems $ (Set.fromList as') \\ as

deleteSolver :: SolverId -> ProofScript ()
deleteSolver sid =
  (lift . modify) $ \s -> s { solvers = Map.delete sid (solvers s) }

startNewSolver :: SolverId -> ProofScript Solver
startNewSolver sid = do
  pipe <- liftIO $ createPipe "z3" ["-smt2", "-in"]
  dbg <- (options <$> get >>= return . debug)
  s <- liftIO $ namedDebugBackend (show sid) (not dbg) pipe
  setSolver sid s
  return s

stop :: SolverId -> ProofScript ()
stop sid = do
  s <- getSolver sid
  deleteSolver sid
  -- liftIO $ close s

stopSolvers :: ProofScript ()
stopSolvers = do
  solvers <- solvers <$> get
  mapM_ stop (fst <$> Map.toList solvers)

proofKind :: Integer -> String
proofKind 0 = "induction"
proofKind k = "k-induction (k = " ++ show k ++ ")"

entailment :: SolverId -> [IL.Expr] -> [IL.Expr] -> ProofScript CheckSatResult
entailment sid assumptions props = do
  s <- getSolver sid
  liftIO $ withBackendExitCleanly s $ setOption (ProduceModels True)
  -- liftIO $ withBackendExitCleanly s $ setOption (ProduceProofs True)
  -- liftIO $ withBackendExitCleanly s $ setOption (ProduceUnsatCores True)
  vs <- getVars sid
  assumps' <- newAssumps sid assumptions
  (_, vs')  <- liftIO $ withBackendExitCleanly s $ runStateT (mapM_ (\e -> transB e >>= lift . assert) assumps') vs
  setVars sid vs'
  liftIO $ withBackendExitCleanly s $ push
  _ <- liftIO $ withBackendExitCleanly s $ runStateT
    (transB (bsimpl (foldl' (Op2 Bool IL.Or) (ConstB False) $ map (Op1 Bool IL.Not) props)) >>= lift . assert) vs'

  nraNL <- (options <$> get >>= return . nraNLSat)
  res <- if nraNL
    then liftIO $ withBackendExitCleanly s $ checkSat (Just (UsingParams (CustomTactic "qfnra-nlsat") []))
         (CheckSatLimits (Just 5000) Nothing)
    else liftIO $ withBackendExitCleanly s $ checkSat Nothing (CheckSatLimits (Just 5000) Nothing)

  when (res == Sat) $ void $ liftIO $ withBackendExitCleanly s $ getModel
  -- when (res == Unsat) $ void $ liftIO $ withBackendExitCleanly s $ getProof
  liftIO $ withBackendExitCleanly s $ pop
  -- liftIO $ print model
  return res

unknown :: ProofScript a
unknown = mzero

unknown' :: String -> ProofScript Output
unknown' msg = return $ Output P.Unknown [msg]

invalid :: String -> ProofScript Output
invalid msg = return $ Output P.Invalid [msg]

sat :: String -> ProofScript Output
sat msg = return $ Output P.Sat [msg]

valid :: String -> ProofScript Output
valid msg = return $ Output P.Valid [msg]

kInduction' :: Word32 -> Word32 -> ProofState -> [PropId] -> [PropId] -> IO Output
kInduction' startK maxK s as ps = (fromMaybe (Output P.Unknown ["proof by " ++ proofKind (toInteger maxK) ++ " failed"]) . fst)
  <$> runPS (msum (map induction [(toInteger startK) .. (toInteger maxK)]) <* stopSolvers) s
  where
    induction k = do
      (assumps, modelInit, modelRec, toCheck, inductive) <- getModels as ps

      let base    = [evalAt (Fixed i) m | m <- modelRec, i <- [0 .. k]]
          baseInv = [evalAt (Fixed k) m | m <- toCheck]

      let step    = [evalAt (_n_plus i) m | m <- modelRec, i <- [0 .. k + 1]]
                    ++ [evalAt (_n_plus i) m | m <- toCheck, i <- [0 .. k]]
          stepInv = [evalAt (_n_plus $ k + 1) m | m <- toCheck]

      entailment Base assumps [ConstB False] >>= \case
        Unknown -> unknown
        Unsat   -> invalid $ "inconsistent assumptions"
        Sat     -> entailment Base (modelInit ++ base) baseInv >>= \case
          Sat     -> invalid $ "base case failed for " ++ proofKind k
          Unknown -> unknown
          Unsat   ->
            if not inductive then valid ("proved without induction")
            else entailment Step step stepInv >>= \case
              Sat     -> unknown
              Unknown -> unknown
              Unsat   -> valid $ "proved with " ++ proofKind k

onlySat' :: ProofState -> [PropId] -> [PropId] -> IO Output
onlySat' s as ps = (fromJust . fst) <$> runPS (script <* stopSolvers) s
  where
    script  = do
      (assumps, modelInit, modelRec, toCheck, inductive) <- getModels as ps

      let base    = map (evalAt (Fixed 0)) modelRec
          baseInv = map (evalAt (Fixed 0)) toCheck

      entailment Base assumps [ConstB False] >>= \case
        Unknown -> unknown
        Unsat   -> invalid $ "inconsistent assumptions"
        Sat     -> if inductive
          then unknown' "proposition requires induction to prove."
          else entailment Base (modelInit ++ base) (map (Op1 Bool IL.Not) baseInv) >>= \case
            Unsat   -> invalid "prop not satisfiable"
            Unknown -> unknown' "failed to find a satisfying model"
            Sat     -> sat "prop is satisfiable"

onlyValidity' :: ProofState -> [PropId] -> [PropId] -> IO Output
onlyValidity' s as ps = (fromJust . fst) <$> runPS (script <* stopSolvers) s
  where
    script  = do
      (assumps, modelInit, modelRec, toCheck, inductive) <- getModels as ps

      let base    = map (evalAt (Fixed 0)) modelRec
          baseInv = map (evalAt (Fixed 0)) toCheck

      entailment Base assumps [ConstB False] >>= \case
        Unknown -> unknown
        Unsat   -> invalid $ "inconsistent assumptions"
        Sat     -> if inductive
          then unknown' "proposition requires induction to prove."
          else entailment Base (modelInit ++ base) baseInv >>= \case
            Unsat   -> valid "proof by Z3"
            Unknown -> unknown
            Sat     -> invalid "Z3 found a counter-example."

selectProps :: [PropId] -> Map PropId ([IL.Expr], IL.Expr) -> ([IL.Expr], [IL.Expr])
selectProps propIds properties =
  (squash . unzip) [(as, p) | (id, (as, p)) <- Map.toList properties, id `elem` propIds]
    where squash (a, b) = (concat a, b)

--------------------------------------------------------------------------------

-- | This is all very ugly. It might make better sense to go straight from Core to SMT.Expr, or maybe use SBV instead.

type Trans = StateT TransState (SMT Solver)

data TransState = TransState
  { boolVars :: Map String (SMT.Expr Solver BoolType)
  , bv8Vars  :: Map String (SMT.Expr Solver (BitVecType 8))
  , bv16Vars :: Map String (SMT.Expr Solver (BitVecType 16))
  , bv32Vars :: Map String (SMT.Expr Solver (BitVecType 32))
  , bv64Vars :: Map String (SMT.Expr Solver (BitVecType 64))
  , realVars  :: Map String (SMT.Expr Solver RealType)
  }

noVars :: TransState
noVars = TransState Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

getBoolVar :: String -> Trans (SMT.Expr Solver BoolType)
getBoolVar = getVar bool boolVars (\v s -> s {boolVars  = v})

getBV8Var  :: String -> Trans (SMT.Expr Solver (BitVecType 8))
getBV8Var  = getVar (bitvec 8) bv8Vars  (\v s -> s {bv8Vars  = v})

getBV16Var :: String -> Trans (SMT.Expr Solver (BitVecType 16))
getBV16Var = getVar (bitvec 16) bv16Vars (\v s -> s {bv16Vars = v})

getBV32Var :: String -> Trans (SMT.Expr Solver (BitVecType 32))
getBV32Var = getVar (bitvec 32) bv32Vars (\v s -> s {bv32Vars = v})

getBV64Var :: String -> Trans (SMT.Expr Solver (BitVecType 64))
getBV64Var = getVar (bitvec 64) bv64Vars (\v s -> s {bv64Vars = v})

getRealVar  :: String -> Trans (SMT.Expr Solver RealType)
getRealVar  = getVar real realVars (\v s -> s {realVars  = v})

--getVar :: (Unit (SMTAnnotation t), SMTType t) => (TransState -> Map String (SMT.Expr Solver t)) -> (Map String (SMT.Expr Solver t) -> TransState -> TransState) -> String -> Trans (SMT.Expr Solver t)
getVar t proj upd v = do
  vs <- proj <$> get
  case Map.lookup v vs of
    Nothing -> do
      newVar <- lift $ declareVarNamed t v
      modify $ upd $ Map.insert v newVar vs
      return newVar
    Just x -> return x

transB :: IL.Expr -> Trans (SMT.Expr Solver BoolType)
transB = \case
  ConstB b           -> return $ constant b
  Ite _ c e1 e2      -> ite <$> transB c <*> transB e1 <*> transB e2
  Op1 _ IL.Not e     -> not' <$> transB e
  Op2 _ IL.And e1 e2 -> (.&.) <$> transB e1 <*> transB e2
  Op2 _ IL.Or e1 e2  -> (.|.) <$> transB e1 <*> transB e2
  Op2 _ IL.Eq e1 e2  -> case typeOf e1 of
    Bool   -> (.==.) <$> transB e1    <*> transB e2
    Real   -> (.==.) <$> transR e1    <*> transR e2
    BV8    -> (.==.) <$> transBV8 e1  <*> transBV8 e2
    BV16   -> (.==.) <$> transBV16 e1 <*> transBV16 e2
    BV32   -> (.==.) <$> transBV32 e1 <*> transBV32 e2
    BV64   -> (.==.) <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> (.==.) <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> (.==.) <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> (.==.) <$> transBV32 e1 <*> transBV32 e2
    SBV64  -> (.==.) <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Le e1 e2) -> case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> (.<=.) <$> transR e1    <*> transR e2
    BV8    -> bvule  <$> transBV8 e1  <*> transBV8 e2
    BV16   -> bvule  <$> transBV16 e1 <*> transBV16 e2
    BV32   -> bvule  <$> transBV32 e1 <*> transBV32 e2
    BV64   -> bvule  <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> bvule  <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> bvule  <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> bvule  <$> transBV32 e1 <*> transBV32 e2
    SBV64  -> bvule  <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Ge e1 e2) -> case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> (.>=.) <$> transR e1    <*> transR e2
    BV8    -> bvuge  <$> transBV8 e1  <*> transBV8 e2
    BV16   -> bvuge  <$> transBV16 e1 <*> transBV16 e2
    BV32   -> bvuge  <$> transBV32 e1 <*> transBV32 e2
    BV64   -> bvuge  <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> bvuge  <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> bvuge  <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> bvuge  <$> transBV32 e1 <*> transBV32 e2
    SBV64  -> bvuge  <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Lt e1 e2) -> case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> (.<.) <$> transR e1    <*> transR e2
    BV8    -> bvult <$> transBV8 e1  <*> transBV8 e2
    BV16   -> bvult <$> transBV16 e1 <*> transBV16 e2
    BV32   -> bvult <$> transBV32 e1 <*> transBV32 e2
    BV64   -> bvult <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> bvult <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> bvult <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> bvult <$> transBV32 e1 <*> transBV32 e2
    SBV64  -> bvult <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Gt e1 e2) -> case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> (.>.) <$> transR e1    <*> transR e2
    BV8    -> bvugt <$> transBV8 e1  <*> transBV8 e2
    BV16   -> bvugt <$> transBV16 e1 <*> transBV16 e2
    BV32   -> bvugt <$> transBV32 e1 <*> transBV32 e2
    BV64   -> bvugt <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> bvugt <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> bvugt <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> bvugt <$> transBV32 e1 <*> transBV32 e2
    SBV64  -> bvugt <$> transBV64 e1 <*> transBV64 e2
  SVal _ s i         -> getBoolVar $ ncVar s i
  e                  -> error $ "Encountered unhandled expression (Bool): " ++ show e

ncVar :: [Char] -> SeqIndex -> [Char]
ncVar s (Fixed i) = s ++ "_" ++ show i
ncVar s (Var   i) = s ++ "_n" ++ show i

transR :: IL.Expr -> Trans (SMT.Expr Solver RealType)
transR = \case
  ConstR n         -> return $ constant $ toRational n
  Ite _ c e1 e2    -> ite <$> transB c <*> transR e1 <*> transR e2

  Op1 _ IL.Neg e   -> app neg <$> transR e
  Op1 _ IL.Abs e   -> app SMT.Abs <$> transR e

  Op2 _ Add e1 e2  -> (\x y -> app plus [x, y]) <$> transR e1 <*> transR e2
  Op2 _ Sub e1 e2  -> (\x y -> app minus (x, y)) <$> transR e1 <*> transR e2
  Op2 _ Mul e1 e2  -> (\x y -> app mult [x, y]) <$> transR e1 <*> transR e2
  Op2 _ Fdiv e1 e2 -> SMT.Div <$> transR e1 <*> transR e2

  Op2 _ Pow e1 e2  -> do
    -- let pow = SMTBuiltIn "^" () :: SMTFunction (SMT.Expr Solver Rational, SMT.Expr Solver Rational) Rational
    let pow = undefined -- TODO(chathhorn)
    (\x y -> app pow (x, y)) <$> transR e1 <*> transR e2

  SVal _ s i       -> getRealVar $ ncVar s i
  e                -> error $ "Encountered unhandled expression (Rat): " ++ show e

-- TODO(chathhorn): bleghh
transBV8 :: IL.Expr -> Trans (SMT.Expr Solver (BitVecType 8))
transBV8 = \case
  ConstI _ n      -> return $ constant $ bitvec n
  Ite _ c e1 e2   -> ite <$> transB c <*> transBV8 e1 <*> transBV8 e2
  Op1 _ IL.Abs e  -> abs <$> transBV8 e
  Op1 _ IL.Neg e  -> negate <$> transBV8 e
  Op2 _ Add e1 e2 -> (+) <$> transBV8 e1 <*> transBV8 e2
  Op2 _ Sub e1 e2 -> (-) <$> transBV8 e1 <*> transBV8 e2
  Op2 _ Mul e1 e2 -> (*) <$> transBV8 e1 <*> transBV8 e2
  SVal _ s i      -> getBV8Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV8): " ++ show e

transBV16 :: IL.Expr -> Trans (SMT.Expr Solver (BitVecType 16))
transBV16 = \case
  ConstI _ n      -> return $ constant $ bitvec n
  Ite _ c e1 e2   -> ite <$> transB c <*> transBV16 e1 <*> transBV16 e2
  Op1 _ IL.Abs e  -> abs <$> transBV16 e
  Op1 _ IL.Neg e  -> negate <$> transBV16 e
  Op2 _ Add e1 e2 -> (+) <$> transBV16 e1 <*> transBV16 e2
  Op2 _ Sub e1 e2 -> (-) <$> transBV16 e1 <*> transBV16 e2
  Op2 _ Mul e1 e2 -> (*) <$> transBV16 e1 <*> transBV16 e2
  SVal _ s i      -> getBV16Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV16): " ++ show e

transBV32 :: IL.Expr -> Trans (SMT.Expr Solver (BitVecType 32))
transBV32 = \case
  ConstI _ n      -> return $ constant $ bitvec n
  Ite _ c e1 e2   -> ite <$> transB c <*> transBV32 e1 <*> transBV32 e2
  Op1 _ IL.Abs e  -> abs <$> transBV32 e
  Op1 _ IL.Neg e  -> negate <$> transBV32 e
  Op2 _ Add e1 e2 -> (+) <$> transBV32 e1 <*> transBV32 e2
  Op2 _ Sub e1 e2 -> (-) <$> transBV32 e1 <*> transBV32 e2
  Op2 _ Mul e1 e2 -> (*) <$> transBV32 e1 <*> transBV32 e2
  SVal _ s i      -> getBV32Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV32): " ++ show e

transBV64 :: IL.Expr -> Trans (SMT.Expr Solver (BitVecType 64))
transBV64 = \case
  ConstI _ n      -> return $ constant $ bitvec n
  Ite _ c e1 e2   -> ite <$> transB c <*> transBV64 e1 <*> transBV64 e2
  Op1 _ IL.Abs e  -> abs <$> transBV64 e
  Op1 _ IL.Neg e  -> negate <$> transBV64 e
  Op2 _ Add e1 e2 -> (+) <$> transBV64 e1 <*> transBV64 e2
  Op2 _ Sub e1 e2 -> (-) <$> transBV64 e1 <*> transBV64 e2
  Op2 _ Mul e1 e2 -> (*) <$> transBV64 e1 <*> transBV64 e2
  SVal _ s i      -> getBV64Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV64): " ++ show e
