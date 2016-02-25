module Coercion where

import {-# SOURCE #-} TyCoRep
import {-# SOURCE #-} TyCon

import CoAxiom
import Var
import Outputable

{-
mkTyConAppCo :: Role -> TyCon -> [Coercion] -> Coercion
mkAppCo :: Coercion -> Coercion -> Coercion
mkForAllCo :: TyVar -> Coercion -> Coercion -> Coercion
mkAxiomInstCo :: CoAxiom Branched -> BranchIndex -> [Coercion] -> Coercion
mkPhantomCo :: Coercion -> Type -> Type -> Coercion
mkUnsafeCo :: Role -> Type -> Type -> Coercion
mkUnivCo :: UnivCoProvenance -> Role -> Type -> Type -> Coercion
mkNthCo :: Int -> Coercion -> Coercion
mkLRCo :: LeftOrRight -> Coercion -> Coercion
mkInstCo :: Coercion -> Coercion -> Coercion
mkCoherenceCo :: Coercion -> Coercion -> Coercion
mkKindCo :: Coercion -> Coercion
mkSubRoleCo :: Role -> Coercion -> Coercion
mkProofIrrelCo :: Role -> Coercion -> Coercion -> Coercion -> Coercion


coVarRole :: CoVar -> Role


data LiftingContext
liftCoSubst :: Role -> LiftingContext -> Type -> Coercion

-}

mkReflCo :: Role -> Type -> Coercion
mkCoVarCo :: CoVar -> Coercion
mkSymCo :: Coercion -> Coercion
mkTransCo :: Coercion -> Coercion -> Coercion

mkFunCos :: Role -> [Coercion] -> Coercion -> Coercion

isReflCo :: Coercion -> Bool
isReflexiveCo :: Coercion -> Bool

coVarKindsTypesRole :: CoVar -> (Kind, Kind, Type, Type, Role)
mkCoercionType :: Role -> Type -> Type -> Type

tyConRolesX :: Role -> TyCon -> [Role]
tyConRolesRepresentational :: TyCon -> [Role]
nthRole :: Role -> TyCon -> Int -> Role

coercionSize :: Coercion -> Int
coercionType :: Coercion -> Type
seqCo :: Coercion -> ()

pprCo :: Coercion -> SDoc
pprCoRep :: CoercionRep -> SDoc
