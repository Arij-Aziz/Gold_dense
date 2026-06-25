import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions
import RequestProject.RestrictedGoldbachDefs
import RequestProject.RestrictedGoldbachCombinatorics
import RequestProject.RestrictedGoldbachMajorArc
import RequestProject.RestrictedGoldbachSingularSeries
import RequestProject.RestrictedGoldbachExceptionalSet
import RequestProject.RestrictedGoldbachMain
import RequestProject.MainTheorem
import RequestProject.Goldbach
import RequestProject.Audit

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
