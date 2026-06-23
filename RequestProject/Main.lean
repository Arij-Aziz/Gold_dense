import Mathlib
import RequestProject.AdditiveEnergy
import RequestProject.Definitions
import RequestProject.ExplicitCounting
import RequestProject.ShortInterval
import RequestProject.EnergyUpperBound
import RequestProject.ResearchLadder
import RequestProject.KappaFactory
import RequestProject.DifferenceSieve
import RequestProject.ConcreteConstants
import RequestProject.MainTheorem
import RequestProject.MinorArc
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
