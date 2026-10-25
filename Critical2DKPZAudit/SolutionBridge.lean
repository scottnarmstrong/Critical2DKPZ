/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZAudit.SolutionBasic
public import Critical2DKPZStatements.CriticalKPZMain

/-! The polymer and local Sobolev definitions in the independent statement agree with those of the library. -/

@[expose] public noncomputable section

namespace Critical2DKPZAudit.Conversion

/-- The square-lattice carriers agree. -/
theorem Site_eq :
    @Critical2DKPZAudit.Site = @Critical2DKPZ.Site := rfl

/-- The four signed coordinate steps agree. -/
theorem srwStep_eq :
    @Critical2DKPZAudit.srwStep = @Critical2DKPZ.srwStep := rfl

/-- The walk-position sums agree. -/
theorem walkPosition_eq :
    @Critical2DKPZAudit.walkPosition = @Critical2DKPZ.walkPosition := rfl

/-- The planar walk transition probabilities agree. -/
theorem srwKernel_eq :
    @Critical2DKPZAudit.srwKernel = @Critical2DKPZ.srwKernel := rfl

/-- The expected walk-overlap sums agree. -/
theorem replicaOverlap_eq :
    @Critical2DKPZAudit.replicaOverlap = @Critical2DKPZ.replicaOverlap := rfl

/-- The critical disorder variances agree. -/
theorem criticalSigmaSq_eq :
    @Critical2DKPZAudit.criticalSigmaSq = @Critical2DKPZ.criticalSigmaSq := rfl

/-- The critical disorder strengths agree. -/
theorem criticalBeta_eq :
    @Critical2DKPZAudit.criticalBeta = @Critical2DKPZ.criticalBeta := rfl

/-- The Gaussian disorder spaces agree. -/
theorem Disorder_eq :
    @Critical2DKPZAudit.Disorder = @Critical2DKPZ.Disorder := rfl

/-- The Gaussian product laws agree. -/
theorem disorderLaw_eq :
    @Critical2DKPZAudit.disorderLaw = @Critical2DKPZ.disorderLaw := rfl

/-- The Gaussian probability-measure instances agree. -/
theorem disorderLaw_isProbabilityMeasure_eq :
    @Critical2DKPZAudit.disorderLaw_isProbabilityMeasure = @Critical2DKPZ.disorderLaw_isProbabilityMeasure := rfl

/-- The Euclidean plane carriers agree. -/
theorem Plane_eq :
    @Critical2DKPZAudit.Plane = @Critical2DKPZ.Plane := rfl

/-- The real distribution spaces agree. -/
theorem Distr_eq :
    @Critical2DKPZAudit.Distr = @Critical2DKPZ.Distr := rfl

/-- The even upper approximations to lattice times agree. -/
theorem evenCeil_eq :
    @Critical2DKPZAudit.evenCeil = @Critical2DKPZ.evenCeil := rfl

/-- The planar heat kernels agree. -/
theorem heatKernel_eq :
    @Critical2DKPZAudit.heatKernel = @Critical2DKPZ.heatKernel := rfl

/-- The stochastic heat-flow pairings agree. -/
theorem shfPairing_eq :
    @Critical2DKPZAudit.shfPairing = @Critical2DKPZ.shfPairing := rfl

/-- The temporally regularized KPZ fields agree. -/
theorem kpzRegularized_eq :
    @Critical2DKPZAudit.kpzRegularized = @Critical2DKPZ.kpzRegularized := rfl

/-- The smooth compactly supported test-function spaces agree. -/
theorem TestFn_eq :
    @Critical2DKPZAudit.TestFn = @Critical2DKPZ.TestFn := rfl

/-- The characterizations of the critical KPZ process agree. -/
theorem IsCriticalKPZ_eq :
    @Critical2DKPZAudit.IsCriticalKPZ = @Critical2DKPZ.IsCriticalKPZ := rfl

/-- The nearest-even rounding functions agree. -/
theorem nearestEven_eq :
    @Critical2DKPZAudit.nearestEven = @Critical2DKPZ.nearestEven := rfl

/-- The rescaled lattice-point representatives agree. -/
theorem latticePoint_eq :
    @Critical2DKPZAudit.latticePoint = @Critical2DKPZ.latticePoint := rfl

/-- The point-to-point polymer partition functions agree. -/
theorem pointToPoint_eq :
    @Critical2DKPZAudit.pointToPoint = @Critical2DKPZ.pointToPoint := rfl

/-- The rescaled point-to-point polymer densities agree. -/
theorem rescaledP2P_eq :
    @Critical2DKPZAudit.rescaledP2P = @Critical2DKPZ.rescaledP2P := rfl

/-- The free-endpoint polymer partition functions agree. -/
theorem pointToPlane_eq :
    @Critical2DKPZAudit.pointToPlane = @Critical2DKPZ.pointToPlane := rfl

/-- The rescaled free-endpoint partition functions agree. -/
theorem rescaledP2Plane_eq :
    @Critical2DKPZAudit.rescaledP2Plane = @Critical2DKPZ.rescaledP2Plane := rfl

/-- The characterizations of the critical stochastic heat flow agree. -/
theorem IsCriticalSHF_eq :
    @Critical2DKPZAudit.IsCriticalSHF = @Critical2DKPZ.IsCriticalSHF := rfl

/-- The lattice centring constants agree. -/
theorem kpzLatticeCentring_eq :
    @Critical2DKPZAudit.kpzLatticeCentring = @Critical2DKPZ.kpzLatticeCentring := rfl

/-- The centred lattice KPZ fields agree. -/
theorem kpzLattice_eq :
    @Critical2DKPZAudit.kpzLattice = @Critical2DKPZ.kpzLattice := rfl

/-- The local negative Sobolev carriers agree. -/
theorem LocNegSobolevTop_eq :
    @Critical2DKPZAudit.LocNegSobolevTop = @Critical2DKPZ.LocNegSobolevTop := rfl

/-- The underlying distribution maps agree. -/
theorem LocNegSobolevTop_toDistr_eq :
    @Critical2DKPZAudit.LocNegSobolevTop.toDistr = @Critical2DKPZ.LocNegSobolevTop.toDistr := rfl

/-- The cosine-modulated test functions agree. -/
theorem TestFn_mulCos_eq :
    @Critical2DKPZAudit.TestFn.mulCos = @Critical2DKPZ.TestFn.mulCos := rfl

/-- The sine-modulated test functions agree. -/
theorem TestFn_mulSin_eq :
    @Critical2DKPZAudit.TestFn.mulSin = @Critical2DKPZ.TestFn.mulSin := rfl

/-- The localized negative Sobolev energies agree. -/
theorem localNegSobolevSq_eq :
    @Critical2DKPZAudit.localNegSobolevSq = @Critical2DKPZ.localNegSobolevSq := rfl

/-- The local negative Sobolev topologies agree. -/
theorem LocNegSobolevTop_topologicalSpace_eq :
    @Critical2DKPZAudit.LocNegSobolevTop.topologicalSpace = @Critical2DKPZ.LocNegSobolevTop.topologicalSpace := rfl

/-- The finite-tuple distribution carriers agree. -/
theorem LocNegSobolevTuple_eq :
    @Critical2DKPZAudit.LocNegSobolevTuple = @Critical2DKPZ.LocNegSobolevTuple := rfl

/-- The finite-tuple local negative Sobolev topologies agree. -/
theorem LocNegSobolevTuple_topologicalSpace_eq :
    @Critical2DKPZAudit.LocNegSobolevTuple.topologicalSpace = @Critical2DKPZ.LocNegSobolevTuple.topologicalSpace := rfl

/-- The finite-tuple Borel sigma-algebras agree. -/
theorem LocNegSobolevTuple_measurableSpace_eq :
    @Critical2DKPZAudit.LocNegSobolevTuple.measurableSpace = @Critical2DKPZ.LocNegSobolevTuple.measurableSpace := rfl

/-- The Borel-space instances for the finite-tuple topologies agree. -/
theorem LocNegSobolevTuple_borelSpace_eq :
    @Critical2DKPZAudit.LocNegSobolevTuple.borelSpace = @Critical2DKPZ.LocNegSobolevTuple.borelSpace := rfl

/-- The local negative Sobolev membership conditions agree. -/
theorem MemLocalNegSobolev_eq :
    @Critical2DKPZAudit.MemLocalNegSobolev = @Critical2DKPZ.MemLocalNegSobolev := rfl

/-- The sigma-algebras generated by the stochastic heat flow agree. -/
theorem shfSigma_eq :
    @Critical2DKPZAudit.shfSigma = @Critical2DKPZ.shfSigma := rfl

/-- The embeddings of finite distribution tuples into their local Sobolev carriers agree. -/
theorem toLocNegSobolevTuple_eq :
    @Critical2DKPZAudit.toLocNegSobolevTuple = @Critical2DKPZ.toLocNegSobolevTuple := rfl

end Critical2DKPZAudit.Conversion
