/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZAudit.FourResults.SolutionBasic
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.CriticalSigmaSq
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.KpzLattice
public import Critical2DKPZ.Definitions.KpzLatticeCentring
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.LatticePoint
public import Critical2DKPZ.Definitions.LocNegSobolevTop
public import Critical2DKPZ.Definitions.LocNegSobolevTopToDistr
public import Critical2DKPZ.Definitions.LocNegSobolevTopTopologicalSpace
public import Critical2DKPZ.Definitions.LocNegSobolevTuple
public import Critical2DKPZ.Definitions.LocNegSobolevTupleBorelSpace
public import Critical2DKPZ.Definitions.LocNegSobolevTupleMeasurableSpace
public import Critical2DKPZ.Definitions.LocNegSobolevTupleTopologicalSpace
public import Critical2DKPZ.Definitions.LocalNegSobolevSq
public import Critical2DKPZ.Definitions.MemLocalNegSobolev
public import Critical2DKPZ.Definitions.NearestEven
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.PointToPlane
public import Critical2DKPZ.Definitions.PointToPoint
public import Critical2DKPZ.Definitions.ReplicaOverlap
public import Critical2DKPZ.Definitions.RescaledP2P
public import Critical2DKPZ.Definitions.RescaledP2Plane
public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Definitions.ShfSigma
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.SrwKernel
public import Critical2DKPZ.Definitions.SrwStep
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Definitions.TestFnMulCos
public import Critical2DKPZ.Definitions.TestFnMulSin
public import Critical2DKPZ.Definitions.ToLocNegSobolevTuple
public import Critical2DKPZ.Definitions.WalkPosition
public import Critical2DKPZ.Extensions.Definitions.ResponseCutoff
public import Critical2DKPZ.Extensions.Definitions.RestrictJet
public import Critical2DKPZ.Extensions.Definitions.ScaleInterval
public import Critical2DKPZ.Extensions.Definitions.ScalePath
public import Critical2DKPZ.Extensions.Definitions.ScaleRadius
public import Critical2DKPZ.Extensions.Definitions.ScaledPairing
public import Critical2DKPZ.Extensions.Definitions.IsWienerLaw
public import Critical2DKPZ.Extensions.Definitions.LogCovariance
public import Critical2DKPZ.Extensions.Definitions.IsFiniteGffLaw

/-! The definitions for Theorems A–D agree with their library counterparts by definitional equality. -/

@[expose] public noncomputable section

namespace Critical2DKPZAudit.FourResults.Conversion

/-- The two definitions of `Site` agree. -/
theorem Site_eq :
    @Critical2DKPZAudit.FourResults.Site = @Critical2DKPZ.Site := rfl

/-- The two definitions of `srwStep` agree. -/
theorem srwStep_eq :
    @Critical2DKPZAudit.FourResults.srwStep = @Critical2DKPZ.srwStep := rfl

/-- The two definitions of `walkPosition` agree. -/
theorem walkPosition_eq :
    @Critical2DKPZAudit.FourResults.walkPosition = @Critical2DKPZ.walkPosition := rfl

/-- The two definitions of `srwKernel` agree. -/
theorem srwKernel_eq :
    @Critical2DKPZAudit.FourResults.srwKernel = @Critical2DKPZ.srwKernel := rfl

/-- The two definitions of `replicaOverlap` agree. -/
theorem replicaOverlap_eq :
    @Critical2DKPZAudit.FourResults.replicaOverlap = @Critical2DKPZ.replicaOverlap := rfl

/-- The two definitions of `criticalSigmaSq` agree. -/
theorem criticalSigmaSq_eq :
    @Critical2DKPZAudit.FourResults.criticalSigmaSq = @Critical2DKPZ.criticalSigmaSq := rfl

/-- The two definitions of `criticalBeta` agree. -/
theorem criticalBeta_eq :
    @Critical2DKPZAudit.FourResults.criticalBeta = @Critical2DKPZ.criticalBeta := rfl

/-- The two definitions of `Disorder` agree. -/
theorem Disorder_eq :
    @Critical2DKPZAudit.FourResults.Disorder = @Critical2DKPZ.Disorder := rfl

/-- The two definitions of `disorderLaw` agree. -/
theorem disorderLaw_eq :
    @Critical2DKPZAudit.FourResults.disorderLaw = @Critical2DKPZ.disorderLaw := rfl

/-- The two definitions of `disorderLaw_isProbabilityMeasure` agree. -/
theorem disorderLaw_isProbabilityMeasure_eq :
    @Critical2DKPZAudit.FourResults.disorderLaw_isProbabilityMeasure = @Critical2DKPZ.disorderLaw_isProbabilityMeasure := rfl

/-- The two definitions of `Plane` agree. -/
theorem Plane_eq :
    @Critical2DKPZAudit.FourResults.Plane = @Critical2DKPZ.Plane := rfl

/-- The two definitions of `Distr` agree. -/
theorem Distr_eq :
    @Critical2DKPZAudit.FourResults.Distr = @Critical2DKPZ.Distr := rfl

/-- The two definitions of `evenCeil` agree. -/
theorem evenCeil_eq :
    @Critical2DKPZAudit.FourResults.evenCeil = @Critical2DKPZ.evenCeil := rfl

/-- The two definitions of `heatKernel` agree. -/
theorem heatKernel_eq :
    @Critical2DKPZAudit.FourResults.heatKernel = @Critical2DKPZ.heatKernel := rfl

/-- The two definitions of `shfPairing` agree. -/
theorem shfPairing_eq :
    @Critical2DKPZAudit.FourResults.shfPairing = @Critical2DKPZ.shfPairing := rfl

/-- The two definitions of `kpzRegularized` agree. -/
theorem kpzRegularized_eq :
    @Critical2DKPZAudit.FourResults.kpzRegularized = @Critical2DKPZ.kpzRegularized := rfl

/-- The two definitions of `TestFn` agree. -/
theorem TestFn_eq :
    @Critical2DKPZAudit.FourResults.TestFn = @Critical2DKPZ.TestFn := rfl

/-- The two definitions of `IsCriticalKPZ` agree. -/
theorem IsCriticalKPZ_eq :
    @Critical2DKPZAudit.FourResults.IsCriticalKPZ = @Critical2DKPZ.IsCriticalKPZ := rfl

/-- The two definitions of `nearestEven` agree. -/
theorem nearestEven_eq :
    @Critical2DKPZAudit.FourResults.nearestEven = @Critical2DKPZ.nearestEven := rfl

/-- The two definitions of `latticePoint` agree. -/
theorem latticePoint_eq :
    @Critical2DKPZAudit.FourResults.latticePoint = @Critical2DKPZ.latticePoint := rfl

/-- The two definitions of `pointToPoint` agree. -/
theorem pointToPoint_eq :
    @Critical2DKPZAudit.FourResults.pointToPoint = @Critical2DKPZ.pointToPoint := rfl

/-- The two definitions of `rescaledP2P` agree. -/
theorem rescaledP2P_eq :
    @Critical2DKPZAudit.FourResults.rescaledP2P = @Critical2DKPZ.rescaledP2P := rfl

/-- The two definitions of `pointToPlane` agree. -/
theorem pointToPlane_eq :
    @Critical2DKPZAudit.FourResults.pointToPlane = @Critical2DKPZ.pointToPlane := rfl

/-- The two definitions of `rescaledP2Plane` agree. -/
theorem rescaledP2Plane_eq :
    @Critical2DKPZAudit.FourResults.rescaledP2Plane = @Critical2DKPZ.rescaledP2Plane := rfl

/-- The two definitions of `IsCriticalSHF` agree. -/
theorem IsCriticalSHF_eq :
    @Critical2DKPZAudit.FourResults.IsCriticalSHF = @Critical2DKPZ.IsCriticalSHF := rfl

/-- The two definitions of `kpzLatticeCentring` agree. -/
theorem kpzLatticeCentring_eq :
    @Critical2DKPZAudit.FourResults.kpzLatticeCentring = @Critical2DKPZ.kpzLatticeCentring := rfl

/-- The two definitions of `kpzLattice` agree. -/
theorem kpzLattice_eq :
    @Critical2DKPZAudit.FourResults.kpzLattice = @Critical2DKPZ.kpzLattice := rfl

/-- The two definitions of `LocNegSobolevTop` agree. -/
theorem LocNegSobolevTop_eq :
    @Critical2DKPZAudit.FourResults.LocNegSobolevTop = @Critical2DKPZ.LocNegSobolevTop := rfl

/-- The two definitions of `LocNegSobolevTop.toDistr` agree. -/
theorem LocNegSobolevTop_toDistr_eq :
    @Critical2DKPZAudit.FourResults.LocNegSobolevTop.toDistr = @Critical2DKPZ.LocNegSobolevTop.toDistr := rfl

/-- The two definitions of `TestFn.mulCos` agree. -/
theorem TestFn_mulCos_eq :
    @Critical2DKPZAudit.FourResults.TestFn.mulCos = @Critical2DKPZ.TestFn.mulCos := rfl

/-- The two definitions of `TestFn.mulSin` agree. -/
theorem TestFn_mulSin_eq :
    @Critical2DKPZAudit.FourResults.TestFn.mulSin = @Critical2DKPZ.TestFn.mulSin := rfl

/-- The two definitions of `localNegSobolevSq` agree. -/
theorem localNegSobolevSq_eq :
    @Critical2DKPZAudit.FourResults.localNegSobolevSq = @Critical2DKPZ.localNegSobolevSq := rfl

/-- The two definitions of `LocNegSobolevTop.topologicalSpace` agree. -/
theorem LocNegSobolevTop_topologicalSpace_eq :
    @Critical2DKPZAudit.FourResults.LocNegSobolevTop.topologicalSpace = @Critical2DKPZ.LocNegSobolevTop.topologicalSpace := rfl

/-- The two definitions of `LocNegSobolevTuple` agree. -/
theorem LocNegSobolevTuple_eq :
    @Critical2DKPZAudit.FourResults.LocNegSobolevTuple = @Critical2DKPZ.LocNegSobolevTuple := rfl

/-- The two definitions of `LocNegSobolevTuple.topologicalSpace` agree. -/
theorem LocNegSobolevTuple_topologicalSpace_eq :
    @Critical2DKPZAudit.FourResults.LocNegSobolevTuple.topologicalSpace = @Critical2DKPZ.LocNegSobolevTuple.topologicalSpace := rfl

/-- The two definitions of `LocNegSobolevTuple.measurableSpace` agree. -/
theorem LocNegSobolevTuple_measurableSpace_eq :
    @Critical2DKPZAudit.FourResults.LocNegSobolevTuple.measurableSpace = @Critical2DKPZ.LocNegSobolevTuple.measurableSpace := rfl

/-- The two definitions of `LocNegSobolevTuple.borelSpace` agree. -/
theorem LocNegSobolevTuple_borelSpace_eq :
    @Critical2DKPZAudit.FourResults.LocNegSobolevTuple.borelSpace = @Critical2DKPZ.LocNegSobolevTuple.borelSpace := rfl

/-- The two definitions of `MemLocalNegSobolev` agree. -/
theorem MemLocalNegSobolev_eq :
    @Critical2DKPZAudit.FourResults.MemLocalNegSobolev = @Critical2DKPZ.MemLocalNegSobolev := rfl

/-- The two definitions of `shfSigma` agree. -/
theorem shfSigma_eq :
    @Critical2DKPZAudit.FourResults.shfSigma = @Critical2DKPZ.shfSigma := rfl

/-- The two definitions of `toLocNegSobolevTuple` agree. -/
theorem toLocNegSobolevTuple_eq :
    @Critical2DKPZAudit.FourResults.toLocNegSobolevTuple = @Critical2DKPZ.toLocNegSobolevTuple := rfl

/-- The two definitions of `TestFn.dilate` agree. -/
theorem TestFn_dilate_eq :
    @Critical2DKPZAudit.FourResults.TestFn.dilate = @Critical2DKPZ.TestFn.dilate := rfl

/-- The two definitions of `Extensions.responseCutoff` agree. -/
theorem Extensions_responseCutoff_eq :
    @Critical2DKPZAudit.FourResults.Extensions.responseCutoff = @Critical2DKPZ.Extensions.responseCutoff := rfl

/-- The two definitions of `Extensions.restrictJet` agree. -/
theorem Extensions_restrictJet_eq :
    @Critical2DKPZAudit.FourResults.Extensions.restrictJet = @Critical2DKPZ.Extensions.restrictJet := rfl

/-- The two definitions of `Extensions.ScaleInterval` agree. -/
theorem Extensions_ScaleInterval_eq :
    @Critical2DKPZAudit.FourResults.Extensions.ScaleInterval = @Critical2DKPZ.Extensions.ScaleInterval := rfl

/-- The two definitions of `Extensions.ScalePath` agree. -/
theorem Extensions_ScalePath_eq :
    @Critical2DKPZAudit.FourResults.Extensions.ScalePath = @Critical2DKPZ.Extensions.ScalePath := rfl

/-- The two definitions of `Extensions.scaleRadius` agree. -/
theorem Extensions_scaleRadius_eq :
    @Critical2DKPZAudit.FourResults.Extensions.scaleRadius = @Critical2DKPZ.Extensions.scaleRadius := rfl

/-- The two definitions of `Extensions.scaledPairing` agree. -/
theorem Extensions_scaledPairing_eq :
    @Critical2DKPZAudit.FourResults.Extensions.scaledPairing = @Critical2DKPZ.Extensions.scaledPairing := rfl

/-- The two definitions of `Extensions.IsWienerLaw` agree. -/
theorem Extensions_IsWienerLaw_eq :
    @Critical2DKPZAudit.FourResults.Extensions.IsWienerLaw = @Critical2DKPZ.Extensions.IsWienerLaw := rfl

/-- The two definitions of `Extensions.logCovariance` agree. -/
theorem Extensions_logCovariance_eq :
    @Critical2DKPZAudit.FourResults.Extensions.logCovariance = @Critical2DKPZ.Extensions.logCovariance := rfl

/-- The two definitions of `Extensions.IsFiniteGffLaw` agree. -/
theorem Extensions_IsFiniteGffLaw_eq :
    @Critical2DKPZAudit.FourResults.Extensions.IsFiniteGffLaw = @Critical2DKPZ.Extensions.IsFiniteGffLaw := rfl

end Critical2DKPZAudit.FourResults.Conversion

end
