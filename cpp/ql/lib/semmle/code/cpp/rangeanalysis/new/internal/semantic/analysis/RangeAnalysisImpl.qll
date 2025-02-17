private import RangeAnalysisStage
private import RangeAnalysisConstantSpecific
private import RangeAnalysisRelativeSpecific
private import semmle.code.cpp.rangeanalysis.new.internal.semantic.analysis.FloatDelta
private import RangeUtils
private import semmle.code.cpp.rangeanalysis.new.internal.semantic.SemanticBound as SemanticBound
private import semmle.code.cpp.rangeanalysis.new.internal.semantic.SemanticLocation
private import semmle.code.cpp.rangeanalysis.new.internal.semantic.SemanticSSA

module ConstantBounds implements BoundSig<FloatDelta> {
  class SemBound instanceof SemanticBound::SemBound {
    SemBound() {
      this instanceof SemanticBound::SemZeroBound
      or
      this.(SemanticBound::SemSsaBound).getAVariable() instanceof SemSsaPhiNode
    }

    string toString() { result = super.toString() }

    SemLocation getLocation() { result = super.getLocation() }

    SemExpr getExpr(float delta) { result = super.getExpr(delta) }
  }

  class SemZeroBound extends SemBound instanceof SemanticBound::SemZeroBound { }

  class SemSsaBound extends SemBound instanceof SemanticBound::SemSsaBound {
    SemSsaVariable getAVariable() { result = this.(SemanticBound::SemSsaBound).getAVariable() }
  }
}

module RelativeBounds implements BoundSig<FloatDelta> {
  class SemBound instanceof SemanticBound::SemBound {
    SemBound() { not this instanceof SemanticBound::SemZeroBound }

    string toString() { result = super.toString() }

    SemLocation getLocation() { result = super.getLocation() }

    SemExpr getExpr(float delta) { result = super.getExpr(delta) }
  }

  class SemZeroBound extends SemBound instanceof SemanticBound::SemZeroBound { }

  class SemSsaBound extends SemBound instanceof SemanticBound::SemSsaBound {
    SemSsaVariable getAVariable() { result = this.(SemanticBound::SemSsaBound).getAVariable() }
  }
}

module ConstantStage =
  RangeStage<FloatDelta, ConstantBounds, FloatOverflow, CppLangImplConstant,
    RangeUtil<FloatDelta, CppLangImplConstant>>;

module RelativeStage =
  RangeStage<FloatDelta, RelativeBounds, FloatOverflow, CppLangImplRelative,
    RangeUtil<FloatDelta, CppLangImplRelative>>;

private newtype TSemReason =
  TSemNoReason() or
  TSemCondReason(SemGuard guard) {
    guard = any(ConstantStage::SemCondReason reason).getCond()
    or
    guard = any(RelativeStage::SemCondReason reason).getCond()
  } or
  TSemTypeReason()

private ConstantStage::SemReason constantReason(SemReason reason) {
  result instanceof ConstantStage::SemNoReason and reason instanceof SemNoReason
  or
  result.(ConstantStage::SemCondReason).getCond() = reason.(SemCondReason).getCond()
  or
  result instanceof ConstantStage::SemTypeReason and reason instanceof SemTypeReason
}

private RelativeStage::SemReason relativeReason(SemReason reason) {
  result instanceof RelativeStage::SemNoReason and reason instanceof SemNoReason
  or
  result.(RelativeStage::SemCondReason).getCond() = reason.(SemCondReason).getCond()
  or
  result instanceof RelativeStage::SemTypeReason and reason instanceof SemTypeReason
}

import Public

module Public {
  predicate semBounded(
    SemExpr e, SemanticBound::SemBound b, float delta, boolean upper, SemReason reason
  ) {
    ConstantStage::semBounded(e, b, delta, upper, constantReason(reason))
    or
    RelativeStage::semBounded(e, b, delta, upper, relativeReason(reason))
  }

  /**
   * A reason for an inferred bound. This can either be `CondReason` if the bound
   * is due to a specific condition, or `NoReason` if the bound is inferred
   * without going through a bounding condition.
   */
  abstract class SemReason extends TSemReason {
    /** Gets a textual representation of this reason. */
    abstract string toString();
  }

  /**
   * A reason for an inferred bound that indicates that the bound is inferred
   * without going through a bounding condition.
   */
  class SemNoReason extends SemReason, TSemNoReason {
    override string toString() { result = "NoReason" }
  }

  /** A reason for an inferred bound pointing to a condition. */
  class SemCondReason extends SemReason, TSemCondReason {
    /** Gets the condition that is the reason for the bound. */
    SemGuard getCond() { this = TSemCondReason(result) }

    override string toString() { result = this.getCond().toString() }
  }

  /**
   * A reason for an inferred bound that indicates that the bound is inferred
   * based on type-information.
   */
  class SemTypeReason extends SemReason, TSemTypeReason {
    override string toString() { result = "TypeReason" }
  }
}
