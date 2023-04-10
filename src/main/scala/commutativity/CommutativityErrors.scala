package commutativity

import viper.silver.verifier.{AbstractVerificationError, ErrorMessage, ErrorReason}
import viper.silver.verifier.errors.ErrorNode

/*
 * Defines new custom error classes.
 */

case class CommutativityCheckFailed(a1: String, a2: String, offendingNode: ErrorNode, reason: ErrorReason,
                                    override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "commutativity.check.failed"
  val text: String = "Abstract commutativity check for actions " + a1 + " and "+ a2 + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    CommutativityCheckFailed(a1, a2, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = CommutativityCheckFailed(a1, a2, offendingNode, r)
}

case class ReorderingCheckFailed(a1: String, a2: String, offendingNode: ErrorNode, reason: ErrorReason,
                                 override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "reordering.check.failed"
  val text: String = "Reordering check for actions " + a1 + " and "+ a2 + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    ReorderingCheckFailed(a1, a2, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = ReorderingCheckFailed(a1, a2, offendingNode, r)
}

case class PreservationCheckFailed(a1: String, offendingNode: ErrorNode, reason: ErrorReason,
                                    override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "preservation.check.failed"
  val text: String = "Low abstraction preservation check for action " + a1 + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    PreservationCheckFailed(a1, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = PreservationCheckFailed(a1, offendingNode, r)
}

case class UniquenessCheckFailed(lt: String, offendingNode: ErrorNode, reason: ErrorReason,
                                   override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "uniqueness.check.failed"
  val text: String = "Invariant value uniqueness check for lock type " + lt + " failed."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    UniquenessCheckFailed(lt, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = UniquenessCheckFailed(lt, offendingNode, r)
}

case class HistoryNotReflexive(lt: String, offendingNode: ErrorNode, reason: ErrorReason,
                                 override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "history.not.reflexive"
  val text: String = "History invariant of lock type " + lt + " might not be reflexive."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    HistoryNotReflexive(lt, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = HistoryNotReflexive(lt, offendingNode, r)
}

case class HistoryNotTransitive(lt: String, offendingNode: ErrorNode, reason: ErrorReason,
                               override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "history.not.transitive"
  val text: String = "History invariant of lock type " + lt + " might not be transitive."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    HistoryNotTransitive(lt, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = HistoryNotTransitive(lt, offendingNode, r)
}

case class HistoryNotPreserved(lt: String, action: String, offendingNode: ErrorNode, reason: ErrorReason,
                                override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "history.not.preserved"
  val text: String = "History invariant of lock type " + lt + " might not be preserved by action " + action + "."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    HistoryNotPreserved(lt, action, offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = HistoryNotPreserved(lt, action, offendingNode, r)
}

case class ForkFailed(offendingNode: Fork, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "fork.failed"
  val text = "Fork might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = ForkFailed(offendingNode.asInstanceOf[Fork], this.reason)
  def withReason(r: ErrorReason) = ForkFailed(offendingNode, r)
}

case class JoinFailed(offendingNode: Join, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "join.failed"
  val text = "Join might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = JoinFailed(offendingNode.asInstanceOf[Join], this.reason)
  def withReason(r: ErrorReason) = JoinFailed(offendingNode, r)
}

case class AcquireFailed(offendingNode: Acquire, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "acquire.failed"
  val text = "Acquire might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = AcquireFailed(offendingNode.asInstanceOf[Acquire], this.reason)
  def withReason(r: ErrorReason) = AcquireFailed(offendingNode, r)
}

case class ReleaseFailed(offendingNode: Release, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "release.failed"
  val text = "Release might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = ReleaseFailed(offendingNode.asInstanceOf[Release], this.reason)
  def withReason(r: ErrorReason) = ReleaseFailed(offendingNode, r)
}

case class ShareFailed(offendingNode: Share, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "share.failed"
  val text = "Share might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = ShareFailed(offendingNode.asInstanceOf[Share], this.reason)
  def withReason(r: ErrorReason) = ShareFailed(offendingNode, r)
}

case class UnshareFailed(offendingNode: Unshare, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "unshare.failed"
  val text = "Unshare might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = UnshareFailed(offendingNode.asInstanceOf[Unshare], this.reason)
  def withReason(r: ErrorReason) = UnshareFailed(offendingNode, r)
}

case class WaitFailed(offendingNode: Wait, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "wait.failed"
  val text = "Wait might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = WaitFailed(offendingNode.asInstanceOf[Wait], this.reason)
  def withReason(r: ErrorReason) = WaitFailed(offendingNode, r)
}

case class NewBarrierFailed(offendingNode: NewBarrier, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "new.barrier.failed"
  val text = "Barrier creation might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = NewBarrierFailed(offendingNode.asInstanceOf[NewBarrier], this.reason)
  def withReason(r: ErrorReason) = NewBarrierFailed(offendingNode, r)
}

case class BarrierInvalidTotalInTrueAtZero(offendingNode: ErrorNode, reason: ErrorReason,
                                    override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "barrier.check.failed.totalin_true"
  val text: String = "Barrier validity check failed; totalInAfter assertion might not be true at i == 0."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    BarrierInvalidTotalInTrueAtZero(offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = BarrierInvalidTotalInTrueAtZero(offendingNode, r)
}

case class BarrierInvalidTotalInImpliesTotalOut(offendingNode: ErrorNode, reason: ErrorReason,
                                           override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "barrier.check.failed.totalin_implies_totalout"
  val text: String = "Barrier validity check failed; totalInAfter assertion might entail totalOutAfter assertion."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    BarrierInvalidTotalInImpliesTotalOut(offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = BarrierInvalidTotalInImpliesTotalOut(offendingNode, r)
}

case class BarrierInvalidInEstablishesTotalIn(offendingNode: ErrorNode, reason: ErrorReason,
                                           override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "barrier.check.failed.in_entails_totalin"
  val text: String = "Barrier validity check failed; sum of in assertions might not entail totalInAfter assertion."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    BarrierInvalidInEstablishesTotalIn(offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = BarrierInvalidInEstablishesTotalIn(offendingNode, r)
}

case class BarrierInvalidTotalOutEstablishesOut(offendingNode: ErrorNode, reason: ErrorReason,
                                              override val cached: Boolean = false) extends AbstractVerificationError {
  val id: String = "barrier.check.failed.totalout_entails_out"
  val text: String = "Barrier validity check failed; totalOut assertion might not entail sum of out assertions."
  override def withNode(offendingNode: ErrorNode = this.offendingNode): ErrorMessage =
    BarrierInvalidTotalOutEstablishesOut(offendingNode, this.reason)

  override def withReason(r: ErrorReason): AbstractVerificationError = BarrierInvalidTotalOutEstablishesOut(offendingNode, r)
}

