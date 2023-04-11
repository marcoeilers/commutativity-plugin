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

case class WithFailed(offendingNode: With, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "with.failed"
  val text = "With-statement might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = WithFailed(offendingNode.asInstanceOf[With], this.reason)
  def withReason(r: ErrorReason) = WithFailed(offendingNode, r)
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

case class SplitFailed(offendingNode: Split, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "split.failed"
  val text = "Split-statement might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = SplitFailed(offendingNode.asInstanceOf[Split], this.reason)
  def withReason(r: ErrorReason) = SplitFailed(offendingNode, r)
}

case class MergeFailed(offendingNode: Merge, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "merge.failed"
  val text = "Merge-statement might fail."

  def withNode(offendingNode: ErrorNode = this.offendingNode) = MergeFailed(offendingNode.asInstanceOf[Merge], this.reason)
  def withReason(r: ErrorReason) = MergeFailed(offendingNode, r)
}
